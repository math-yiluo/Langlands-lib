/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Exact left derived mixed tensor for a fixed complex

Source: Stacks Project, More on Algebra, Section 06Y5, Tag 06Y6.
(blueprint: lem-pc-mixed-tensor-pointwise-left-derived)
-/

@[expose] public section

set_option synthInstance.maxSize 512

universe u wR wA

open CategoryTheory CategoryTheory.Functor

namespace DerivedCategory

/-- Existence, exactness, and computation on K-flat complexes for one fixed A-complex.
Source: Stacks Project, Section 06Y5, Tag 06Y6.
(blueprint: lem-pc-mixed-tensor-pointwise-left-derived)

Proof: Mixed total tensor in the R-variable sends a chain homotopy h to the
termwise tensor homotopy h ⊗ 1. Thus it factors through K(R). Its signed
shift isomorphism identifies Tot(E[1] ⊗ N) with Tot(E ⊗ N)[1]. Reindex the
summands of the total of Cone(a) ⊗ N to identify it with Cone(Tot(a ⊗ 1));
the block differentials agree, so the homotopy functor is triangulated.
Every R-complex has a K-flat resolution by the functorial flat resolution
construction. The first clause of mixedTensor_kFlat_quasiIso inverts maps
between these models. Apply leftDerived_from_resolvingClass on K(R) to
obtain an exact left derived functor with counit invertible on K-flat objects.
Whisker its counit by the homotopy quotient. The quotient is full and
surjective on objects, so the right Kan universal property on K(R) is
also the right Kan universal property along the composite Q_R on complexes.
Transport through quotientCompQhIso to obtain the stated counit.
Exactness is unchanged by this transport, and its components on K-flat
complexes remain isomorphisms. -/
theorem exists_mixedTensor_pointwise_leftDerived
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (f : R →+* A) (N : CochainComplex (ModuleCat.{u} A) ℤ) :
    let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
    ∃ (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
      (ε : (Q : CochainComplex (ModuleCat R) ℤ ⥤ _) ⋙ L ⟶
        B.flip.obj N ⋙ (Q : CochainComplex (ModuleCat A) ℤ ⥤ _)),
      L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)) ∧
      (∃ c : L.CommShift ℤ, letI := c; L.IsTriangulated) ∧
      (∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
        (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F → IsIso (ε.app F)) :=
  by
    classical
    dsimp only
    let G := (ModuleCat.mixedTensor f).flip
    have : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive
    have : G.Additive := by
      change (ModuleCat.extendScalars f ⋙
        (MonoidalCategory.curriedTensor (ModuleCat A)).flip).Additive
      infer_instance
    have (X : ModuleCat.{u} R) : (G.obj X).Additive := by
      change (MonoidalCategory.tensorRight ((ModuleCat.extendScalars f).obj X)).Additive
      infer_instance
    let Gh := (G.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj
      ((HomotopyCategory.quotient _ _).obj N)
    let Fh := Gh ⋙ (Qh : HomotopyCategory (ModuleCat A) (.up ℤ) ⥤ _)
    let P : Set (HomotopyCategory (ModuleCat R) (.up ℤ)) :=
      (HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ)).kFlat
    have hres (X : HomotopyCategory (ModuleCat R) (.up ℤ)) :
        ∃ (X' : HomotopyCategory (ModuleCat R) (.up ℤ)) (s : X' ⟶ X),
          X' ∈ P ∧ HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ) s := by
      obtain ⟨E, rfl⟩ := X.quotient_obj_surjective
      let Λ := (Classical.choice (inferInstance :
        Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R))).reduced
      let K := Λ.resolutionFunctor.obj E
      let s := Λ.resolutionNatTrans.app E
      have hs : QuasiIso s := inferInstance
      have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le E
      refine ⟨(HomotopyCategory.quotient _ _).obj K,
        (HomotopyCategory.quotient _ _).map s, ?_, ?_⟩
      · exact (HomotopyCategory.kFlat_quotient_obj_iff K).2 hk
      · rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
          HomologicalComplex.mem_quasiIso_iff]
        exact hs
    have hinv (X Y : HomotopyCategory (ModuleCat R) (.up ℤ)) (s : X ⟶ Y)
        (hX : X ∈ P) (hY : Y ∈ P)
        (hs : HomotopyCategory.quasiIso (ModuleCat R) (.up ℤ) s) :
        IsIso (Fh.map s) := by
      obtain ⟨E, rfl⟩ := X.quotient_obj_surjective
      obtain ⟨E', rfl⟩ := Y.quotient_obj_surjective
      obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff] at hs
      have hk := (HomotopyCategory.kFlat_quotient_obj_iff E).1 hX
      have hk' := (HomotopyCategory.kFlat_quotient_obj_iff E').1 hY
      have ha := (CochainComplex.mixedTensor_kFlat_quasiIso f).1 N E E' a hs hk hk'
      change IsIso (Qh.map (Gh.map ((HomotopyCategory.quotient _ _).map a)))
      apply Localization.inverts (Qh : HomotopyCategory (ModuleCat A) (.up ℤ) ⥤ _)
        (HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ))
      change HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
        ((HomotopyCategory.quotient _ _).map
          (((ModuleCat.mixedTensor f).flip.map₂CochainComplex.map a).app N))
      rw [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff]
      exact ha
    obtain ⟨_, L, εh, _, htri, hcompute⟩ :=
      Functor.leftDerived_from_resolvingClass (ModuleCat R) (DerivedCategory (ModuleCat A))
        Fh P hres hinv
    let ι := HomotopyCategory.quotient (ModuleCat R) (.up ℤ)
    let B := G.map₂CochainComplex
    let ei : (Q : CochainComplex (ModuleCat R) ℤ ⥤ _) ⋙ L ≅ ι ⋙ Qh ⋙ L :=
      isoWhiskerRight (quotientCompQhIso (ModuleCat R)).symm L ≪≫
        Functor.associator _ _ _
    let eo : ι ⋙ Fh ≅ B.flip.obj N ⋙ (Q : CochainComplex (ModuleCat A) ℤ ⥤ _) :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (G.quotientCompBifunctorMapHomotopyFlipObjIso
          (.up ℤ) (.up ℤ) (.up ℤ) N) Qh ≪≫
        Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (quotientCompQhIso (ModuleCat A))
    let ε := ei.hom ≫ whiskerLeft ι εh ≫ eo.hom
    have hcompute' (K : CochainComplex (ModuleCat.{u} R) ℤ)
        (hK : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat K) :
        IsIso (ε.app K) := by
      have := hcompute (ι.obj K) ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
      dsimp only [ε, NatTrans.comp_app, whiskerLeft_app]
      infer_instance
    refine ⟨L, ε, ?_, htri, hcompute'⟩
    apply LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).localizerMorphismKFlat
    intro K
    exact hcompute' K.obj K.property

end DerivedCategory
