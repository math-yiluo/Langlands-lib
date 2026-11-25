/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.BaseTensorUnitCohomologyModel

/-! # Fractions before transport to tensor cohomology models

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-localization-derived-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

private theorem ordinary_fractions (A Aq : Type u) [CommRing A] [CommRing Aq]
    [Algebra A Aq] (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (y : ((restrict A Aq).obj ((extend A Aq).obj C)).homology i) :
    ∃ (x : C.homology i) (s : S), (s : A) • y =
      (HomologicalComplex.homologyMap
        (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
          (.up ℤ)).unit.app C) i) x := by
  let f := algebraMap A Aq
  let E := ModuleCat.extendScalars f
  let G := ModuleCat.restrictScalars f
  let adj := ModuleCat.extendRestrictScalarsAdj f
  have : Module.Flat A Aq := IsLocalization.flat Aq S
  have : CategoryTheory.Limits.PreservesFiniteLimits E :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A Aq›)
  have : E.IsLeftAdjoint := adj.isLeftAdjoint
  have : CategoryTheory.Limits.PreservesFiniteColimits E := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits G := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteColimits G := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits (E ⋙ G) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits E G
  have : CategoryTheory.Limits.PreservesFiniteColimits (E ⋙ G) :=
    CategoryTheory.Limits.comp_preservesFiniteColimits E G
  have : (E ⋙ G).PreservesHomology := inferInstance
  let T := C.sc i
  let e := T.mapHomologyIso (𝟭 (ModuleCat.{u} A))
  let e' := T.mapHomologyIso (E ⋙ G)
  have hmap : HomologicalComplex.homologyMap
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) i =
      e.hom ≫ adj.unit.app T.homology ≫ e'.inv := by
    change ShortComplex.homologyMap (T.mapNatTrans adj.unit) = _
    exact T.homologyMap_mapNatTrans adj.unit
  let v : T.homology →ₗ[A] (G.obj (E.obj T.homology)) := (adj.unit.app _).hom
  have hloc : IsLocalization S Aq := inferInstance
  have halg : f.toAlgebra = ‹Algebra A Aq› := Algebra.algebra_ext _ _ fun _ ↦ rfl
  have : IsLocalizedModule S v := by
    let : Algebra A Aq := f.toAlgebra
    have : IsLocalization S Aq := by
      change @IsLocalization A _ S Aq _ f.toAlgebra
      rw [halg]
      exact hloc
    change IsLocalizedModule S (TensorProduct.mk A Aq T.homology 1)
    infer_instance
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S v (e'.hom y)
  refine ⟨e.inv x, s, ?_⟩
  apply (ModuleCat.mono_iff_injective e'.hom).1 inferInstance
  rw [e'.hom.hom.map_smul, hmap]
  change (s : A) • e'.hom y =
    (e.inv ≫ e.hom ≫ adj.unit.app T.homology ≫ e'.inv ≫ e'.hom) x
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact hs

private theorem model_fractions (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (y : K.cohomology i) :
    ∃ (x : L.cohomology i) (s : S),
      (Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
        Aq ⊗[R] B) • y = localizationModelMap R A Aq B D i Q L K uQ x := by
  obtain ⟨C, e, e', he⟩ :=
    exists_baseTensorUnitCohomologyModel R A Aq B D i Q L K uQ huQ
  obtain ⟨x, s, hs⟩ := ordinary_fractions A Aq S i C (e'.hom y)
  refine ⟨e.inv x, s, ?_⟩
  apply (ModuleCat.mono_iff_injective e'.hom).1 inferInstance
  rw [he, Iso.inv_hom_id_apply]
  exact (e'.hom.hom.map_smul (s : A) y).trans hs

/-- The derived scalar-extension functor sends the localization unit to a map whose
homology classes admit fractions. The denominator acts by the derived image of
multiplication on the localized input complex, before any tensor-coefficient
module structure or chosen cohomology model is introduced.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-localization-derived-fractions).

Proof in words: take a K-flat R-resolution F of B concentrated in degree zero.
The balanced derived tensor calculation computes the functor on an A-complex Q
by the total complex Q tensor_R F. It computes the localized input by the
localization of this same total complex: localization commutes with tensor
products and the direct sums defining totalization, and is exact. Each element
of the localized total complex is a fraction z/s. A cycle represented by z/s
has differential zero after localization, so a further denominator t kills dz.
Then tz is a cycle and its cohomology class, with denominator ts, gives the
required equation. The denominator endomorphism is multiplication by the image
of ts on the localized input. The balanced calculation is natural for the unit
and these scalar endomorphisms. The universal counit identifies any supplied
left derived scalar-extension functor with this calculation, so applying
homology and transporting the cycle equation proves the displayed assertion.
This argument only clears finitely many denominators of an individual element,
so no boundedness of Q is needed. When zero lies in S, the localized complex is
zero and the zero denominator works; for S = {1} the unit is an isomorphism. -/
theorem derivedLocalization_fractions
    (R A Aq B : Type u) [CommRing R] [CommRing A] [CommRing Aq] [CommRing B]
    [Algebra R A] [Algebra R Aq] [Algebra R B] [Algebra A Aq]
    [IsScalarTower R A Aq]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (S : Submonoid A) [IsLocalization S Aq]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε : DerivedCategory.Qh ⋙ F ⟶
      (ModuleCat.extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [F.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (i : ℤ) (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
      (F.obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj
          ((restrict R Aq).obj ((extend A Aq).obj Q)))))) :
    ∃ (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (F.obj (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ _).obj ((restrict R A).obj Q))))) (s : S),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (F.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
            ((restrict R Aq).map
              ((algebraMap A Aq (s : A)) • 𝟙 ((extend A Aq).obj Q)))))) y =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
          (F.map (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ _).map uQ))) x := by
  classical
  let D := Aq ⊗[R] B
  let φ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
    (AlgHom.id R B)).toRingHom
  let : Algebra (A ⊗[R] B) D := φ.toAlgebra
  obtain ⟨L⟩ := ModuleCat.nonempty_baseDerivedTensorCohomologyModel R A B Q D
  obtain ⟨K⟩ := ModuleCat.nonempty_baseDerivedTensorCohomologyModel R Aq B
    ((extend A Aq).obj Q) D
  let := L.universal
  let := K.universal
  let ζ := Functor.leftDerivedNatIso F L.derived ε L.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  let η := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  let V := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  let Z := (restrict R Aq).obj ((extend A Aq).obj Q)
  let e := H.mapIso (ζ.app (V.obj ((restrict R A).obj Q))) ≪≫ (L.cohomologyIso i).symm
  let e' := H.mapIso ((ζ ≪≫ η).app (V.obj Z)) ≪≫ (K.cohomologyIso i).symm
  obtain ⟨x, s, hs⟩ := model_fractions R A Aq B D S i Q L K uQ huQ (e'.hom y)
  refine ⟨e.inv x, s, ?_⟩
  let β := (restrict R Aq).map
    ((algebraMap A Aq (s : A)) • 𝟙 ((extend A Aq).obj Q))
  let σ := (ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom).map
    ((Algebra.TensorProduct.includeLeft (S := R) (algebraMap A Aq (s : A)) :
      Aq ⊗[R] B) • 𝟙 (K.cohomology i))
  have hact : H.map (F.map (V.map β)) ≫ e'.hom = e'.hom ≫ σ := by
    apply (cancel_mono (K.cohomologyIso i).hom).1
    dsimp only [e', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [K.cohomologyIso_smul]
    simp only [Iso.inv_hom_id_assoc]
    change H.map (F.map (V.map β)) ≫ H.map ((ζ ≪≫ η).hom.app _) =
      H.map ((ζ ≪≫ η).hom.app _) ≫ H.map (K.derived.map (V.map β))
    simpa only [H.map_comp] using
      congrArg H.map ((ζ ≪≫ η).hom.naturality (V.map β))
  have hunit : H.map (F.map (V.map uQ)) ≫ e'.hom =
      e.hom ≫ localizationModelMap R A Aq B D i Q L K uQ := by
    dsimp only [e, e', localizationModelMap, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
    have h := congrArg H.map (ζ.hom.naturality (V.map uQ))
    simpa only [Functor.map_comp, Category.assoc, H, V, Z, η,
      Functor.comp_obj, Functor.comp_map] using
      congrArg (fun f ↦ f ≫ H.map (η.hom.app (V.obj Z)) ≫ (K.cohomologyIso i).inv) h
  apply (ModuleCat.mono_iff_injective e'.hom).1 inferInstance
  change e'.hom (H.map (F.map (V.map β)) y) =
    e'.hom (H.map (F.map (V.map uQ)) (e.inv x))
  have hleft := congrArg (fun f ↦ f y) hact
  have hright := congrArg (fun f ↦ f (e.inv x)) hunit
  change e'.hom (H.map (F.map (V.map β)) y) = σ (e'.hom y) at hleft
  change e'.hom (H.map (F.map (V.map uQ)) (e.inv x)) =
    localizationModelMap R A Aq B D i Q L K uQ (e.hom (e.inv x)) at hright
  rw [Iso.inv_hom_id_apply] at hright
  exact hleft.trans (hs.trans hright.symm)

end RingTensorCohomology
