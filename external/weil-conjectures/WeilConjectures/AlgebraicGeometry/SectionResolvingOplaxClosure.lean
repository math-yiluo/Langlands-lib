/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import all WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import WeilConjectures.AlgebraicGeometry.SectionModuleAlgebraicInverseImage

/-! # Resolving closure for nested section tensors

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E;
the resolving-closure part of `lem-pd-section-resolving-oplax-model-edges`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
namespace ResolvingOplaxConstraints

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

private theorem resolving_tensor (T : Scheme.{u})
    (P Q : CochainComplex (modules Λ T) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ T P)
    (hQ : KFlatSectionComparison.sectionResolving Λ T Q) :
    KFlatSectionComparison.sectionResolving Λ T (P ⊗ Q) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (ring Λ T) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem resolving_iso (T : Scheme.{u})
    {P Q : CochainComplex (modules Λ T) ℤ} (e : P ≅ Q)
    (hP : KFlatSectionComparison.sectionResolving Λ T P) :
    KFlatSectionComparison.sectionResolving Λ T Q := by
  refine ⟨?_, ?_⟩
  · intro A hA n
    exact (hP.1 A hA n).of_iso
      (((curriedTensor (modules Λ T)).map₂CochainComplex.obj A).mapIso e)
  · intro n
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (P.X n) ≪≫
        (curriedTensor (modules Λ T)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso e) ≪≫
        (SheafOfModules.siteSheafTensorRightIso (ring Λ T) (Q.X n)).symm) (hP.2 n)

private theorem resolving_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (modules Λ Y) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ Y P) :
    KFlatSectionComparison.sectionResolving Λ X ((totalSectionPull Λ f).obj P) := by
  classical
  let L := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let V := Scheme.proEtaleSheafDirectImage f (Type (u + 1))
  let adj : L ⊣ V := Scheme.proEtaleSheafAdjunction f (Type (u + 1))
  have : PreservesFiniteLimits L := by
    have : PreservesFiniteLimits
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.lan :
          (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
      let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
        AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
      apply preservesFiniteLimits_op_lan_of_flat
    unfold L Scheme.proEtaleSheafInverseImage
      Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  let geom : GeometricMorphism
      (Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
      (Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) :=
    { inverse := L, direct := V, adj := adj, leftExact := inferInstance }
  obtain ⟨I, ⟨θ⟩⟩ := exists_sectionModuleAlgebraicInverseImage f
    (condensedRingObj Λ Y) (condensedRingObj Λ X) (inv (condensedPullbackHom Λ f))
  let c : CondensedRing.upperStar Λ f ≅
      Mod.mapModComap (inv (condensedPullbackHom Λ f)) :=
    Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  let e : I.modules ≅ pullback Λ f :=
    θ.symm ≪≫ Functor.isoWhiskerLeft (equivalence Λ Y).inverse
      (Functor.isoWhiskerRight c.symm (equivalence Λ X).functor ≪≫ pullComparison Λ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equivalence Λ Y).counitIso (pullback Λ f) ≪≫
    Functor.leftUnitor _
  have : (equivalence Λ Y).functor.Additive := sectionFunctorAdditive Λ Y
  have : (equivalence Λ X).functor.Additive := sectionFunctorAdditive Λ X
  have : I.modules.Additive := Functor.additive_of_iso θ
  have : (pullback Λ f).Additive := Functor.additive_of_iso e
  let I₀ := SheafOfModules.unliftInverseImage geom I
  have : I₀.modules.Additive := ‹I.modules.Additive›
  have hk := SheafOfModules.PullbackTensorResolving.isKFlat_inverseImage
    L V adj I₀ P hP.1 hP.2
  have hf (n : ℤ) := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u,
    u + 1, u, u + 1, u + 1}
    L V adj I (P.X n) (hP.2 n)
  exact resolving_iso Λ X ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ⟨hk, hf⟩

/--
The four nested tensor totals of resolving section complexes, together with all
their pullbacks, are resolving.  This is the closure step in the explicit
representative calculation: apply the K-flat total-tensor model theorem to the
two binary pairs and then to the two outer pairs, and apply preservation of
K-flatness and flat terms by ringed-topos pullback.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E.
(auxiliary; not a blueprint node).
-/
theorem section_resolving_oplax_closure {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q H : CochainComplex (modules Λ Y) ℤ)
    (hP : KFlatSectionComparison.sectionResolving Λ Y P)
    (hQ : KFlatSectionComparison.sectionResolving Λ Y Q)
    (hH : KFlatSectionComparison.sectionResolving Λ Y H) :
    ResolvingClosure Λ f P Q H := by
  have hPQ := resolving_tensor Λ Y P Q hP hQ
  have hQH := resolving_tensor Λ Y Q H hQ hH
  have hPQH := resolving_tensor Λ Y (P ⊗ Q) H hPQ hH
  have hPQH' := resolving_tensor Λ Y P (Q ⊗ H) hP hQH
  constructor
  · intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact hPQ
    · exact hQH
    · exact hPQH
    · exact hPQH'
  · intro A hA
    apply resolving_pullback Λ f A
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hP
    · exact hQ
    · exact hH
    · exact hPQ
    · exact hQH
    · exact hPQH
    · exact hPQH'

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
