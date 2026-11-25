/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

/-! # Computing constant-ring derived tensors on flat representatives

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 06YT and 0G7E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.ConstantScalarRestriction

-- Compare the resolving predicate with the specified site tensor at independent universes.
private theorem flatRepresentative {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasDerivedCategory (Modules J A)]
    (K : DerivedCategory (Modules J A)) :
    ∃ P : (SheafOfModules.cochainTensorFlatRepresentatives J (ring J A)).FullSubcategory,
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) := by
  let R := ring J A
  obtain ⟨P, p, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (J := J) (R := R)
      (DerivedCategory.Q.objPreimage K)
  have hp : SheafOfModules.cochainTensorFlatRepresentatives J R P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X i)).symm (hf i)
  let := hq
  exact ⟨⟨P, hp⟩, ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- Both derived inputs have flat-term K-flat representatives computing their published
unbounded derived tensor.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 06YT and 0G7E.
(auxiliary; not a blueprint node).

Proof: choose cochain preimages under Q and apply the independent-coefficient K-flat
resolution theorem. Localize the quasi-isomorphisms and compose with the preimage
isomorphisms. The site tensor comparison identifies degreewise flatness with the
recorded site-flat predicate. Apply cochain tensor-model rigidity to the two flat
representatives. Compose its inverse with the inverse image of the two representative
isomorphisms under the published tensor. This gives the stated tensor comparison,
while retaining both individual localization isomorphisms. No functor or geometric
inverse image is involved, and neither derived input must be bounded or flat. -/
theorem constantRingTensorRepresentatives {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasDerivedCategory (Modules J A)]
    (K L : DerivedCategory (Modules J A)) :
    ∃ P N : (SheafOfModules.cochainTensorFlatRepresentatives J (ring J A)).FullSubcategory,
      Nonempty ((((SheafOfModules.KFlatFixedTensor.derivedTensor (ring J A)).obj K).obj L) ≅
        DerivedCategory.Q.obj
          ((SheafOfModules.cochainTensorTotal J (ring J A)).obj (P.obj, N.obj))) ∧
      Nonempty (DerivedCategory.Q.obj P.obj ≅ K) ∧
      Nonempty (DerivedCategory.Q.obj N.obj ≅ L) := by
  obtain ⟨P, ⟨p⟩⟩ := flatRepresentative J A K
  obtain ⟨N, ⟨n⟩⟩ := flatRepresentative J A L
  obtain ⟨r, _, _, _⟩ :=
    SheafOfModules.cochain_tensor_model_rigidity.{w, w, w, _, 0, 0} J (ring J A)
  let b := SheafOfModules.siteDerivedTensorIndependentCoefficients J (ring J A)
  let a : b.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj N.obj) ≅
      b.obj (K, L) := b.mapIso (CategoryTheory.Iso.prod p n)
  let t : DerivedCategory.Q.obj
      ((SheafOfModules.cochainTensorTotal J (ring J A)).obj (P.obj, N.obj)) ≅
      b.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj N.obj) := r.app (P, N)
  exact ⟨P, N, ⟨a.symm ≪≫ t.symm⟩, ⟨p⟩, ⟨n⟩⟩

end CategoryTheory.ConstantScalarRestriction
