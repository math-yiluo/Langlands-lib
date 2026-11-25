/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization

/-! # Resolving comparison for a flat degree-zero tensor factor -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.SignedLineDerivedBaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w})
  [HasDerivedCategory.{z} (KFlatFixedTensor.Modules A)]

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- A flat degree-zero factor has the published resolving tensor normalization.
Source: Stacks 06YQ and 06YU; the flat-single normalization theorem.
(blueprint: lem-pur-flat-line-resolving-normalization)
Proof: take the K-flatness and flat-term proofs and the resolving comparison chi
from flat_single_derived_normalization. Compose chi with the canonical collapse
from total tensor to the termwise site tensor. The collapse and its inverse cancel,
leaving the inverse representativeIso, exactly the required normalization. -/
theorem flat_line_resolving_normalization
    (L : KFlatFixedTensor.Modules A) (hL : IsFlatOnSite (J := J) (R := A) L) :
    ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L),
    ∃ hF : ∀ i : ℤ, IsFlatOnSite (J := J) (R := A)
      (((CochainComplex.singleFunctor (KFlatFixedTensor.Modules A) 0).obj L).X i),
    ∃ c : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      ResolvingNormalization A L hK hF c := by
  obtain ⟨hK, hF, hLim, hCol, hs, hi, hshift, hdiff, hp⟩ :=
    FlatSingleDerivedNormalization.flat_single_derived_normalization A L hL
  let := hLim
  let := hCol
  obtain ⟨shift, ht, chi, hchi, hn, eta, heta, hfac, hcoh⟩ := hp
  let c : DerivedCategory.Q ⋙ derivedLine.{u, v, w, z} A L ≅
      (siteSheafTensorRight L).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    chi ≪≫ Functor.isoWhiskerRight (collapse A L) DerivedCategory.Q
  refine ⟨hK, hF, c, ?_⟩
  intro E hE hf
  apply heq_of_eq
  dsimp only [c, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (congrArg Iso.hom (hn E hE hf))

end SheafOfModules.SignedLineDerivedBaseChange
