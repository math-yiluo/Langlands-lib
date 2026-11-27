import Langlands.AlgebraicGeometry.Deformation.TransitionObstructionCech

/-! # Changing lifted transition maps and correcting them by a Čech coboundary -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts ElementaryLiftCech
open AffineOpenQuotientSections Langlands.Cohomology
open Langlands.AlgebraicGeometry.TwistedOpenGluing

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝕜" => ResidueField R
local notation "K" => Spec (CommRingCat.of 𝕜)
local notation "r" => (specMap (IsLocalRing.residue R) : K ⟶ Spec (CommRingCat.of R))

section Replace

variable {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom]

namespace Family

variable (D : Family Y)

omit [IsSeparated Y.hom] in
theorem lift₃_over (l m n : D.L) :
    D.lift₃ l m n ≫ (D.V l ⊓ D.V m).ι ≫ Y.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
  rw [lift₃_ι_assoc, D.overBase, ← Category.assoc, Scheme.homOfLE_ι]

omit [IsSeparated Y.hom] in
theorem lift₃_fibre (l m n : D.L) :
    pullback.fst ((D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom) r ≫ D.lift₃ l m n =
      pullback.fst ((D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom) r ≫ Y.left.homOfLE inf_le_left := by
  rw [← cancel_mono (D.V l ⊓ D.V m).ι, Category.assoc, lift₃_ι, Category.assoc,
    Scheme.homOfLE_ι, fibre_homOfLE _ (D.fibre m n), Scheme.homOfLE_ι]

/-- The family with the same opens and other transition maps. -/
abbrev replace (θ' : ∀ l m, (D.V l ⊓ D.V m).toScheme ⟶ Y.left)
    (pointwise' : ∀ l m, IsPointwiseInclusion (θ' l m))
    (overBase' : ∀ l m, θ' l m ≫ Y.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom)
    (fibre' : ∀ l m, pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) r ≫ θ' l m =
      pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) r ≫ (D.V l ⊓ D.V m).ι) : Family Y where
  L := D.L
  V := D.V
  affine := D.affine
  θ := θ'
  pointwise := pointwise'
  overBase := overBase'
  fibre := fibre'

variable {I : Ideal R} (θ' : ∀ l m, (D.V l ⊓ D.V m).toScheme ⟶ Y.left)
  (pointwise' : ∀ l m, IsPointwiseInclusion (θ' l m))
  (overBase' : ∀ l m, θ' l m ≫ Y.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom)
  (fibre' : ∀ l m, pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) (specMap (IsLocalRing.residue R)) ≫
    θ' l m = pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) (specMap (IsLocalRing.residue R)) ≫
      (D.V l ⊓ D.V m).ι)
  (hθ : ∀ l m, AgreeMod I (D.affine₂ l m) (D.θ l m) (θ' l m))

include hθ in
theorem agree_lift₃_replace (l m n : D.L) :
    AgreeMod I (D.affine₃ l m n) ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n)
      (D.lift₃ l m n) := by
  apply AgreeMod.of_mono (D.V l ⊓ D.V m).ι
  refine ((AgreeMod.homOfLE_comp (inf₃_le_bc (D.V l) (D.V m) (D.V n)) (D.affine₃ l m n)
    (hθ m n)).symm).of_eq ?_ ?_
  · exact (lift₃_ι (D.replace θ' pointwise' overBase' fibre') l m n).symm
  · exact (lift₃_ι D l m n).symm

include hθ in
theorem agrees_replace (hD : D.Agrees I) :
    (D.replace θ' pointwise' overBase' fibre').Agrees I := by
  intro l m n
  have h₁ : AgreeMod I (D.affine₃ l m n)
      ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ θ' l m)
      ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ D.θ l m) :=
    (AgreeMod.ringOf_comp (D.affine₂ l m) (D.affine₃ l m n) _
      ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n) (hθ l m)).symm
  have h₂ := (D.agree_lift₃_replace θ' pointwise' overBase' fibre' hθ l m n).comp (D.θ l m)
  have h₃ := AgreeMod.homOfLE_comp (inf₃_le_ac (D.V l) (D.V m) (D.V n)) (D.affine₃ l m n)
    (hθ l n)
  exact h₁.trans (h₂.trans ((hD l m n).trans h₃))

end Family

end Replace

section Change

variable {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

omit [IsSeparated Y.hom] in
lemma openDifference_swap {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x y : Z.Points (Sections Y U)) (h : Z.Agree I x y) (j : Index) :
    openDifference b F hU x y h j = -openDifference b F hU y x h.symm j := by
  have e := openDifference_add b F hU x y x h h.symm j
  rw [show openDifference b F hU x x (h.trans h.symm) j = 0 from
    openDifference_same b F hU x j] at e
  exact eq_neg_of_add_eq_zero_left e.symm

namespace Family

variable (D : Family Y) (θ' : ∀ l m, (D.V l ⊓ D.V m).toScheme ⟶ Y.left)
  (pointwise' : ∀ l m, IsPointwiseInclusion (θ' l m))
  (overBase' : ∀ l m, θ' l m ≫ Y.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom)
  (fibre' : ∀ l m, pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) (specMap (IsLocalRing.residue R)) ≫
    θ' l m = pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) (specMap (IsLocalRing.residue R)) ≫
      (D.V l ⊓ D.V m).ι)
  (hθ : ∀ l m, AgreeMod I (D.affine₂ l m) (D.θ l m) (θ' l m)) (π : Y ⟶ Z.X)

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem θ_π_over (a c : D.L) :
    (D.θ a c ≫ π.left) ≫ Z.X.hom = (D.V a ⊓ D.V c).ι ≫ Y.hom := by
  rw [Category.assoc, Over.w π, D.overBase]

/-- The difference coordinates from the old to the new transition maps, observed through `π`. -/
def diff (a c : D.L) (j : Index) : Γ(F.obj.left, F.toOriginal ⁻¹ᵁ (D.V a ⊓ D.V c)) :=
  openDifference b F (D.affine₂ a c) (pt _ (D.θ a c ≫ π.left) (D.θ_π_over π a c))
    (pt _ (θ' a c ≫ π.left) ((D.replace θ' pointwise' overBase' fibre').θ_π_over π a c))
    (agree_pt_of _ _ ((hθ a c).comp π.left)) j

omit [IsSeparated Y.hom] [Smooth Y.hom] in
include overBase' in
theorem θ'_π_over (a c : D.L) :
    (θ' a c ≫ π.left) ≫ Z.X.hom = (D.V a ⊓ D.V c).ι ≫ Y.hom := by
  rw [Category.assoc, Over.w π, overBase' a c]

/-- Pre-composition step of the change of transitions. -/
theorem replace_pre (l m n : D.L) (j : Index)
    (h₁ : ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ θ' l m ≫ π.left) ≫
      Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom)
    (h₂ : ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ D.θ l m ≫ π.left) ≫
      Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom)
    (ha : Z.Agree I (pt (D.affine₃ l m n) _ h₁) (pt (D.affine₃ l m n) _ h₂)) :
    openDifference b F (D.affine₃ l m n) (pt _ _ h₁) (pt _ _ h₂) ha j =
      -(F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ≤ _))).op).hom
        (D.diff b F θ' pointwise' overBase' fibre' hθ π l m j) := by
  have e := openDifference_pt_ringOf b F inf_le_left (D.affine₂ l m) (D.affine₃ l m n)
    ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n)
    ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n)
    ((D.replace θ' pointwise' overBase' fibre').lift₃_fibre l m n)
    (D.θ'_π_over θ' overBase' π l m) (D.θ_π_over π l m)
    (agree_pt_of _ _ ((hθ l m).symm.comp π.left)) j
  refine e.trans ?_
  rw [openDifference_swap b F (D.affine₂ l m), map_neg]
  rfl

/-- Post-composition step of the change of transitions. -/
theorem replace_post (l m n : D.L) (j : Index)
    (h₁ : ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ D.θ l m ≫ π.left) ≫
      Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom)
    (h₂ : (D.lift₃ l m n ≫ D.θ l m ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom)
    (ha : Z.Agree I (pt (D.affine₃ l m n) _ h₁) (pt (D.affine₃ l m n) _ h₂)) :
    openDifference b F (D.affine₃ l m n) (pt _ _ h₁) (pt _ _ h₂) ha j =
      -(F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf₃_le_bc (D.V l) (D.V m) (D.V n)))).op).hom
        (D.diff b F θ' pointwise' overBase' fibre' hθ π m n j) := by
  have h3 := D.affine₃ l m n
  have hu := D.agree_lift₃_replace θ' pointwise' overBase' fibre' hθ l m n
  have hfib : pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) (specMap (IsLocalRing.residue R)) ≫
      D.θ l m ≫ π.left = pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom)
        (specMap (IsLocalRing.residue R)) ≫ (D.V l ⊓ D.V m).ι ≫ π.left := by
    rw [← Category.assoc, D.fibre l m, Category.assoc]
  have hG₂ : ((D.V l ⊓ D.V m).ι ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom := by
    rw [Category.assoc, Over.w π]
  have E := openDifference_pt_comp_eq b F (D.affine₃ l m n)
    ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n) (D.lift₃_over l m n) hu
    (D.θ l m ≫ π.left) ((D.V l ⊓ D.V m).ι ≫ π.left) (D.θ_π_over π l m) hG₂ hfib j
  have e₁ : (D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ (D.V l ⊓ D.V m).ι ≫
      π.left = Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ θ' m n ≫ π.left := by
    rw [← Category.assoc, lift₃_ι, Category.assoc]
  have e₂ : D.lift₃ l m n ≫ (D.V l ⊓ D.V m).ι ≫ π.left =
      Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ D.θ m n ≫ π.left := by
    rw [← Category.assoc, lift₃_ι, Category.assoc]
  have hr₁ : (Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ θ' m n ≫ π.left) ≫
      Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
    rw [Category.assoc, D.θ'_π_over θ' overBase' π m n, ← Category.assoc, Scheme.homOfLE_ι]
  have hr₂ : (Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ D.θ m n ≫ π.left) ≫
      Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
    rw [Category.assoc, D.θ_π_over π m n, ← Category.assoc, Scheme.homOfLE_ι]
  have hag : AgreeMod I h3 (Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ θ' m n ≫ π.left)
      (Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) ≫ D.θ m n ≫ π.left) :=
    AgreeMod.homOfLE_comp _ h3 ((hθ m n).symm.comp π.left)
  have R₁ := openDifference_pt_restrict b F (inf₃_le_bc (D.V l) (D.V m) (D.V n))
    (D.affine₂ m n) h3 (D.θ'_π_over θ' overBase' π m n) (D.θ_π_over π m n)
    (agree_pt_of _ _ ((hθ m n).symm.comp π.left)) j
  refine E.trans ((openDifference_pt_congr b F h3 e₁ e₂ _ _ hr₁ hr₂ _
    (agree_pt_of hr₁ hr₂ hag) j).trans (R₁.trans ?_))
  rw [openDifference_swap b F (D.affine₂ m n), map_neg]
  rfl

/-- Change of the obstruction under a change of transition maps by the difference cochain. -/
theorem obstruction_replace (hD : D.Agrees I) (l m n : D.L) (j : Index) :
    (D.replace θ' pointwise' overBase' fibre').obstruction b F
        (D.agrees_replace θ' pointwise' overBase' fibre' hθ hD) π l m n j =
      D.obstruction b F hD π l m n j -
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ≤ _))).op).hom
          (D.diff b F θ' pointwise' overBase' fibre' hθ π l m j) -
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf₃_le_bc (D.V l) (D.V m) (D.V n)))).op).hom
          (D.diff b F θ' pointwise' overBase' fibre' hθ π m n j) +
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
          (inf₃_le_ac (D.V l) (D.V m) (D.V n)))).op).hom
          (D.diff b F θ' pointwise' overBase' fibre' hθ π l n j) := by
  have h3 := D.affine₃ l m n
  have hhom (G : (D.V l ⊓ D.V n).toScheme ⟶ Z.X.left)
      (hG : G ≫ Z.X.hom = (D.V l ⊓ D.V n).ι ≫ Y.hom) :
      (Y.left.homOfLE (inf₃_le_ac (D.V l) (D.V m) (D.V n)) ≫ G) ≫ Z.X.hom =
        (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
    rw [Category.assoc, hG, ← Category.assoc, Scheme.homOfLE_ι]
  have hlift (q : (D.V l ⊓ D.V m ⊓ D.V n).toScheme ⟶ (D.V l ⊓ D.V m).toScheme)
      (hq : q ≫ (D.V l ⊓ D.V m).ι ≫ Y.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom)
      (G : (D.V l ⊓ D.V m).toScheme ⟶ Z.X.left)
      (hG : G ≫ Z.X.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom) :
      (q ≫ G) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
    rw [Category.assoc, hG, hq]
  have hQ1 := hlift _ ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n) _
    (D.θ'_π_over θ' overBase' π l m)
  have hQ2 := hlift _ ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n) _
    (D.θ_π_over π l m)
  have hQ3 := hlift _ (D.lift₃_over l m n) _ (D.θ_π_over π l m)
  have hQ4 := hhom _ (D.θ_π_over π l n)
  have hQ5 := hhom _ (D.θ'_π_over θ' overBase' π l n)
  have a12 : AgreeMod I h3
      ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ θ' l m ≫ π.left)
      ((D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ D.θ l m ≫ π.left) :=
    AgreeMod.ringOf_comp (D.affine₂ l m) h3 _
      ((D.replace θ' pointwise' overBase' fibre').lift₃_over l m n) ((hθ l m).symm.comp π.left)
  have a23 := (D.agree_lift₃_replace θ' pointwise' overBase' fibre' hθ l m n).comp
    (D.θ l m ≫ π.left)
  have a34 : AgreeMod I h3 (D.lift₃ l m n ≫ D.θ l m ≫ π.left)
      (Y.left.homOfLE (inf₃_le_ac (D.V l) (D.V m) (D.V n)) ≫ D.θ l n ≫ π.left) :=
    ((hD l m n).comp π.left).of_eq (by rw [comp, Category.assoc])
      (by rw [direct, Category.assoc])
  have a45 := AgreeMod.homOfLE_comp (inf₃_le_ac (D.V l) (D.V m) (D.V n)) h3
    ((hθ l n).comp π.left)
  have S1 := D.replace_pre b F θ' pointwise' overBase' fibre' hθ π l m n j hQ1 hQ2
    (agree_pt_of hQ1 hQ2 a12)
  have S2 := D.replace_post b F θ' pointwise' overBase' fibre' hθ π l m n j hQ2 hQ3
    (agree_pt_of hQ2 hQ3 a23)
  have S3 := openDifference_pt_congr b F h3 (by rw [comp, Category.assoc] :
      D.comp l m n ≫ π.left = D.lift₃ l m n ≫ D.θ l m ≫ π.left)
    (by rw [direct, Category.assoc] : D.direct l m n ≫ π.left =
      Y.left.homOfLE (inf₃_le_ac (D.V l) (D.V m) (D.V n)) ≫ D.θ l n ≫ π.left)
    (D.comp_π_over π l m n) (D.direct_π_over π l m n) hQ3 hQ4
    (agree_pt_of _ _ ((hD l m n).comp π.left)) (agree_pt_of hQ3 hQ4 a34) j
  have S4 := openDifference_pt_restrict b F (inf₃_le_ac (D.V l) (D.V m) (D.V n))
    (D.affine₂ l n) h3 (D.θ_π_over π l n) (D.θ'_π_over θ' overBase' π l n)
    (agree_pt_of _ _ ((hθ l n).comp π.left)) j
  have L := openDifference_pt_congr b F h3
    (by rw [comp, Category.assoc] : (D.replace θ' pointwise' overBase' fibre').comp l m n ≫
      π.left = (D.replace θ' pointwise' overBase' fibre').lift₃ l m n ≫ θ' l m ≫ π.left)
    (by rw [direct, Category.assoc] : (D.replace θ' pointwise' overBase' fibre').direct l m n ≫
      π.left = Y.left.homOfLE (inf₃_le_ac (D.V l) (D.V m) (D.V n)) ≫ θ' l n ≫ π.left)
    ((D.replace θ' pointwise' overBase' fibre').comp_π_over π l m n)
    ((D.replace θ' pointwise' overBase' fibre').direct_π_over π l m n) hQ1 hQ5
    (agree_pt_of _ _ (((D.agrees_replace θ' pointwise' overBase' fibre' hθ hD) l m n).comp
      π.left))
    (agree_pt_of hQ1 hQ5 (a12.trans (a23.trans (a34.trans a45)))) j
  have add₁ := openDifference_add b F h3 _ _ _ (agree_pt_of hQ1 hQ2 a12)
    (agree_pt_of hQ2 hQ5 (a23.trans (a34.trans a45))) j
  have add₂ := openDifference_add b F h3 _ _ _ (agree_pt_of hQ2 hQ3 a23)
    (agree_pt_of hQ3 hQ5 (a34.trans a45)) j
  have add₃ := openDifference_add b F h3 _ _ _ (agree_pt_of hQ3 hQ4 a34)
    (agree_pt_of hQ4 hQ5 a45) j
  have key := L.trans (add₁.trans (congrArg₂ (· + ·) S1 (add₂.trans (congrArg₂ (· + ·) S2
    (add₃.trans (congrArg₂ (· + ·) S3.symm S4))))))
  unfold Family.obstruction at key ⊢
  rw [key]
  abel

end Family

end Change

section Correction

variable {Z : Target R} [IsSeparated Z.X.hom] [Smooth Z.X.hom] {I : Ideal R}
  [Fact (maximalIdeal R * I = ⊥)] (hI : I ≤ maximalIdeal R) (b : Z.Coordinates I)
  (F : Reduction Z.X (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

namespace Family

variable (D : Family Z.X)
  (c : ∀ l m, Fin b.cotangentRank × Fin b.idealRank → Γ(F.obj.left, F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m)))

/-- The point of a transition map on the coordinate ring of an overlap. -/
abbrev tpt (l m : D.L) : Z.Points (Sections Z.X (D.V l ⊓ D.V m)) :=
  pt (D.affine₂ l m) (D.θ l m ≫ (𝟙 Z.X : Z.X ⟶ Z.X).left) (D.θ_π_over (𝟙 Z.X) l m)

/-- The transition maps corrected by prescribed difference coordinates. -/
def corrected (l m : D.L) : (D.V l ⊓ D.V m).toScheme ⟶ Z.X.left :=
  (D.affine₂ l m).isoSpec.hom ≫ (correctOpen b F (D.affine₂ l m) (D.tpt l m) (c l m)).left

theorem isoSpec_inv_corrected (l m : D.L) :
    (D.affine₂ l m).isoSpec.inv ≫ D.corrected b F c l m =
      (correctOpen b F (D.affine₂ l m) (D.tpt l m) (c l m)).left := by
  rw [corrected, Iso.inv_hom_id_assoc]

theorem corrected_overBase (l m : D.L) :
    D.corrected b F c l m ≫ Z.X.hom = (D.V l ⊓ D.V m).ι ≫ Z.X.hom := by
  rw [corrected, Category.assoc, Over.w (correctOpen b F (D.affine₂ l m) (D.tpt l m) (c l m))]
  change (D.affine₂ l m).isoSpec.hom ≫ str Z.X (D.V l ⊓ D.V m) = _
  rw [← fromSpec_hom (D.affine₂ l m), ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem agree_corrected (l m : D.L) :
    AgreeMod I (D.affine₂ l m) (D.θ l m) (D.corrected b F c l m) := by
  have h := correctOpen_agree b F (D.affine₂ l m) (D.tpt l m) (c l m)
  unfold AgreeMod
  rw [isoSpec_inv_corrected]
  change _ ≫ (D.affine₂ l m).isoSpec.inv ≫ D.θ l m ≫ 𝟙 _ = _ at h
  rw [Category.comp_id] at h
  exact h

include hI in
theorem corrected_pointwise (l m : D.L) : IsPointwiseInclusion (D.corrected b F c l m) :=
  fun x ↦ (apply_eq_of_agreeMod _ (D.agree_corrected b F c l m)
    (extended_squareZero I _ hI) x).symm.trans (D.pointwise l m x)

include hI in
theorem corrected_fibre (l m : D.L) :
    pullback.fst ((D.V l ⊓ D.V m).ι ≫ Z.X.hom) (specMap (IsLocalRing.residue R)) ≫
        D.corrected b F c l m =
      pullback.fst ((D.V l ⊓ D.V m).ι ≫ Z.X.hom) (specMap (IsLocalRing.residue R)) ≫
        (D.V l ⊓ D.V m).ι :=
  (fibre_of_agreeMod hI _ (D.agree_corrected b F c l m)).symm.trans (D.fibre l m)

/-- The family with corrected transition maps. -/
abbrev correctedFamily : Family Z.X :=
  D.replace (D.corrected b F c) (D.corrected_pointwise hI b F c) (D.corrected_overBase b F c)
    (D.corrected_fibre hI b F c)

theorem diff_corrected (l m : D.L) (j : Index) :
    D.diff b F (D.corrected b F c) (D.corrected_pointwise hI b F c) (D.corrected_overBase b F c)
      (D.corrected_fibre hI b F c) (D.agree_corrected b F c) (𝟙 Z.X) l m j = c l m j := by
  have e : pt (D.affine₂ l m) (D.corrected b F c l m ≫ (𝟙 Z.X : Z.X ⟶ Z.X).left)
      ((D.correctedFamily hI b F c).θ_π_over (𝟙 Z.X) l m) =
      correctOpen b F (D.affine₂ l m) (D.tpt l m) (c l m) := by
    apply Over.OverMorphism.ext
    rw [pt_left]
    change (D.affine₂ l m).isoSpec.inv ≫ D.corrected b F c l m ≫ 𝟙 _ = _
    rw [Category.comp_id, isoSpec_inv_corrected]
  unfold diff
  rw [openDifference_congr b F (D.affine₂ l m) rfl e _
    (correctOpen_agree b F (D.affine₂ l m) (D.tpt l m) (c l m)) j]
  exact openDifference_correctOpen b F (D.affine₂ l m) (D.tpt l m) (c l m) j

end Family

end Correction

end Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
