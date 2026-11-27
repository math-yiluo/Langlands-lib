import Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech

/-! # Pullback of elementary lifting obstructions along a morphism with a lift -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts
open AffineOpenQuotientSections
open Picard.FieldTwoAxisH1Injectivity (map_map_apply)

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {I : Ideal R} {Z : Target R}
variable {Y Y' : Over (Spec (CommRingCat.of R))}

/-- A preimage in the residue fibre can be taken in either order around the base-change square. -/
lemma preimage_fibre_map (F : Reduction Y (maximalIdeal R)) (F' : Reduction Y' (maximalIdeal R))
    (f : Y' ⟶ Y) (U : Y.left.Opens) :
    F'.toOriginal ⁻¹ᵁ (f.left ⁻¹ᵁ U) = (F'.map F f).left ⁻¹ᵁ (F.toOriginal ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, F'.map_left_toOriginal]

private lemma sectionMap_restrict_point (f : Y' ⟶ Y) {U V : Y.left.Opens} {W : Y'.left.Opens}
    (h : V ≤ U) (k : W ≤ f.left ⁻¹ᵁ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (x : Z.Points (Sections Y U)) :
    Z.restrict (sectionMap f k) (Z.restrict (restrict Y h) x) =
      Z.restrict (sectionMap f (k.trans (f.left.preimage_mono h))) x := by
  apply Over.OverMorphism.ext
  simp only [Target.restrict_left]
  have hcomp : specMap (sectionMap f k).toRingHom ≫ specMap (restrict Y h).toRingHom =
      specMap (sectionMap f (k.trans (f.left.preimage_mono h))).toRingHom := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, restrict_fromSpec Y h hU hV, sectionMap_fromSpec f k hV hW,
      sectionMap_fromSpec f _ hU hW]
  rw [← Category.assoc, hcomp]

private lemma restrict_sectionMap_point (f : Y' ⟶ Y) {U : Y.left.Opens} {V W : Y'.left.Opens}
    (h : W ≤ V) (k : V ≤ f.left ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (x : Z.Points (Sections Y U)) :
    Z.restrict (restrict Y' h) (Z.restrict (sectionMap f k) x) =
      Z.restrict (sectionMap f (h.trans k)) x := by
  apply Over.OverMorphism.ext
  simp only [Target.restrict_left]
  have hcomp : specMap (restrict Y' h).toRingHom ≫ specMap (sectionMap f k).toRingHom =
      specMap (sectionMap f (h.trans k)).toRingHom := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, sectionMap_fromSpec f k hU hV, restrict_fromSpec_assoc Y' h hV hW,
      sectionMap_fromSpec f _ hU hW]
  rw [← Category.assoc, hcomp]

section

variable [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] [IsSeparated Y.hom] [Smooth Y'.hom]
  (B : Reduction Y I) (B' : Reduction Y' I) (F : Reduction Y (maximalIdeal R))
  (F' : Reduction Y' (maximalIdeal R)) (b : Z.Coordinates I)
  {g₀ : B.obj.left ⟶ Z.X.left} (f : Y' ⟶ Y)
  {ι : Type*} (U : ι → Y.left.Opens) (hU : ∀ a, IsAffineOpen (U a))
  (x : ∀ a, Z.Points (Sections Y (U a))) (hx : ∀ a, IsLocalLift (g₀ := g₀) B (hU a) (x a))
  (hV : ∀ a, IsAffineOpen (f.left ⁻¹ᵁ U a))
  (hW : ∀ a c, IsAffineOpen (f.left ⁻¹ᵁ (U a ⊓ U c)))
  (g : Y' ⟶ Z.X) (hg : B'.toOriginal ≫ g.left = (B'.map B f).left ≫ g₀)

set_option quotPrecheck false in
local notation "preU" => (fun a ↦ f.left ⁻¹ᵁ U a)
set_option quotPrecheck false in
local notation "fibreArrow" => (F'.map F f).left
set_option quotPrecheck false in
local notation "L" => (fun a ↦ F.toOriginal ⁻¹ᵁ U a)
local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

include hx hg in
omit [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] [IsSeparated Y.hom] [Smooth Y'.hom] in
private lemma pulled_agree (a : ι) :
    Z.Agree I (localPoint g (hV a))
      (Z.restrict (sectionMap f (U := U a) (V := preU a) le_rfl) (x a)) :=
  (localPoint_isLift B' hg (hV a)).trans
    (sectionMap_isLocalLift B B' f le_rfl (hU a) (hV a) (x a) (hx a)).symm

/-- The primitive on the pullback cover is the difference from the actual lift to the local lift. -/
def pullbackPrimitive (a : ι) (j : Index) : Γ(F'.obj.left, F'.toOriginal ⁻¹ᵁ preU a) :=
  openDifference b F' (hV a) (localPoint g (hV a))
    (Z.restrict (sectionMap f (U := U a) (V := preU a) le_rfl) (x a))
    (pulled_agree B B' f U hU x hx hV g hg a) j

include hg hV hW in
/-- On the reduction of a morphism along which an actual lift is given, the local
lifting cocycle is a Čech coboundary. -/
theorem cocycle_pullback_coboundary (j : Index) :
    ∃ p : ∀ a, Γ(F'.obj.left, fibreArrow ⁻¹ᵁ L a), ∀ a c,
      ((fibreArrow).app (F.toOriginal ⁻¹ᵁ (U a ⊓ U c))).hom (cocycle B b F U hU x hx a c j) =
        (F'.obj.left.presheaf.map (homOfLE ((fibreArrow).preimage_mono
          (F.toOriginal.preimage_mono (show U a ⊓ U c ≤ U c from inf_le_right)))).op).hom (p c) -
        (F'.obj.left.presheaf.map (homOfLE ((fibreArrow).preimage_mono
          (F.toOriginal.preimage_mono (show U a ⊓ U c ≤ U a from inf_le_left)))).op).hom (p a) := by
  let y (a : ι) := Z.restrict (sectionMap f (U := U a) (V := preU a) le_rfl) (x a)
  have hy (a : ι) : IsLocalLift (g₀ := (B'.map B f).left ≫ g₀) B' (hV a) (y a) :=
    sectionMap_isLocalLift B B' f le_rfl (hU a) (hV a) (x a) (hx a)
  let d (a : ι) := pullbackPrimitive B B' F' b f U hU x hx hV g hg a j
  refine ⟨fun a ↦ (F'.obj.left.presheaf.map
    (homOfLE (preimage_fibre_map F F' f (U a)).ge).op).hom (d a), ?_⟩
  intro a c
  let O := U a ⊓ U c
  let W := f.left ⁻¹ᵁ O
  let T := F'.toOriginal ⁻¹ᵁ W
  let T' := fibreArrow ⁻¹ᵁ (F.toOriginal ⁻¹ᵁ O)
  have eT : T = T' := preimage_fibre_map F F' f O
  have l : O ≤ U a := inf_le_left
  have r : O ≤ U c := inf_le_right
  have l' : W ≤ preU a := f.left.preimage_mono l
  have r' : W ≤ preU c := f.left.preimage_mono r
  let xa := Z.restrict (restrict Y l) (x a)
  let xc := Z.restrict (restrict Y r) (x c)
  have ex : Z.Agree I xa xc :=
    (restrict_isLocalLift B l (hU a) (affine_inf (hU a) (hU c)) _ (hx a)).trans
      (restrict_isLocalLift B r (hU c) (affine_inf (hU a) (hU c)) _ (hx c)).symm
  let ya := Z.restrict (restrict Y' l') (y a)
  let yc := Z.restrict (restrict Y' r') (y c)
  have ea : Z.Agree I (localPoint g (hW a c)) ya :=
    (localPoint_isLift B' hg (hW a c)).trans
      (restrict_isLocalLift B' l' (hV a) (hW a c) _ (hy a)).symm
  have ec : Z.Agree I (localPoint g (hW a c)) yc :=
    (localPoint_isLift B' hg (hW a c)).trans
      (restrict_isLocalLift B' r' (hV c) (hW a c) _ (hy c)).symm
  have eac : Z.Agree I ya yc := ea.symm.trans ec
  have hl : Z.restrict (sectionMap f (U := O) (V := W) le_rfl) xa = ya :=
    (sectionMap_restrict_point f l le_rfl (hU a) (affine_inf (hU a) (hU c)) (hW a c) (x a)).trans
      (restrict_sectionMap_point f l' le_rfl (hU a) (hV a) (hW a c) (x a)).symm
  have hr : Z.restrict (sectionMap f (U := O) (V := W) le_rfl) xc = yc :=
    (sectionMap_restrict_point f r le_rfl (hU c) (affine_inf (hU a) (hU c)) (hW a c) (x c)).trans
      (restrict_sectionMap_point f r' le_rfl (hU c) (hV c) (hW a c) (x c)).symm
  have he : ((fibreArrow).appLE _ T eT.le).hom (cocycle B b F U hU x hx a c j) =
      openDifference b F' (hW a c) ya yc eac j := by
    change ((fibreArrow).appLE _ T eT.le).hom
      (openDifference b F (affine_inf (hU a) (hU c)) xa xc ex j) = _
    rw [← openDifference_sectionMap b F F' f le_rfl (affine_inf (hU a) (hU c)) (hW a c) eT.le]
    exact openDifference_congr b F' _ hl hr _ _ j
  have ela : (F'.obj.left.presheaf.map (homOfLE (F'.toOriginal.preimage_mono l')).op).hom (d a) =
      openDifference b F' (hW a c) (localPoint g (hW a c)) ya ea j := by
    dsimp only [d, pullbackPrimitive]
    rw [← openDifference_restrict b F' l' (hV a) (hW a c)]
    exact openDifference_congr b F' _ (restrict_localPoint g l' (hV a) (hW a c)) rfl _ _ j
  have elc : (F'.obj.left.presheaf.map (homOfLE (F'.toOriginal.preimage_mono r')).op).hom (d c) =
      openDifference b F' (hW a c) (localPoint g (hW a c)) yc ec j := by
    dsimp only [d, pullbackPrimitive]
    rw [← openDifference_restrict b F' r' (hV c) (hW a c)]
    exact openDifference_congr b F' _ (restrict_localPoint g r' (hV c) (hW a c)) rfl _ _ j
  have h := openDifference_add b F' (hW a c) (localPoint g (hW a c)) ya yc ea eac j
  rw [← elc, ← ela, ← he] at h
  have hh := congrArg (F'.obj.left.presheaf.map (homOfLE eT.ge).op).hom (eq_sub_of_add_eq' h.symm)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, map_sub] at hh
  dsimp only [T'] at hh
  rw [Scheme.Hom.appLE_eq_app] at hh
  rw [map_map_apply, map_map_apply] at hh
  rw [map_map_apply, map_map_apply]
  exact hh

end

end Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech
