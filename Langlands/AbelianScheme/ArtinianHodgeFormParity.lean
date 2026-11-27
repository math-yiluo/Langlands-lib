import Langlands.AbelianScheme.ArtinianHodgeSignedFunctions
import Langlands.AbelianScheme.HodgeFrameInversion

/-! # Inversion signs on relative form cochains -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Scheme
open Langlands.Algebra
open Langlands.AlgebraicGeometry.AffineCechDeRham
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

variable {R : Type u} [CommRing R] (B : AbelianScheme (Spec (CommRingCat.of R)))
  (U : Scheme.AffineOpenCover.{u} B.X.left)
  (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ ι[B.X].left ⁻¹ᵁ coverOpens U (β i))
  {κ : Type u} [Fintype κ]
  (E : SheafOfModules.free (R := B.X.left.ringCatSheaf) κ ≅ relativeDifferentials B.X.hom)

/-- Pullback of the one-form cochains by inversion and its chart assignment. -/
abbrev oneFormInversion (p : ℕ) := pullOneForms ι[B.X].left (Over.w ι[B.X]) β hβ p

/-- Pullback of the two-form cochains by inversion and its chart assignment. -/
abbrev twoFormInversion (p : ℕ) := pullTwoForms ι[B.X].left (Over.w ι[B.X]) β hβ p

/-- Inversion negates the frame vectors, so the coordinates of the pulled-back
one-form are the negatives of the pulled-back function coordinates. -/
lemma oneCochainCoordinates_inversion (p : ℕ) (b : Cochains U (oneForms B.X.hom) p) (i : κ) :
    oneCochainCoordinates B.X.hom U E p (oneFormInversion B U β hβ p b) i =
      -functionInversion B U β hβ p (oneCochainCoordinates B.X.hom U E p b i) := by
  funext σ
  let r := tupleAlgHomOver ι[B.X].left (Over.w ι[B.X]) β hβ σ
  let V := inter (coverOpens U) (β ∘ σ)
  let W := inter (coverOpens U) σ
  let bV := hodgeOneBasis B.X.hom E V (isAffineOpen_inter B.X.hom U (β ∘ σ))
  let bW := hodgeOneBasis B.X.hom E W (isAffineOpen_inter B.X.hom U σ)
  change bW.equivFun (RelativeForms.mapOne r (b (β ∘ σ))) i =
    -r (bV.equivFun (b (β ∘ σ)) i)
  have hb (j : κ) : (-(RelativeForms.mapOne r)) (bV j) = bW j := by
    rw [LinearMap.neg_apply, hodgeOneBasis_inversion B E, neg_neg]
  have h := basis_coordinates_map (-(RelativeForms.mapOne r)) bV bW hb (b (β ∘ σ)) i
  simp only [LinearMap.neg_apply, map_neg, Pi.neg_apply] at h
  exact neg_eq_iff_eq_neg.mp h

include E in
lemma oneFormInversion_involutive (hInv : Function.Involutive β) (p : ℕ) :
    Function.Involutive (oneFormInversion B U β hβ p) := by
  intro b
  apply (oneCochainCoordinates B.X.hom U E p).injective
  funext i
  rw [oneCochainCoordinates_inversion, oneCochainCoordinates_inversion, map_neg, neg_neg]
  exact functionInversion_involutive B U β hβ hInv p _

variable [LinearOrder κ]

/-- Inversion fixes the wedges of pairs of frame vectors. -/
lemma hodgeTwoBasis_inversion {V W : B.X.left.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : W ≤ ι[B.X].left ⁻¹ᵁ V) (i : Set.powersetCard κ 2) :
    RelativeForms.mapTwo (sectionAlgHomOver ι[B.X].left (Over.w ι[B.X]) h)
        (hodgeTwoBasis B.X.hom E V hV i) = hodgeTwoBasis B.X.hom E W hW i := by
  simp only [hodgeTwoBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    RelativeForms.mapTwo_ιMulti]
  let j' := Set.powersetCard.ofFinEmbEquiv.symm i
  let v : Fin 2 → Ω[(sectionRing B.X.hom W)⁄R] := fun j => hodgeOneBasis B.X.hom E W hW (j' j)
  have hv : (RelativeForms.mapOne (sectionAlgHomOver ι[B.X].left (Over.w ι[B.X]) h) ∘
      hodgeOneBasis B.X.hom E V hV ∘ j') = fun j => (-1 : sectionRing B.X.hom W) • v j := by
    funext j
    change RelativeForms.mapOne (sectionAlgHomOver ι[B.X].left (Over.w ι[B.X]) h)
      (hodgeOneBasis B.X.hom E V hV (j' j)) = (-1 : sectionRing B.X.hom W) • v j
    rw [hodgeOneBasis_inversion B E, neg_one_smul]
  change exteriorPower.ιMulti (sectionRing B.X.hom W) 2 _ =
    exteriorPower.ιMulti (sectionRing B.X.hom W) 2 v
  rw [hv, AlternatingMap.map_smul_univ]
  simp

include E in
/-- A compatible family of two-forms has constant coordinates in the wedge frame
and is therefore fixed by inversion. -/
lemma twoFormInversion_eq_of_cechD_zero (b : Cochains U (twoForms B.X.hom) 0)
    (hb : cechD U (twoForms B.X.hom) 0 b = 0) : twoFormInversion B U β hβ 0 b = b := by
  have hIso : IsIso B.X.hom.appTop := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    _ _ _ inferInstance inferInstance inferInstance ⊤
  funext σ
  apply (hodgeTwoBasis B.X.hom E _ (isAffineOpen_inter B.X.hom U σ)).equivFun.injective
  funext i
  have hz : cechD U (functions B.X.hom) 0 (twoCochainCoordinates B.X.hom U E 0 b i) = 0 := by
    rw [← twoCochainCoordinates_cechD, hb]
    funext τ
    exact congrFun (map_zero (hodgeTwoBasis B.X.hom E _ (isAffineOpen_inter B.X.hom U τ)).equivFun) i
  obtain ⟨r, hr, _⟩ := existsUnique_scalar_of_cechD_zero U B.X.hom _ hz
  change twoCochainCoordinates B.X.hom U E 0 (twoFormInversion B U β hβ 0 b) i σ =
    twoCochainCoordinates B.X.hom U E 0 b i σ
  let hV := isAffineOpen_inter B.X.hom U (β ∘ σ)
  let hW := isAffineOpen_inter B.X.hom U σ
  refine .trans (basis_coordinates_map (RelativeForms.mapTwo (tupleAlgHomOver ι[B.X].left
    (Over.w ι[B.X]) β hβ σ)) (hodgeTwoBasis B.X.hom E _ hV) (hodgeTwoBasis B.X.hom E _ hW)
    (hodgeTwoBasis_inversion B E hV hW _) (b (β ∘ σ)) i) ?_
  change tupleAlgHomOver ι[B.X].left (Over.w ι[B.X]) β hβ σ
    (twoCochainCoordinates B.X.hom U E 0 b i (β ∘ σ)) = _
  rw [hr (β ∘ σ), (tupleAlgHomOver ι[B.X].left (Over.w ι[B.X]) β hβ σ).commutes, hr σ]

variable [Algebra ℚ R]

include E in
/-- The derivative of an odd one-form cochain vanishes if it is Čech compatible.
Naturality makes it odd and compatibility makes it even. -/
lemma exteriorD1_eq_zero_of_odd_of_cechD_zero (b : Cochains U (oneForms B.X.hom) 0)
    (hb : oneFormInversion B U β hβ 0 b = -b)
    (hc : cechD U (twoForms B.X.hom) 0 (cochainMap U (exteriorD1 B.X.hom) 0 b) = 0) :
    cochainMap U (exteriorD1 B.X.hom) 0 b = 0 := by
  let d := cochainMap U (exteriorD1 B.X.hom) 0
  have h : twoFormInversion B U β hβ 0 (d b) = -(d b) := by
    rw [show twoFormInversion B U β hβ 0 (d b) = d (oneFormInversion B U β hβ 0 b) from
      pullTwoForms_exteriorD1 ι[B.X].left (Over.w ι[B.X]) β hβ 0 b, hb, map_neg]
  exact eq_zero_of_eq_neg_of_rat (R := R) ((twoFormInversion_eq_of_cechD_zero B U β hβ E _ hc).symm.trans h)

end Langlands.AbelianScheme
