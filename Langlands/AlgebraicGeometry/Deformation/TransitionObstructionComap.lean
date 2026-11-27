import Langlands.AlgebraicGeometry.Deformation.TransitionObstructionCech
import Langlands.AlgebraicGeometry.Deformation.GroupTargetDifference

/-! # Obstruction cochains along maps of schemes and for quotients of observers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts ElementaryLiftCech
open AffineOpenQuotientSections

variable {R : Type u} [CommRing R] [IsLocalRing R]

section Points

variable {Z : Target R} {Y Y' : Over (Spec (CommRingCat.of R))}

lemma pt_eq_pt {U : Y.left.Opens} (hU : IsAffineOpen U) {g g' : U.toScheme ⟶ Z.X.left}
    (e : g = g') (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) (hg' : g' ≫ Z.X.hom = U.ι ≫ Y.hom) :
    pt hU g hg = pt hU g' hg' := by
  subst e
  rfl

/-- The point of a morphism restricted along a map of affine opens is the point of the
composite. -/
lemma sectionMap_pt (f : Y' ⟶ Y) {U : Y.left.Opens} {V : Y'.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (g : U.toScheme ⟶ Z.X.left)
    (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) :
    Z.restrict (sectionMap f h) (pt hU g hg) = pt hV (f.left.resLE U V h ≫ g) (by
      rw [Category.assoc, hg, Scheme.Hom.resLE_comp_ι_assoc, Over.w f]) := by
  apply Over.OverMorphism.ext
  rw [Target.restrict_left, pt_left, pt_left]
  have e : specMap (sectionMap f h).toRingHom ≫ hU.isoSpec.inv =
      hV.isoSpec.inv ≫ f.left.resLE U V h := by
    rw [← cancel_mono U.ι, Category.assoc, IsAffineOpen.isoSpec_inv_ι, sectionMap_fromSpec f h hU hV,
      Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  rw [reassoc_of% e]

end Points

section Comap

variable {Y Y' : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [IsSeparated Y'.hom]

namespace Family

variable (D : Family Y) (D' : Family Y') (f : Y' ⟶ Y) {l m n : D'.L} {a c e : D.L}
  (hl : D'.V l ≤ f.left ⁻¹ᵁ D.V a) (hm : D'.V m ≤ f.left ⁻¹ᵁ D.V c)
  (hn : D'.V n ≤ f.left ⁻¹ᵁ D.V e)

omit [IsSeparated Y.hom] [IsSeparated Y'.hom] in
include hl hm in
theorem le_preimage₂ : D'.V l ⊓ D'.V m ≤ f.left ⁻¹ᵁ (D.V a ⊓ D.V c) :=
  fun _ hx ↦ ⟨hl hx.1, hm hx.2⟩

omit [IsSeparated Y.hom] [IsSeparated Y'.hom] in
include hl hm hn in
theorem le_preimage₃ :
    D'.V l ⊓ D'.V m ⊓ D'.V n ≤ f.left ⁻¹ᵁ (D.V a ⊓ D.V c ⊓ D.V e) :=
  fun _ hx ↦ ⟨⟨hl hx.1.1, hm hx.1.2⟩, hn hx.2⟩

variable {D D' f}

omit [IsSeparated Y.hom] [IsSeparated Y'.hom] in
/-- Composites of transitions compatible with a map are compatible with it. -/
theorem comp_comap
    (hlm : D'.θ l m ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hl hm) ≫ D.θ a c)
    (hmn : D'.θ m n ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hm hn) ≫ D.θ c e) :
    D'.comp l m n ≫ f.left =
      f.left.resLE _ _ (le_preimage₃ D D' f hl hm hn) ≫ D.comp a c e := by
  have e₁ : D'.lift₃ l m n ≫ f.left.resLE _ _ (le_preimage₂ D D' f hl hm) =
      f.left.resLE _ _ (le_preimage₃ D D' f hl hm hn) ≫ D.lift₃ a c e := by
    rw [← cancel_mono (D.V a ⊓ D.V c).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, lift₃_ι_assoc,
      hmn, Category.assoc, lift₃_ι, ← Category.assoc, ← Category.assoc, Scheme.Hom.map_resLE,
      Scheme.Hom.resLE_map]
  rw [comp, comp, Category.assoc, hlm, ← Category.assoc, e₁, Category.assoc]

omit [IsSeparated Y.hom] [IsSeparated Y'.hom] in
/-- Direct transitions compatible with a map are compatible with it on triple overlaps. -/
theorem direct_comap
    (hln : D'.θ l n ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hl hn) ≫ D.θ a e) :
    D'.direct l m n ≫ f.left =
      f.left.resLE _ _ (le_preimage₃ D D' f hl hm hn) ≫ D.direct a c e := by
  rw [direct, direct, Category.assoc, hln, ← Category.assoc, ← Category.assoc,
    Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]

end Family

end Comap

section Obstruction

variable {Y Y' : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  [IsSeparated Y'.hom] [Smooth Y'.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R)) (F' : Reduction Y' (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

namespace Family

variable {D : Family Y} {D' : Family Y'} {f : Y' ⟶ Y} {l m n : D'.L} {a c e : D.L}
  {hl : D'.V l ≤ f.left ⁻¹ᵁ D.V a} {hm : D'.V m ≤ f.left ⁻¹ᵁ D.V c}
  {hn : D'.V n ≤ f.left ⁻¹ᵁ D.V e}

omit [IsSeparated Y.hom] [Smooth Y.hom] [IsSeparated Y'.hom] [Smooth Y'.hom] in
theorem preimage_le_comap (h₃ : D'.V l ⊓ D'.V m ⊓ D'.V n ≤ f.left ⁻¹ᵁ (D.V a ⊓ D.V c ⊓ D.V e)) :
    F'.toOriginal ⁻¹ᵁ (D'.V l ⊓ D'.V m ⊓ D'.V n) ≤
      (F'.map F f).left ⁻¹ᵁ (F.toOriginal ⁻¹ᵁ (D.V a ⊓ D.V c ⊓ D.V e)) := by
  rw [← Scheme.Hom.comp_preimage, Reduction.map_left_toOriginal, Scheme.Hom.comp_preimage]
  exact F'.toOriginal.preimage_mono h₃

/-- The obstruction of a family whose transitions are compatible, along a map, with those of
another family is the pullback of the obstruction of the other family. -/
theorem obstruction_comap (hD : D.Agrees I) (hD' : D'.Agrees I) (π : Y ⟶ Z.X) (π' : Y' ⟶ Z.X)
    (hπ : π' = f ≫ π)
    (hlm : D'.θ l m ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hl hm) ≫ D.θ a c)
    (hmn : D'.θ m n ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hm hn) ≫ D.θ c e)
    (hln : D'.θ l n ≫ f.left = f.left.resLE _ _ (le_preimage₂ D D' f hl hn) ≫ D.θ a e)
    (j : Index) :
    D'.obstruction b F' hD' π' l m n j =
      ((F'.map F f).left.appLE _ _
        (preimage_le_comap F F' (le_preimage₃ D D' f hl hm hn))).hom
        (D.obstruction b F hD π a c e j) := by
  subst hπ
  have h₃ := le_preimage₃ D D' f hl hm hn
  have hx : pt (D'.affine₃ l m n) (D'.comp l m n ≫ (f ≫ π).left) (D'.comp_π_over (f ≫ π) l m n) =
      Z.restrict (sectionMap f h₃) (pt (D.affine₃ a c e) (D.comp a c e ≫ π.left)
        (D.comp_π_over π a c e)) := by
    rw [sectionMap_pt]
    refine pt_eq_pt _ ?_ _ _
    rw [Over.comp_left, ← Category.assoc, comp_comap hl hm hn hlm hmn, Category.assoc]
  have hy : pt (D'.affine₃ l m n) (D'.direct l m n ≫ (f ≫ π).left)
      (D'.direct_π_over (f ≫ π) l m n) =
      Z.restrict (sectionMap f h₃) (pt (D.affine₃ a c e) (D.direct a c e ≫ π.left)
        (D.direct_π_over π a c e)) := by
    rw [sectionMap_pt]
    refine pt_eq_pt _ ?_ _ _
    rw [Over.comp_left, ← Category.assoc, direct_comap hl hm hn hln, Category.assoc]
  unfold obstruction
  rw [openDifference_congr b F' (D'.affine₃ l m n) hx hy _
    (Z.restrict_agree I _ _ _ (agree_pt_of _ _ ((hD a c e).comp π.left))) j]
  exact openDifference_sectionMap b F F' f h₃ (D.affine₃ a c e) (D'.affine₃ l m n) _ _ _ _ j

end Family

end Obstruction

section Quotients

variable {Y : Over (Spec (CommRingCat.of R))} (H : GroupScheme (Spec (CommRingCat.of R)))

/-- A morphism from an affine open into the source of two maps to a group scheme. -/
private def ptSource {U : Y.left.Opens} (hU : IsAffineOpen U) (g : U.toScheme ⟶ Y.left)
    (hg : g ≫ Y.hom = U.ι ≫ Y.hom) : Over.mk (str Y U) ⟶ Y :=
  Over.homMk (hU.isoSpec.inv ≫ g) (by
    change (hU.isoSpec.inv ≫ g) ≫ Y.hom = str Y U
    rw [Category.assoc, hg, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, fromSpec_hom hU])

private lemma pt_eq_comp {U : Y.left.Opens} (hU : IsAffineOpen U) (g : U.toScheme ⟶ Y.left)
    (hg : g ≫ Y.hom = U.ι ≫ Y.hom) (π : Y ⟶ H.X) (hπ : (g ≫ π.left) ≫ H.X.hom = U.ι ≫ Y.hom) :
    pt (Z := Target.ofGroup H) hU (g ≫ π.left) hπ = ptSource hU g hg ≫ π := by
  apply Over.OverMorphism.ext
  rw [pt_left, Over.comp_left]
  exact (Category.assoc _ _ _).symm

lemma pt_mul_inv {U : Y.left.Opens} (hU : IsAffineOpen U) (g : U.toScheme ⟶ Y.left)
    (hg : g ≫ Y.hom = U.ι ≫ Y.hom) (π₁ π₂ : Y ⟶ H.X)
    (h : (g ≫ (π₁ * π₂⁻¹).left) ≫ H.X.hom = U.ι ≫ Y.hom)
    (h₁ : (g ≫ π₁.left) ≫ H.X.hom = U.ι ≫ Y.hom) (h₂ : (g ≫ π₂.left) ≫ H.X.hom = U.ι ≫ Y.hom) :
    pt (Z := Target.ofGroup H) hU (g ≫ (π₁ * π₂⁻¹).left) h =
      pt (Z := Target.ofGroup H) hU (g ≫ π₁.left) h₁ *
        (pt (Z := Target.ofGroup H) hU (g ≫ π₂.left) h₂)⁻¹ := by
  rw [pt_eq_comp H hU g hg, pt_eq_comp H hU g hg, pt_eq_comp H hU g hg, MonObj.comp_mul,
    GrpObj.comp_inv]

variable [IsSeparated Y.hom] [Smooth Y.hom] [IsCommMonObj H.X] {I : Ideal R}
  [Fact (maximalIdeal R * I = ⊥)] (b : (Target.ofGroup H).Coordinates I)
  (F : Reduction Y (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

omit [IsSeparated Y.hom] in
lemma openDifference_div {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x x' y y' : (Target.ofGroup H).Points (Sections Y U)) (h : (Target.ofGroup H).Agree I x y)
    (h' : (Target.ofGroup H).Agree I x' y') (j : Index) :
    openDifference b F hU (x * x'⁻¹) (y * y'⁻¹)
        (Target.agree_mul H I h (Target.agree_inv H I h')) j =
      openDifference b F hU x y h j - openDifference b F hU x' y' h' j := by
  let : Module.Flat R (Sections Y U) := flat hU
  simp only [openDifference]
  rw [Target.difference_div H b x x' y y' h h', Pi.sub_apply, map_sub]

namespace Family

variable (D : Family Y) (hD : D.Agrees I)

/-- The obstruction for a quotient of two observers is the difference of their obstructions. -/
theorem obstruction_mul_inv (π₁ π₂ : Y ⟶ (Target.ofGroup H).X) (l m n : D.L) (j : Index) :
    D.obstruction b F hD (π₁ * π₂⁻¹) l m n j =
      D.obstruction b F hD π₁ l m n j - D.obstruction b F hD π₂ l m n j := by
  unfold obstruction
  rw [← openDifference_div H b F (D.affine₃ l m n)]
  exact openDifference_congr b F _
    (pt_mul_inv H _ _ (D.comp_over l m n) π₁ π₂ _ _ _)
    (pt_mul_inv H _ _ (D.direct_over l m n) π₁ π₂ _ _ _) _ _ j

end Family

end Quotients

end Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
