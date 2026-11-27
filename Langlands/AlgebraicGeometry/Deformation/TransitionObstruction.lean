import Langlands.AlgebraicGeometry.Deformation.GroupTargetDifference
import Langlands.AlgebraicGeometry.TwistedOpenGluing

/-! # The obstruction cocycle of lifted transition maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

open SquareZeroAffinePairs SplitInfinitesimalCoordinates ElementaryIdealCoefficients
open ElementaryMorphismLifts ElementaryLiftCech AffineOpenQuotientSections
open scoped SquareZeroAffinePairs ElementaryIdealCoefficients
open Langlands.AlgebraicGeometry.TwistedOpenGluing

variable {R : Type u} [CommRing R] [IsLocalRing R]

local notation "𝕜" => ResidueField R
local notation "S" => Spec (CommRingCat.of R)
local notation "K" => Spec (CommRingCat.of 𝕜)
local notation "r" => (specMap (IsLocalRing.residue R) : K ⟶ S)

section Points

variable {Z : Target R} {Y : Over (Spec (CommRingCat.of R))}

/-- A morphism from an affine open to the target, as a point on the coordinate ring. -/
def pt {U : Y.left.Opens} (hU : IsAffineOpen U) (g : U.toScheme ⟶ Z.X.left)
    (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) : Z.Points (Sections Y U) :=
  Over.homMk (hU.isoSpec.inv ≫ g) (by
    change (hU.isoSpec.inv ≫ g) ≫ Z.X.hom = str Y U
    rw [Category.assoc, hg, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, fromSpec_hom hU])

@[simp] lemma pt_left {U : Y.left.Opens} (hU : IsAffineOpen U) (g : U.toScheme ⟶ Z.X.left)
    (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) : (pt hU g hg).left = hU.isoSpec.inv ≫ g := rfl

lemma pt_congr {U : Y.left.Opens} (hU : IsAffineOpen U) {g g' : U.toScheme ⟶ Z.X.left}
    (e : g = g') (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) :
    pt hU g hg = pt hU g' (e ▸ hg) := by
  subst e
  rfl

lemma eq_of_pt_eq {U : Y.left.Opens} (hU : IsAffineOpen U) {g g' : U.toScheme ⟶ Z.X.left}
    (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) (hg' : g' ≫ Z.X.hom = U.ι ≫ Y.hom)
    (e : pt hU g hg = pt hU g' hg') : g = g' :=
  (cancel_epi hU.isoSpec.inv).mp (congrArg (fun x : Z.Points (Sections Y U) ↦ x.left) e)

omit [IsLocalRing R] in
@[reassoc] lemma isoSpec_restrict {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    hV.isoSpec.inv ≫ Y.left.homOfLE h ≫ hU.isoSpec.hom = specMap (restrict Y h).toRingHom := by
  apply (cancel_mono hU.fromSpec).mp
  simp only [Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι, restrict_fromSpec Y h hU hV]

lemma restrict_pt {U V : Y.left.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (g : U.toScheme ⟶ Z.X.left) (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) :
    Z.restrict (restrict Y h) (pt hU g hg) = pt hV (Y.left.homOfLE h ≫ g) (by
      rw [Category.assoc, hg, ← Category.assoc, Scheme.homOfLE_ι]) := by
  apply Over.OverMorphism.ext
  rw [Target.restrict_left, pt_left, pt_left, ← isoSpec_restrict h hU hV]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The coordinate-ring map of a morphism between affine opens over the base. -/
def ringOf {U V : Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom) :
    Sections Y U →ₐ[R] Sections Y V :=
  { (Spec.preimage (hV.isoSpec.inv ≫ q ≫ hU.isoSpec.hom)).hom with
    commutes' := fun a ↦ by
      have e : specMap ((Spec.preimage (hV.isoSpec.inv ≫ q ≫ hU.isoSpec.hom)).hom.comp
          (algebraMap R (Sections Y U))) = specMap (algebraMap R (Sections Y V)) := by
        rw [specMap_comp]
        change Spec.map (Spec.preimage (hV.isoSpec.inv ≫ q ≫ hU.isoSpec.hom)) ≫ str Y U =
          str Y V
        rw [Spec.map_preimage, ← fromSpec_hom hU, ← fromSpec_hom hV]
        simp only [Category.assoc]
        rw [← Category.assoc hU.isoSpec.hom, IsAffineOpen.isoSpec_hom_fromSpec, hq,
          ← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
      have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
      exact RingHom.congr_fun e' a }

omit [IsLocalRing R] in
lemma specMap_ringOf {U V : Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom) :
    specMap (ringOf hU hV q hq).toRingHom = hV.isoSpec.inv ≫ q ≫ hU.isoSpec.hom :=
  Spec.map_preimage _

lemma restrict_ringOf_pt {U V : Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom)
    (g : U.toScheme ⟶ Z.X.left) (hg : g ≫ Z.X.hom = U.ι ≫ Y.hom) :
    Z.restrict (ringOf hU hV q hq) (pt hU g hg) = pt hV (q ≫ g) (by
      rw [Category.assoc, hg, hq]) := by
  apply Over.OverMorphism.ext
  rw [Target.restrict_left, pt_left, pt_left, specMap_ringOf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- A morphism between affine opens agreeing with the inclusion on the actual residue fibre
induces the restriction map on residue coordinate rings. -/
lemma fibreMap_ringOf {U V : Y.left.Opens} (h : V ≤ U) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom)
    (hfib : pullback.fst (V.ι ≫ Y.hom) r ≫ q = pullback.fst (V.ι ≫ Y.hom) r ≫ Y.left.homOfLE h) :
    fibreMap (ringOf hU hV q hq) = fibreMap (restrict Y h) := by
  have hring : (reduce (R := R) (Sections Y V)).comp (ringOf hU hV q hq).toRingHom =
      (reduce (R := R) (Sections Y V)).comp (restrict Y h).toRingHom := by
    have e : specMap ((reduce (R := R) (Sections Y V)).comp (ringOf hU hV q hq).toRingHom) =
        specMap ((reduce (R := R) (Sections Y V)).comp (restrict Y h).toRingHom) := by
      rw [specMap_comp, specMap_comp, specMap_ringOf, ← isoSpec_restrict h hU hV]
      have hv : (specMap (reduce (R := R) (Sections Y V)) ≫ hV.isoSpec.inv) ≫ V.ι ≫ Y.hom =
          (test (k := 𝕜) (Fibre (R := R) (Sections Y V))).hom ≫ r := by
        rw [Category.assoc, ← Category.assoc hV.isoSpec.inv, IsAffineOpen.isoSpec_inv_ι,
          fromSpec_hom hV]
        exact Target.reduce_comp_base (C := Sections Y V)
      have := Target.comp_eq_of_fibre (W := Over.mk (V.ι ≫ Y.hom)) q (Y.left.homOfLE h) hfib _ _ hv
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
    have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    exact e'
  apply AlgHom.ext
  intro x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  change reduce (R := R) (Sections Y V) (ringOf hU hV q hq c) =
    reduce (R := R) (Sections Y V) (restrict Y h c)
  exact RingHom.congr_fun hring c

end Points

section Differences

variable {Z : Target R} {Y : Over (Spec (CommRingCat.of R))} {I : Ideal R}
  [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

/-- Difference coordinates of points given by equal morphisms are equal. -/
lemma openDifference_pt_congr {U : Y.left.Opens} (hU : IsAffineOpen U)
    {g₁ g₁' g₂ g₂' : U.toScheme ⟶ Z.X.left} (e₁ : g₁ = g₁') (e₂ : g₂ = g₂')
    (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom) (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₁' : g₁' ≫ Z.X.hom = U.ι ≫ Y.hom) (hg₂' : g₂' ≫ Z.X.hom = U.ι ≫ Y.hom)
    (h : Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂)) (h' : Z.Agree I (pt hU g₁' hg₁') (pt hU g₂' hg₂'))
    (j : Index) :
    openDifference b F hU (pt hU g₁ hg₁) (pt hU g₂ hg₂) h j =
      openDifference b F hU (pt hU g₁' hg₁') (pt hU g₂' hg₂') h' j := by
  subst e₁ e₂
  rfl

omit [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] in
lemma agree_pt_ringOf {U V : Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom)
    {g₁ g₂ : U.toScheme ⟶ Z.X.left} (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom) (h : Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂)) :
    Z.Agree I (pt hV (q ≫ g₁) (by rw [Category.assoc, hg₁, hq]))
      (pt hV (q ≫ g₂) (by rw [Category.assoc, hg₂, hq])) := by
  rw [← restrict_ringOf_pt hU hV q hq g₁ hg₁, ← restrict_ringOf_pt hU hV q hq g₂ hg₂]
  exact Z.restrict_agree I _ _ _ h

omit [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] in
lemma agree_pt_restrict {U V : Y.left.Opens} (hVU : V ≤ U) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) {g₁ g₂ : U.toScheme ⟶ Z.X.left} (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom) (h : Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂)) :
    Z.Agree I (pt hV (Y.left.homOfLE hVU ≫ g₁) (by
        rw [Category.assoc, hg₁, ← Category.assoc, Scheme.homOfLE_ι]))
      (pt hV (Y.left.homOfLE hVU ≫ g₂) (by
        rw [Category.assoc, hg₂, ← Category.assoc, Scheme.homOfLE_ι])) := by
  rw [← restrict_pt hVU hU hV g₁ hg₁, ← restrict_pt hVU hU hV g₂ hg₂]
  exact Z.restrict_agree I _ _ _ h

/-- Restriction of difference functions along an inclusion of affine opens. -/
lemma openDifference_pt_restrict {U V : Y.left.Opens} (hVU : V ≤ U) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) {g₁ g₂ : U.toScheme ⟶ Z.X.left} (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom) (h : Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂))
    (j : Index) :
    openDifference b F hV _ _ (agree_pt_restrict hVU hU hV hg₁ hg₂ h) j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono hVU)).op).hom
        (openDifference b F hU _ _ h j) := by
  rw [← openDifference_restrict b F hVU hU hV _ _ h j]
  exact openDifference_congr b F hV (restrict_pt hVU hU hV g₁ hg₁).symm
    (restrict_pt hVU hU hV g₂ hg₂).symm _ _ j

/-- Pre-composition with a morphism of affine opens agreeing with the inclusion on the actual
residue fibre restricts difference functions. -/
lemma openDifference_pt_ringOf {U V : Y.left.Opens} (hVU : V ≤ U) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom)
    (hfib : pullback.fst (V.ι ≫ Y.hom) r ≫ q = pullback.fst (V.ι ≫ Y.hom) r ≫ Y.left.homOfLE hVU)
    {g₁ g₂ : U.toScheme ⟶ Z.X.left} (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom) (h : Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂))
    (j : Index) :
    openDifference b F hV _ _ (agree_pt_ringOf hU hV q hq hg₁ hg₂ h) j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono hVU)).op).hom
        (openDifference b F hU _ _ h j) := by
  rw [← openDifference_restrict b F hVU hU hV _ _ h j]
  have e : openDifference b F hV (Z.restrict (ringOf hU hV q hq) (pt hU g₁ hg₁))
      (Z.restrict (ringOf hU hV q hq) (pt hU g₂ hg₂)) (Z.restrict_agree I _ _ _ h) j =
      openDifference b F hV (Z.restrict (restrict Y hVU) (pt hU g₁ hg₁))
        (Z.restrict (restrict Y hVU) (pt hU g₂ hg₂)) (Z.restrict_agree I _ _ _ h) j := by
    let : Module.Flat R (Sections Y U) := flat hU
    let : Module.Flat R (Sections Y V) := flat hV
    simp only [openDifference]
    rw [b.difference_restrict (ringOf hU hV q hq) _ _ h j,
      b.difference_restrict (restrict Y hVU) _ _ h j, fibreMap_ringOf hVU hU hV q hq hfib]
  refine Eq.trans ?_ e
  exact openDifference_congr b F hV (restrict_ringOf_pt hU hV q hq g₁ hg₁).symm
    (restrict_ringOf_pt hU hV q hq g₂ hg₂).symm _ _ j

omit [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] in
lemma agree_pt_comp {U V : Y.left.Opens} (hU : IsAffineOpen U) {u₁ u₂ : U.toScheme ⟶ V.toScheme}
    (hu₁ : u₁ ≫ V.ι ≫ Y.hom = U.ι ≫ Y.hom) (hu₂ : u₂ ≫ V.ι ≫ Y.hom = U.ι ≫ Y.hom)
    (hu : specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₁ =
      specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₂)
    (G : V.toScheme ⟶ Z.X.left) (hG : G ≫ Z.X.hom = V.ι ≫ Y.hom) :
    Z.Agree I (pt hU (u₁ ≫ G) (by rw [Category.assoc, hG, hu₁]))
      (pt hU (u₂ ≫ G) (by rw [Category.assoc, hG, hu₂])) := by
  change specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₁ ≫ G =
    specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₂ ≫ G
  have e := congrArg (· ≫ G) hu
  simpa only [Category.assoc] using e

/-- Post-composition with two maps agreeing on the actual residue fibre of an open gives the
same difference functions. -/
lemma openDifference_pt_comp_eq {U V : Y.left.Opens} (hU : IsAffineOpen U)
    {u₁ u₂ : U.toScheme ⟶ V.toScheme}
    (hu₁ : u₁ ≫ V.ι ≫ Y.hom = U.ι ≫ Y.hom) (hu₂ : u₂ ≫ V.ι ≫ Y.hom = U.ι ≫ Y.hom)
    (hu : specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₁ =
      specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ u₂)
    (G₁ G₂ : V.toScheme ⟶ Z.X.left) (hG₁ : G₁ ≫ Z.X.hom = V.ι ≫ Y.hom)
    (hG₂ : G₂ ≫ Z.X.hom = V.ι ≫ Y.hom)
    (hfib : pullback.fst (V.ι ≫ Y.hom) r ≫ G₁ = pullback.fst (V.ι ≫ Y.hom) r ≫ G₂)
    (j : Index) :
    openDifference b F hU _ _ (agree_pt_comp hU hu₁ hu₂ hu G₁ hG₁) j =
      openDifference b F hU _ _ (agree_pt_comp hU hu₁ hu₂ hu G₂ hG₂) j := by
  let W : Over (Spec (CommRingCat.of R)) := Over.mk (V.ι ≫ Y.hom)
  let x₁ : Over.mk (str Y U) ⟶ W := Over.homMk (hU.isoSpec.inv ≫ u₁) (by
    change (hU.isoSpec.inv ≫ u₁) ≫ V.ι ≫ Y.hom = str Y U
    rw [Category.assoc, hu₁, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, fromSpec_hom hU])
  let x₂ : Over.mk (str Y U) ⟶ W := Over.homMk (hU.isoSpec.inv ≫ u₂) (by
    change (hU.isoSpec.inv ≫ u₂) ≫ V.ι ≫ Y.hom = str Y U
    rw [Category.assoc, hu₂, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι, fromSpec_hom hU])
  let F₁ : W ⟶ Z.X := Over.homMk G₁ hG₁
  let F₂ : W ⟶ Z.X := Over.homMk G₂ hG₂
  have hx : specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ x₁.left =
      specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ x₂.left := hu
  have key : openDifference b F hU (x₁ ≫ F₁) (x₂ ≫ F₁) (Z.agree_comp I x₁ x₂ hx F₁) j =
      openDifference b F hU (x₁ ≫ F₂) (x₂ ≫ F₂) (Z.agree_comp I x₁ x₂ hx F₂) j := by
    let : Module.Flat R (Sections Y U) := flat hU
    have hd : b.difference (x₁ ≫ F₁) (x₂ ≫ F₁) (Z.agree_comp I x₁ x₂ hx F₁) =
        b.difference (x₁ ≫ F₂) (x₂ ≫ F₂) (Z.agree_comp I x₁ x₂ hx F₂) := by
      unfold Target.Coordinates.difference
      rw [Z.translatedDifference_comp_eq I b.ideal_le b.chart F₁ F₂ hfib x₁ x₂ hx]
    simp only [openDifference]
    rw [hd]
  have e (u : U.toScheme ⟶ V.toScheme) (hu' : u ≫ V.ι ≫ Y.hom = U.ι ≫ Y.hom)
      (x : Over.mk (str Y U) ⟶ W) (hx : x.left = hU.isoSpec.inv ≫ u)
      (G : V.toScheme ⟶ Z.X.left) (hG : G ≫ Z.X.hom = V.ι ≫ Y.hom) :
      x ≫ Over.homMk G hG = pt hU (u ≫ G) (by rw [Category.assoc, hG, hu']) := by
    apply Over.OverMorphism.ext
    change x.left ≫ G = _
    rw [hx, pt_left, Category.assoc]
  refine Eq.trans ?_ (key.trans ?_)
  · exact openDifference_congr b F hU (e u₁ hu₁ x₁ rfl G₁ hG₁).symm (e u₂ hu₂ x₂ rfl G₁ hG₁).symm _ _ j
  · exact openDifference_congr b F hU (e u₁ hu₁ x₁ rfl G₂ hG₂) (e u₂ hu₂ x₂ rfl G₂ hG₂) _ _ j

end Differences

section Agreement

variable {Y : Over (Spec (CommRingCat.of R))} (I : Ideal R)

/-- Two maps from an affine open agree after reduction modulo the extended ideal. -/
def AgreeMod {U : Y.left.Opens} (hU : IsAffineOpen U) {T : Scheme.{u}} (a b : U.toScheme ⟶ T) :
    Prop :=
  specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ a =
    specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.isoSpec.inv ≫ b

variable {I}

omit [IsLocalRing R] in
lemma AgreeMod.trans {U : Y.left.Opens} {hU : IsAffineOpen U} {T : Scheme.{u}}
    {a b c : U.toScheme ⟶ T} (h : AgreeMod I hU a b) (h' : AgreeMod I hU b c) :
    AgreeMod I hU a c := Eq.trans h h'

omit [IsLocalRing R] in
lemma AgreeMod.symm {U : Y.left.Opens} {hU : IsAffineOpen U} {T : Scheme.{u}}
    {a b : U.toScheme ⟶ T} (h : AgreeMod I hU a b) : AgreeMod I hU b a := Eq.symm h

omit [IsLocalRing R] in
lemma AgreeMod.of_eq {U : Y.left.Opens} {hU : IsAffineOpen U} {T : Scheme.{u}}
    {a b a' b' : U.toScheme ⟶ T} (h : AgreeMod I hU a b) (ha : a = a') (hb : b = b') :
    AgreeMod I hU a' b' := by
  subst ha hb
  exact h

omit [IsLocalRing R] in
lemma AgreeMod.comp {U : Y.left.Opens} {hU : IsAffineOpen U} {T T' : Scheme.{u}}
    {a b : U.toScheme ⟶ T} (h : AgreeMod I hU a b) (c : T ⟶ T') :
    AgreeMod I hU (a ≫ c) (b ≫ c) := by
  unfold AgreeMod at h ⊢
  have e := congrArg (· ≫ c) h
  simpa only [Category.assoc] using e

omit [IsLocalRing R] in
lemma AgreeMod.of_mono {U : Y.left.Opens} {hU : IsAffineOpen U} {T T' : Scheme.{u}}
    {a b : U.toScheme ⟶ T} (c : T ⟶ T') [Mono c] (h : AgreeMod I hU (a ≫ c) (b ≫ c)) :
    AgreeMod I hU a b := by
  unfold AgreeMod at h ⊢
  apply (cancel_mono c).mp
  simpa only [Category.assoc] using h

omit [IsLocalRing R] in
lemma AgreeMod.homOfLE_comp {U V : Y.left.Opens} (hVU : V ≤ U) {hU : IsAffineOpen U}
    (hV : IsAffineOpen V) {T : Scheme.{u}} {a b : U.toScheme ⟶ T} (h : AgreeMod I hU a b) :
    AgreeMod I hV (Y.left.homOfLE hVU ≫ a) (Y.left.homOfLE hVU ≫ b) := by
  have e := map_reduced_agree (Extended I (Sections Y U)) (Extended I (Sections Y V))
    (restrict Y hVU).toRingHom (map_extended_le I (restrict Y hVU)) (hU.isoSpec.inv ≫ a)
    (hU.isoSpec.inv ≫ b) h
  have hs : specMap (restrict Y hVU).toRingHom ≫ hU.isoSpec.inv =
      hV.isoSpec.inv ≫ Y.left.homOfLE hVU := by
    rw [← isoSpec_restrict hVU hU hV, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  unfold AgreeMod
  rw [← Category.assoc hV.isoSpec.inv, ← hs, ← Category.assoc hV.isoSpec.inv, ← hs]
  simpa only [Category.assoc] using e

omit [IsLocalRing R] in
lemma AgreeMod.ringOf_comp {U V : Y.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : V.toScheme ⟶ U.toScheme) (hq : q ≫ U.ι ≫ Y.hom = V.ι ≫ Y.hom) {T : Scheme.{u}}
    {a b : U.toScheme ⟶ T} (h : AgreeMod I hU a b) : AgreeMod I hV (q ≫ a) (q ≫ b) := by
  have e := map_reduced_agree (Extended I (Sections Y U)) (Extended I (Sections Y V))
    (ringOf hU hV q hq).toRingHom (map_extended_le I (ringOf hU hV q hq)) (hU.isoSpec.inv ≫ a)
    (hU.isoSpec.inv ≫ b) h
  rw [specMap_ringOf] at e
  unfold AgreeMod
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using e

lemma agree_pt_of {Z : Target R} {U : Y.left.Opens} {hU : IsAffineOpen U}
    {g₁ g₂ : U.toScheme ⟶ Z.X.left} (hg₁ : g₁ ≫ Z.X.hom = U.ι ≫ Y.hom)
    (hg₂ : g₂ ≫ Z.X.hom = U.ι ≫ Y.hom) (h : AgreeMod I hU g₁ g₂) :
    Z.Agree I (pt hU g₁ hg₁) (pt hU g₂ hg₂) := h

/-- Agreement on the actual residue fibre restricts to smaller opens. -/
lemma fibre_homOfLE {U W : Y.left.Opens} (h : W ≤ U) {T : Scheme.{u}} {G₁ G₂ : U.toScheme ⟶ T}
    (hfib : pullback.fst (U.ι ≫ Y.hom) r ≫ G₁ = pullback.fst (U.ι ≫ Y.hom) r ≫ G₂) :
    pullback.fst (W.ι ≫ Y.hom) r ≫ Y.left.homOfLE h ≫ G₁ =
      pullback.fst (W.ι ≫ Y.hom) r ≫ Y.left.homOfLE h ≫ G₂ := by
  have e : pullback.fst (W.ι ≫ Y.hom) r ≫ Y.left.homOfLE h =
      pullback.lift (pullback.fst (W.ι ≫ Y.hom) r ≫ Y.left.homOfLE h) (pullback.snd _ r) (by
        rw [Category.assoc, ← Category.assoc (Y.left.homOfLE h), Scheme.homOfLE_ι,
          pullback.condition]) ≫ pullback.fst (U.ι ≫ Y.hom) r :=
    (pullback.lift_fst _ _ _).symm
  rw [← Category.assoc, e, Category.assoc, hfib, ← Category.assoc, ← e, Category.assoc]

omit [IsLocalRing R] in
/-- Maps agreeing on the reduction of an affine open agree on its base change to the quotient
of the base. -/
lemma pullback_eq_of_agreeMod {L : Ideal R} {U : Y.left.Opens} (hU : IsAffineOpen U)
    {T : Scheme.{u}} {a b : U.toScheme ⟶ T} (h : AgreeMod L hU a b) :
    pullback.fst (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) ≫ a =
      pullback.fst (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) ≫ b := by
  let : Algebra.IsPushout R (Sections Y U) (R ⧸ L) (Sections Y U ⧸ Extended L (Sections Y U)) :=
    Langlands.GroupScheme.HomScheme.quotient_isPushout L (Sections Y U)
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (Sections Y U) (R ⧸ L)
      (Sections Y U ⧸ Extended L (Sections Y U)))
  have hw : (pullback.fst (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) ≫ hU.isoSpec.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Sections Y U))) =
      pullback.snd (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ L))) := by
    change _ ≫ str Y U = _
    rw [← fromSpec_hom hU, Category.assoc, ← Category.assoc hU.isoSpec.hom,
      IsAffineOpen.isoSpec_hom_fromSpec]
    exact pullback.condition
  have e : pullback.fst (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) =
      hP.lift _ _ hw ≫ specMap (Ideal.Quotient.mk (Extended L (Sections Y U))) ≫
        hU.isoSpec.inv := by
    rw [← Category.assoc]
    change _ = (hP.lift _ _ hw ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Sections Y U) _))) ≫ _
    rw [hP.lift_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold AgreeMod at h
  rw [e]
  simp only [Category.assoc]
  rw [h]

/-- Maps agreeing modulo an ideal of the maximal ideal agree on the actual residue fibre. -/
lemma fibre_of_agreeMod {L : Ideal R} (hL : L ≤ maximalIdeal R) {U : Y.left.Opens}
    (hU : IsAffineOpen U) {T : Scheme.{u}} {a b : U.toScheme ⟶ T} (h : AgreeMod L hU a b) :
    pullback.fst (U.ι ≫ Y.hom) r ≫ a = pullback.fst (U.ι ≫ Y.hom) r ≫ b := by
  have e : r = specMap (Ideal.Quotient.factor hL) ≫ specMap (Ideal.Quotient.mk L) := by
    rw [← specMap_comp]
    congr 1
  rw [e]
  have h₂ := pullback_eq_of_agreeMod hU h
  have e₂ : pullback.fst (U.ι ≫ Y.hom)
        (specMap (Ideal.Quotient.factor hL) ≫ specMap (Ideal.Quotient.mk L)) =
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specMap (Ideal.Quotient.factor hL))
        (by rw [Category.assoc]; exact pullback.condition) ≫
        pullback.fst (U.ι ≫ Y.hom) (specMap (Ideal.Quotient.mk L)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e₂, Category.assoc, h₂, ← Category.assoc]

omit [IsLocalRing R] in
/-- Maps agreeing on the reduction of an affine open agree on every map into the open lying
over the quotient of the base. -/
lemma comp_eq_of_agreeMod {L : Ideal R} {U : Y.left.Opens} (hU : IsAffineOpen U)
    {T : Scheme.{u}} {a b : U.toScheme ⟶ T} (h : AgreeMod L hU a b) {T' : Scheme.{u}}
    (u : T' ⟶ U.toScheme) (v : T' ⟶ Spec (CommRingCat.of (R ⧸ L)))
    (huv : u ≫ U.ι ≫ Y.hom = v ≫ specMap (Ideal.Quotient.mk L)) : u ≫ a = u ≫ b := by
  rw [← pullback.lift_fst u v huv, Category.assoc, Category.assoc, pullback_eq_of_agreeMod hU h]

omit [IsLocalRing R] in
/-- Maps agreeing modulo a square-zero extended ideal agree on points. -/
lemma apply_eq_of_agreeMod {L : Ideal R} {U : Y.left.Opens} (hU : IsAffineOpen U)
    {T : Scheme.{u}} {a b : U.toScheme ⟶ T} (h : AgreeMod L hU a b)
    (hsq : Extended L (Sections Y U) ^ 2 = ⊥) (x : U.toScheme) : a x = b x := by
  obtain ⟨y, hy⟩ := Langlands.AlgebraicGeometry.specMap_surjective
    (Ideal.Quotient.mk (Extended L (Sections Y U))) Ideal.Quotient.mk_surjective (by
      intro z hz
      rw [Ideal.mk_ker] at hz
      have hz2 := Ideal.pow_mem_pow hz 2
      rw [hsq] at hz2
      exact ⟨2, Ideal.mem_bot.mp hz2⟩) (hU.isoSpec.hom x)
  have hx : x = hU.isoSpec.inv (specMap (Ideal.Quotient.mk (Extended L (Sections Y U))) y) := by
    change x = hU.isoSpec.inv (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Extended L (Sections Y U)))) y)
    rw [hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  unfold AgreeMod at h
  have e := congrArg (fun f ↦ f y) h
  simp only [Scheme.Hom.comp_apply] at e
  rw [hx]
  exact e

end Agreement

section Lattice

variable {α : Type*} [SemilatticeInf α] (a b c d : α)

theorem inf₄_le_cd : a ⊓ b ⊓ c ⊓ d ≤ c ⊓ d :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem inf₄_le_acd : a ⊓ b ⊓ c ⊓ d ≤ a ⊓ c ⊓ d :=
  le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (inf_le_left.trans inf_le_right)) inf_le_right

theorem inf₄_le_bcd : a ⊓ b ⊓ c ⊓ d ≤ b ⊓ c ⊓ d :=
  le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_left.trans inf_le_right)) inf_le_right

theorem inf₄_le_abd : a ⊓ b ⊓ c ⊓ d ≤ a ⊓ b ⊓ d :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem inf₃_le_bc : a ⊓ b ⊓ c ≤ b ⊓ c :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem inf₃_le_ac : a ⊓ b ⊓ c ≤ a ⊓ c :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

end Lattice

section Family

variable (Y : Over (Spec (CommRingCat.of R))) [IsSeparated Y.hom]

/-- Transition maps between the overlaps of a finite family of affine opens of a scheme over the
base. They fix points, lie over the base and restrict to the inclusion on the actual residue
fibre. -/
structure Family where
  L : Type u
  [fintype : Fintype L]
  V : L → Y.left.Opens
  affine : ∀ l, IsAffineOpen (V l)
  θ : ∀ l m, (V l ⊓ V m).toScheme ⟶ Y.left
  pointwise : ∀ l m, IsPointwiseInclusion (θ l m)
  overBase : ∀ l m, θ l m ≫ Y.hom = (V l ⊓ V m).ι ≫ Y.hom
  fibre : ∀ l m, pullback.fst ((V l ⊓ V m).ι ≫ Y.hom) r ≫ θ l m =
    pullback.fst ((V l ⊓ V m).ι ≫ Y.hom) r ≫ (V l ⊓ V m).ι

attribute [instance] Family.fintype

namespace Family

variable {Y} (D : Family Y)

theorem affine₂ (l m : D.L) : IsAffineOpen (D.V l ⊓ D.V m) :=
  affine_inf (D.affine l) (D.affine m)

theorem affine₃ (l m n : D.L) : IsAffineOpen (D.V l ⊓ D.V m ⊓ D.V n) :=
  affine_inf (D.affine₂ l m) (D.affine n)

theorem affine₄ (l m n p : D.L) : IsAffineOpen (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p) :=
  affine_inf (D.affine₃ l m n) (D.affine p)

/-- The transition `θ m n` on a triple overlap, as a map into the overlap of the first two. -/
def lift₃ (l m n : D.L) : (D.V l ⊓ D.V m ⊓ D.V n).toScheme ⟶ (D.V l ⊓ D.V m).toScheme :=
  restrictTo (D.θ m n) (D.pointwise m n) (W := D.V l ⊓ D.V m ⊓ D.V n)
    (inf₃_le_bc _ _ _) inf_le_left

omit [IsSeparated Y.hom] in
@[reassoc] theorem lift₃_ι (l m n : D.L) :
    D.lift₃ l m n ≫ (D.V l ⊓ D.V m).ι = Y.left.homOfLE (inf₃_le_bc _ _ _) ≫ D.θ m n :=
  restrictTo_ι _ _ _ _

/-- The composite of the transitions `θ m n` and `θ l m` on a triple overlap. -/
def comp (l m n : D.L) : (D.V l ⊓ D.V m ⊓ D.V n).toScheme ⟶ Y.left :=
  D.lift₃ l m n ≫ D.θ l m

/-- The transition `θ l n` on a triple overlap. -/
def direct (l m n : D.L) : (D.V l ⊓ D.V m ⊓ D.V n).toScheme ⟶ Y.left :=
  Y.left.homOfLE (inf₃_le_ac _ _ _) ≫ D.θ l n

omit [IsSeparated Y.hom] in
theorem comp_over (l m n : D.L) :
    D.comp l m n ≫ Y.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
  rw [comp, Category.assoc, D.overBase, lift₃_ι_assoc, D.overBase, ← Category.assoc,
    Scheme.homOfLE_ι]

omit [IsSeparated Y.hom] in
theorem direct_over (l m n : D.L) :
    D.direct l m n ≫ Y.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
  rw [direct, Category.assoc, D.overBase, ← Category.assoc, Scheme.homOfLE_ι]

/-- The cocycle condition after reduction modulo the extended ideal. -/
def Agrees (I : Ideal R) : Prop :=
  ∀ l m n, AgreeMod I (D.affine₃ l m n) (D.comp l m n) (D.direct l m n)

/-- The transition `θ n p` on a quadruple overlap, as a map into the first triple overlap. -/
def shift (l m n p : D.L) :
    (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).toScheme ⟶ (D.V l ⊓ D.V m ⊓ D.V n).toScheme :=
  restrictTo (D.θ n p) (D.pointwise n p) (inf₄_le_cd _ _ _ _) inf_le_left

omit [IsSeparated Y.hom] in
@[reassoc] theorem shift_ι (l m n p : D.L) :
    D.shift l m n p ≫ (D.V l ⊓ D.V m ⊓ D.V n).ι =
      Y.left.homOfLE (inf₄_le_cd _ _ _ _) ≫ D.θ n p :=
  restrictTo_ι _ _ _ _

omit [IsSeparated Y.hom] in
theorem shift_over (l m n p : D.L) :
    D.shift l m n p ≫ (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
  rw [shift_ι_assoc, D.overBase, ← Category.assoc, Scheme.homOfLE_ι]

omit [IsSeparated Y.hom] in
theorem shift_fibre (l m n p : D.L) :
    pullback.fst ((D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom) r ≫ D.shift l m n p =
      pullback.fst ((D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom) r ≫
        Y.left.homOfLE inf_le_left := by
  rw [← cancel_mono (D.V l ⊓ D.V m ⊓ D.V n).ι, Category.assoc, shift_ι, Category.assoc,
    Scheme.homOfLE_ι, fibre_homOfLE _ (D.fibre n p), Scheme.homOfLE_ι]

omit [IsSeparated Y.hom] in
theorem shift_direct (l m n p : D.L) :
    D.shift l m n p ≫ D.direct l m n =
      Y.left.homOfLE (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp l n p := by
  have e : D.shift l m n p ≫ Y.left.homOfLE (inf₃_le_ac (D.V l) (D.V m) (D.V n)) =
      Y.left.homOfLE (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l n p := by
    rw [← cancel_mono (D.V l ⊓ D.V n).ι, Category.assoc, Scheme.homOfLE_ι, shift_ι,
      Category.assoc, lift₃_ι, Scheme.homOfLE_homOfLE_assoc]
  rw [direct, comp, ← Category.assoc, e, Category.assoc]

omit [IsSeparated Y.hom] in
theorem shift_lift₃_ι (l m n p : D.L) :
    D.shift l m n p ≫ D.lift₃ l m n ≫ (D.V l ⊓ D.V m).ι =
      Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp m n p := by
  have e : D.shift l m n p ≫ Y.left.homOfLE (inf₃_le_bc (D.V l) (D.V m) (D.V n)) =
      Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ m n p := by
    rw [← cancel_mono (D.V m ⊓ D.V n).ι, Category.assoc, Scheme.homOfLE_ι, shift_ι,
      Category.assoc, lift₃_ι, Scheme.homOfLE_homOfLE_assoc]
  rw [lift₃_ι, comp, ← Category.assoc, e, Category.assoc]

omit [IsSeparated Y.hom] in
theorem restrict_lift₃_ι (l m n p : D.L) :
    Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l m p ≫
        (D.V l ⊓ D.V m).ι =
      Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct m n p := by
  rw [lift₃_ι, direct, Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]

omit [IsSeparated Y.hom] in
theorem restrict_direct (l m n p : D.L) :
    Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct l m p =
      Y.left.homOfLE (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct l n p := by
  rw [direct, direct, Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc]

end Family

end Family

section Obstruction

variable {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

namespace Family

variable (D : Family Y) (hD : D.Agrees I) (π : Y ⟶ Z.X)

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem comp_π_over (l m n : D.L) :
    (D.comp l m n ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
  rw [Category.assoc, Over.w π, D.comp_over]

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem direct_π_over (l m n : D.L) :
    (D.direct l m n ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n).ι ≫ Y.hom := by
  rw [Category.assoc, Over.w π, D.direct_over]

/-- The obstruction cochain: on each triple overlap, the difference coordinates, observed
through `π`, of the composite of two transitions and the third transition. -/
def obstruction (l m n : D.L) (j : Index) :
    Γ(F.obj.left, F.toOriginal ⁻¹ᵁ (D.V l ⊓ D.V m ⊓ D.V n)) :=
  openDifference b F (D.affine₃ l m n) (pt _ (D.comp l m n ≫ π.left) (D.comp_π_over π l m n))
    (pt _ (D.direct l m n ≫ π.left) (D.direct_π_over π l m n))
    (agree_pt_of _ _ ((hD l m n).comp π.left)) j

/-- Restriction of the obstruction to a smaller affine open. -/
theorem obstruction_restrict {a c e : D.L} {W : Y.left.Opens} (hW : IsAffineOpen W)
    (h : W ≤ D.V a ⊓ D.V c ⊓ D.V e)
    (h₁ : (Y.left.homOfLE h ≫ D.comp a c e ≫ π.left) ≫ Z.X.hom = W.ι ≫ Y.hom)
    (h₂ : (Y.left.homOfLE h ≫ D.direct a c e ≫ π.left) ≫ Z.X.hom = W.ι ≫ Y.hom)
    (ha : Z.Agree I (pt hW _ h₁) (pt hW _ h₂)) (j : Index) :
    openDifference b F hW (pt hW _ h₁) (pt hW _ h₂) ha j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono h)).op).hom
        (D.obstruction b F hD π a c e j) :=
  openDifference_pt_restrict b F h (D.affine₃ a c e) hW (D.comp_π_over π a c e)
    (D.direct_π_over π a c e) (agree_pt_of _ _ ((hD a c e).comp π.left)) j

/-- Pre-composition of the obstruction with the transition on a quadruple overlap. -/
theorem obstruction_shift (l m n p : D.L)
    (h₁ : (D.shift l m n p ≫ D.comp l m n ≫ π.left) ≫ Z.X.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (h₂ : (D.shift l m n p ≫ D.direct l m n ≫ π.left) ≫ Z.X.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (ha : Z.Agree I (pt (D.affine₄ l m n p) _ h₁) (pt (D.affine₄ l m n p) _ h₂)) (j : Index) :
    openDifference b F (D.affine₄ l m n p) (pt _ _ h₁) (pt _ _ h₂) ha j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p ≤ _))).op).hom
        (D.obstruction b F hD π l m n j) :=
  openDifference_pt_ringOf b F inf_le_left (D.affine₃ l m n) (D.affine₄ l m n p)
    (D.shift l m n p) (D.shift_over l m n p) (D.shift_fibre l m n p) (D.comp_π_over π l m n)
    (D.direct_π_over π l m n) (agree_pt_of _ _ ((hD l m n).comp π.left)) j

include hD in
/-- Post-composition with the transition `θ l m` does not change the difference coordinates. -/
theorem obstruction_post (l m n p : D.L)
    (h₁ : (D.shift l m n p ≫ D.comp l m n ≫ π.left) ≫ Z.X.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (h₂ : (Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp l m p ≫
      π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (h₃ : (Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp m n p ≫
      π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (h₄ : (Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct m n p ≫
      π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom)
    (ha : Z.Agree I (pt (D.affine₄ l m n p) _ h₁) (pt (D.affine₄ l m n p) _ h₂))
    (hb : Z.Agree I (pt (D.affine₄ l m n p) _ h₃) (pt (D.affine₄ l m n p) _ h₄)) (j : Index) :
    openDifference b F (D.affine₄ l m n p) (pt _ _ h₁) (pt _ _ h₂) ha j =
      openDifference b F (D.affine₄ l m n p) (pt _ _ h₃) (pt _ _ h₄) hb j := by
  have h4 := D.affine₄ l m n p
  have hu₁ : (D.shift l m n p ≫ D.lift₃ l m n) ≫ (D.V l ⊓ D.V m).ι ≫ Y.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
    rw [Category.assoc, ← Category.assoc (D.lift₃ l m n), ← Category.assoc (D.shift l m n p),
      shift_lift₃_ι, Category.assoc, D.comp_over, ← Category.assoc, Scheme.homOfLE_ι]
  have hu₅ : (Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l m p) ≫
      (D.V l ⊓ D.V m).ι ≫ Y.hom = (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
    rw [Category.assoc, ← Category.assoc (D.lift₃ l m p), ← Category.assoc (Y.left.homOfLE _),
      restrict_lift₃_ι, Category.assoc, D.direct_over, ← Category.assoc, Scheme.homOfLE_ι]
  have hu : AgreeMod I h4 (D.shift l m n p ≫ D.lift₃ l m n)
      (Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l m p) :=
    AgreeMod.of_mono (D.V l ⊓ D.V m).ι
      ((AgreeMod.homOfLE_comp (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) h4
        (hD m n p)).of_eq (by rw [Category.assoc, shift_lift₃_ι])
          (by rw [Category.assoc, restrict_lift₃_ι]))
  have hfib : pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) r ≫ D.θ l m ≫ π.left =
      pullback.fst ((D.V l ⊓ D.V m).ι ≫ Y.hom) r ≫ (D.V l ⊓ D.V m).ι ≫ π.left := by
    rw [← Category.assoc, D.fibre l m, Category.assoc]
  have hG₁ : (D.θ l m ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom := by
    rw [Category.assoc, Over.w π, D.overBase]
  have hG₂ : ((D.V l ⊓ D.V m).ι ≫ π.left) ≫ Z.X.hom = (D.V l ⊓ D.V m).ι ≫ Y.hom := by
    rw [Category.assoc, Over.w π]
  have E := openDifference_pt_comp_eq b F h4 hu₁ hu₅ hu (D.θ l m ≫ π.left)
    ((D.V l ⊓ D.V m).ι ≫ π.left) hG₁ hG₂ hfib j
  have e₁ : D.shift l m n p ≫ D.comp l m n ≫ π.left =
      (D.shift l m n p ≫ D.lift₃ l m n) ≫ D.θ l m ≫ π.left := by
    rw [comp]
    simp only [Category.assoc]
  have e₂ : Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp l m p ≫
      π.left = (Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l m p) ≫
        D.θ l m ≫ π.left := by
    rw [comp]
    simp only [Category.assoc]
  have e₃ : (D.shift l m n p ≫ D.lift₃ l m n) ≫ (D.V l ⊓ D.V m).ι ≫ π.left =
      Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp m n p ≫ π.left := by
    rw [Category.assoc, ← Category.assoc (D.lift₃ l m n), ← Category.assoc (D.shift l m n p),
      shift_lift₃_ι, Category.assoc]
  have e₄ : (Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.lift₃ l m p) ≫
      (D.V l ⊓ D.V m).ι ≫ π.left =
      Y.left.homOfLE (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct m n p ≫ π.left := by
    rw [Category.assoc, ← Category.assoc (D.lift₃ l m p), ← Category.assoc (Y.left.homOfLE _),
      restrict_lift₃_ι, Category.assoc]
  exact (openDifference_pt_congr b F h4 e₁ e₂ h₁ h₂ _ _ ha _ j).trans
    (E.trans (openDifference_pt_congr b F h4 e₃ e₄ _ _ h₃ h₄ _ hb j))

/-- The obstruction satisfies the Čech cocycle identity on every quadruple overlap. -/
theorem obstruction_four (l m n p : D.L) (j : Index) :
    (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf_le_left : D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p ≤ _))).op).hom
        (D.obstruction b F hD π l m n j) +
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)))).op).hom
        (D.obstruction b F hD π l n p j) =
    (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)))).op).hom
        (D.obstruction b F hD π m n p j) +
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)))).op).hom
        (D.obstruction b F hD π l m p j) := by
  have h4 := D.affine₄ l m n p
  have hP1 : (D.shift l m n p ≫ D.comp l m n ≫ π.left) ≫ Z.X.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
    rw [Category.assoc, D.comp_π_over π l m n, D.shift_over]
  have hP2 : (D.shift l m n p ≫ D.direct l m n ≫ π.left) ≫ Z.X.hom =
      (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
    rw [Category.assoc, D.direct_π_over π l m n, D.shift_over]
  have hr (a c e : D.L) (h : D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p ≤ D.V a ⊓ D.V c ⊓ D.V e)
      (g : (D.V a ⊓ D.V c ⊓ D.V e).toScheme ⟶ Z.X.left)
      (hg : g ≫ Z.X.hom = (D.V a ⊓ D.V c ⊓ D.V e).ι ≫ Y.hom) :
      (Y.left.homOfLE h ≫ g) ≫ Z.X.hom = (D.V l ⊓ D.V m ⊓ D.V n ⊓ D.V p).ι ≫ Y.hom := by
    rw [Category.assoc, hg, ← Category.assoc, Scheme.homOfLE_ι]
  have hP3 := hr l n p (inf₄_le_acd _ _ _ _) _ (D.comp_π_over π l n p)
  have hP4 := hr l n p (inf₄_le_acd _ _ _ _) _ (D.direct_π_over π l n p)
  have hP5 := hr l m p (inf₄_le_abd _ _ _ _) _ (D.comp_π_over π l m p)
  have hP6 := hr l m p (inf₄_le_abd _ _ _ _) _ (D.direct_π_over π l m p)
  have hP7 := hr m n p (inf₄_le_bcd _ _ _ _) _ (D.comp_π_over π m n p)
  have hP8 := hr m n p (inf₄_le_bcd _ _ _ _) _ (D.direct_π_over π m n p)
  have a12 : AgreeMod I h4 (D.shift l m n p ≫ D.comp l m n ≫ π.left)
      (D.shift l m n p ≫ D.direct l m n ≫ π.left) :=
    AgreeMod.ringOf_comp _ h4 _ (D.shift_over l m n p) ((hD l m n).comp π.left)
  have a34 := AgreeMod.homOfLE_comp (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) h4
    ((hD l n p).comp π.left)
  have a56 := AgreeMod.homOfLE_comp (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) h4
    ((hD l m p).comp π.left)
  have a78 := AgreeMod.homOfLE_comp (inf₄_le_bcd (D.V l) (D.V m) (D.V n) (D.V p)) h4
    ((hD m n p).comp π.left)
  have e23 : D.shift l m n p ≫ D.direct l m n ≫ π.left =
      Y.left.homOfLE (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.comp l n p ≫ π.left := by
    rw [← Category.assoc, D.shift_direct, Category.assoc]
  have e64 : Y.left.homOfLE (inf₄_le_abd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct l m p ≫
      π.left = Y.left.homOfLE (inf₄_le_acd (D.V l) (D.V m) (D.V n) (D.V p)) ≫ D.direct l n p ≫
        π.left := by
    rw [← Category.assoc, D.restrict_direct, Category.assoc]
  have a24 := a34.of_eq e23.symm rfl
  have a54 := a56.of_eq rfl e64
  have a15 := a12.trans (a24.trans a54.symm)
  have s1 := D.obstruction_shift b F hD π l m n p hP1 hP2 (agree_pt_of hP1 hP2 a12) j
  have s2 := D.obstruction_restrict b F hD π h4 (inf₄_le_acd _ _ _ _) hP3 hP4
    (agree_pt_of hP3 hP4 a34) j
  have s3 := D.obstruction_restrict b F hD π h4 (inf₄_le_bcd _ _ _ _) hP7 hP8
    (agree_pt_of hP7 hP8 a78) j
  have s4 := D.obstruction_restrict b F hD π h4 (inf₄_le_abd _ _ _ _) hP5 hP6
    (agree_pt_of hP5 hP6 a56) j
  have s5 := D.obstruction_post b F hD π l m n p hP1 hP5 hP7 hP8 (agree_pt_of hP1 hP5 a15)
    (agree_pt_of hP7 hP8 a78) j
  have c1 := openDifference_pt_congr b F h4 e23 rfl hP2 hP4 hP3 hP4 (agree_pt_of hP2 hP4 a24)
    (agree_pt_of hP3 hP4 a34) j
  have c2 := openDifference_pt_congr b F h4 rfl e64.symm hP5 hP4 hP5 hP6
    (agree_pt_of hP5 hP4 a54) (agree_pt_of hP5 hP6 a56) j
  have add1 := openDifference_add b F h4 _ _ _ (agree_pt_of hP1 hP2 a12)
    (agree_pt_of hP2 hP4 a24) j
  have add2 := openDifference_add b F h4 _ _ _ (agree_pt_of hP1 hP5 a15)
    (agree_pt_of hP5 hP4 a54) j
  exact (congrArg₂ (· + ·) s1 s2).symm.trans ((congrArg₂ (· + ·) rfl c1.symm).trans
    (add1.symm.trans (add2.trans (congrArg₂ (· + ·) (s5.trans s3) (c2.trans s4)))))

end Family

end Obstruction

end Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
