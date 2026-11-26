import Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
import Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityProof
import Mathlib.AlgebraicGeometry.Gluing

/-! # Čech differences and gluing of ordinary elementary lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts
open AffineOpenQuotientSections
open scoped ElementaryIdealCoefficients

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {I : Ideal R} {Z : Target R}
variable {Y Y' : Over (Spec (CommRingCat.of R))}

/-- Restriction of an actual morphism to the spectrum of an affine chart. -/
def localPoint (g : Y ⟶ Z.X) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    Z.Points (Sections Y U) := Over.homMk (hU.fromSpec ≫ g.left) (by
      rw [Category.assoc, Over.w g, fromSpec_hom hU]
      rfl)

@[simp] lemma localPoint_left (g : Y ⟶ Z.X) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    (localPoint g hU).left = hU.fromSpec ≫ g.left := rfl

variable (B : Reduction Y I) {g₀ : B.obj.left ⟶ Z.X.left}

/-- The prescribed reduction of an affine lift is the restriction to the actual reduced chart. -/
abbrev IsLocalLift {U : Y.left.Opens} (hU : IsAffineOpen U) (x : Z.Points (Sections Y U)) : Prop :=
  specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ x.left = B.chart hU ≫ g₀

lemma localPoint_isLift {g : Y ⟶ Z.X} (hg : B.toOriginal ≫ g.left = g₀)
    {U : Y.left.Opens} (hU : IsAffineOpen U) : IsLocalLift (g₀ := g₀) B hU (localPoint g hU) := by
  change specMap (Ideal.Quotient.mk (Extended I (Sections Y U))) ≫ hU.fromSpec ≫ g.left = _
  rw [← B.chart_toOriginal_assoc, hg]

/-- An affine lift of the prescribed reduction exists by smoothness. -/
theorem exists_localLift [Fact (maximalIdeal R * I = ⊥)] [Smooth Z.X.hom] (hI : I ≤ maximalIdeal R)
    (hg₀ : g₀ ≫ Z.X.hom = B.toOriginal ≫ Y.hom) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    ∃ x : Z.Points (Sections Y U), IsLocalLift (g₀ := g₀) B hU x := by
  apply Z.exists_lift I hI
  rw [Category.assoc, hg₀, B.chart_toOriginal_assoc, fromSpec_hom hU]

lemma restrict_isLocalLift {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x : Z.Points (Sections Y U))
    (hx : IsLocalLift (g₀ := g₀) B hU x) :
    IsLocalLift (g₀ := g₀) B hV (Z.restrict (restrict Y h) x) := by
  change specMap (Ideal.Quotient.mk (Extended I (Sections Y V))) ≫
    specMap (restrict Y h).toRingHom ≫ x.left = _
  rw [← specMap_comp_assoc, Reduction.mk_comp_map, specMap_comp_assoc, hx,
    B.chart_restrict_assoc h hU hV]

lemma sectionMap_isLocalLift (A : Reduction Y' I) (f : Y' ⟶ Y)
    {U : Y.left.Opens} {V : Y'.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x : Z.Points (Sections Y U))
    (hx : IsLocalLift (g₀ := g₀) B hU x) :
    IsLocalLift (g₀ := (A.map B f).left ≫ g₀) A hV (Z.restrict (sectionMap f h) x) := by
  change specMap (Ideal.Quotient.mk (Extended I (Sections Y' V))) ≫
    specMap (sectionMap f h).toRingHom ≫ x.left = _
  rw [← specMap_comp_assoc, Reduction.mk_comp_map, specMap_comp_assoc, hx,
    A.chart_map_assoc B f h hU hV]

lemma restrict_localPoint (g : Y ⟶ Z.X) {U V : Y.left.Opens}
    (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Z.restrict (restrict Y h) (localPoint g hU) = localPoint g hV := by
  apply Over.OverMorphism.ext
  rw [Target.restrict_left, localPoint_left, localPoint_left, restrict_fromSpec_assoc Y h hU hV]

lemma sectionMap_localPoint (f : Y' ⟶ Y) (g : Y ⟶ Z.X)
    {U : Y.left.Opens} {V : Y'.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Z.restrict (sectionMap f h) (localPoint g hU) = localPoint (f ≫ g) hV := by
  apply Over.OverMorphism.ext
  rw [Target.restrict_left, localPoint_left, localPoint_left, Over.comp_left,
    sectionMap_fromSpec_assoc f h hU hV]

/-- Equality can be checked on the spectra of the affine opens of a cover. -/
theorem hom_ext_fromSpec {X T : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ a, IsAffineOpen (U a)) (hc : ⊤ ≤ iSup U) {f g : X ⟶ T}
    (h : ∀ a, (hU a).fromSpec ≫ f = (hU a).fromSpec ≫ g) : f = g := by
  let cover := X.openCoverOfIsOpenCover U (top_le_iff.mp hc)
  apply cover.hom_ext
  intro a
  apply (cancel_epi (hU a).isoSpec.inv).mp
  change (hU a).isoSpec.inv ≫ (U a).ι ≫ f = (hU a).isoSpec.inv ≫ (U a).ι ≫ g
  simpa only [← Category.assoc, IsAffineOpen.isoSpec_inv_ι] using h a

/-- Testing equality of maps from the reduction on its affine quotient charts. -/
theorem hom_ext_quotientChart {ι : Type*} (U : ι → Y.left.Opens)
    (hU : ∀ a, IsAffineOpen (U a)) (hc : ⊤ ≤ iSup U) {f g : B.obj.left ⟶ Z.X.left}
    (h : ∀ a, B.chart (hU a) ≫ f = B.chart (hU a) ≫ g) : f = g := by
  apply hom_ext_fromSpec (fun a ↦ B.toOriginal ⁻¹ᵁ U a) (fun a ↦ B.affine_preimage (hU a))
    (B.cover_preimage U hc)
  intro a
  have hi : IsIso (specMap (quotientEquiv B.cartesian (hU a)).symm.toRingHom) := by
    change IsIso (Spec.map (RingEquiv.toCommRingCatIso (quotientEquiv B.cartesian (hU a)).symm).hom)
    infer_instance
  exact (cancel_epi (specMap (quotientEquiv B.cartesian (hU a)).symm.toRingHom)).mp
    (by simpa only [Reduction.chart, Category.assoc] using h a)

omit [IsLocalRing R] in
@[reassoc] private lemma chart_restrict_iso {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    hV.isoSpec.inv ≫ Y.left.homOfLE h ≫ hU.isoSpec.hom = specMap (restrict Y h).toRingHom := by
  apply (cancel_mono hU.fromSpec).mp
  simp only [Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι, restrict_fromSpec Y h hU hV]

/-- Compatible local lifts glue to an actual morphism over the base. -/
theorem exists_glue {ι : Type*} (U : ι → Y.left.Opens) (hU : ∀ a, IsAffineOpen (U a))
    (hUU : ∀ a b, IsAffineOpen (U a ⊓ U b)) (hc : ⊤ ≤ iSup U)
    (x : ∀ a, Z.Points (Sections Y (U a))) (hx : ∀ a, IsLocalLift (g₀ := g₀) B (hU a) (x a))
    (hxx : ∀ a b, Z.restrict (restrict Y (U := U a) (V := U a ⊓ U b) inf_le_left) (x a) =
      Z.restrict (restrict Y (U := U b) (V := U a ⊓ U b) inf_le_right) (x b)) :
    ∃ g : Y ⟶ Z.X, B.toOriginal ≫ g.left = g₀ ∧ ∀ a, localPoint g (hU a) = x a := by
  let cover := Y.left.openCoverOfIsOpenCover U (top_le_iff.mp hc)
  let m (a : ι) : (U a).toScheme ⟶ Z.X.left := (hU a).isoSpec.hom ≫ (x a).left
  have hm (a b : ι) : pullback.fst (U a).ι (U b).ι ≫ m a =
      pullback.snd (U a).ι (U b).ι ≫ m b := by
    let pb := isPullback_opens_inf (U a) (U b)
    apply (cancel_epi ((hUU a b).isoSpec.inv ≫ pb.isoPullback.hom)).mp
    simp only [Category.assoc, pb.isoPullback_hom_fst_assoc, pb.isoPullback_hom_snd_assoc, m]
    rw [chart_restrict_iso_assoc inf_le_left (hU a) (hUU a b),
      chart_restrict_iso_assoc inf_le_right (hU b) (hUU a b)]
    exact congrArg (fun g : Z.Points (Sections Y (U a ⊓ U b)) ↦ g.left) (hxx a b)

  let g := cover.glueMorphisms m hm
  have hg (a : ι) : (hU a).fromSpec ≫ g = (x a).left := by
    rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
    change (hU a).isoSpec.inv ≫ cover.f a ≫ cover.glueMorphisms m hm = _
    rw [cover.ι_glueMorphisms]
    simp [m]
  let gOver : Y ⟶ Z.X := Over.homMk g (by
    apply hom_ext_fromSpec U hU hc
    intro a
    rw [← Category.assoc, hg, Over.w (x a), fromSpec_hom (hU a)]
    rfl)
  refine ⟨gOver, ?_, fun a ↦ Over.OverMorphism.ext (hg a)⟩
  apply hom_ext_quotientChart B U hU hc
  intro a
  change B.chart (hU a) ≫ B.toOriginal ≫ g = B.chart (hU a) ≫ g₀
  rw [B.chart_toOriginal_assoc, hg, hx a]

section OpenDifferences

variable [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] [Smooth Y'.hom]
  (b : Z.Coordinates I) (F : Reduction Y (maximalIdeal R))
  (F' : Reduction Y' (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

/-- Scalar difference functions on the actual residue fibre of an affine open. -/
def openDifference {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x y : Z.Points (Sections Y U)) (h : Z.Agree I x y) (j : Index) :
    Γ(F.obj.left, F.toOriginal ⁻¹ᵁ U) := by
  let : Module.Flat R (Sections Y U) := flat hU
  exact residueEquiv F.cartesian hU (b.difference x y h j)

lemma openDifference_congr {U : Y.left.Opens} (hU : IsAffineOpen U)
    {x y x' y' : Z.Points (Sections Y U)} (hx : x = x') (hy : y = y')
    (h : Z.Agree I x y) (h' : Z.Agree I x' y') (j : Index) :
    openDifference b F hU x y h j = openDifference b F hU x' y' h' j := by
  cases hx
  cases hy
  rfl

@[simp] lemma openDifference_same {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x : Z.Points (Sections Y U)) (j : Index) : openDifference b F hU x x rfl j = 0 := by
  simp [openDifference]

lemma openDifference_add {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x y z : Z.Points (Sections Y U)) (hxy : Z.Agree I x y) (hyz : Z.Agree I y z) (j : Index) :
    openDifference b F hU x z (hxy.trans hyz) j = openDifference b F hU x y hxy j +
      openDifference b F hU y z hyz j := by
  let : Module.Flat R (Sections Y U) := flat hU
  simp only [openDifference]
  rw [b.difference_add x y z hxy hyz, Pi.add_apply, map_add]

/-- Difference coordinates on a smaller affine open are restrictions of functions. -/
lemma openDifference_restrict {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (x y : Z.Points (Sections Y U))
    (hxy : Z.Agree I x y) (j : Index) :
    openDifference b F hV (Z.restrict (restrict Y h) x) (Z.restrict (restrict Y h) y)
      (Z.restrict_agree I (restrict Y h) x y hxy) j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono h)).op).hom
        (openDifference b F hU x y hxy j) := by
  let : Module.Flat R (Sections Y U) := flat hU
  let : Module.Flat R (Sections Y V) := flat hV
  simp only [openDifference]
  rw [b.difference_restrict (restrict Y h) x y hxy j]
  exact residueEquiv_restrict F.cartesian h hU hV _

/-- Difference coordinates along a map of affine opens pull back as functions. -/
lemma openDifference_sectionMap (f : Y' ⟶ Y) {U : Y.left.Opens} {V : Y'.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hₖ : F'.toOriginal ⁻¹ᵁ V ≤ (F'.map F f).left ⁻¹ᵁ (F.toOriginal ⁻¹ᵁ U))
    (x y : Z.Points (Sections Y U)) (hxy : Z.Agree I x y) (j : Index) :
    openDifference b F' hV (Z.restrict (sectionMap f h) x) (Z.restrict (sectionMap f h) y)
      (Z.restrict_agree I (sectionMap f h) x y hxy) j =
      ((F'.map F f).left.appLE _ _ hₖ).hom (openDifference b F hU x y hxy j) := by
  let : Module.Flat R (Sections Y U) := flat hU
  let : Module.Flat R (Sections Y' V) := flat hV
  simp only [openDifference]
  rw [b.difference_restrict (sectionMap f h) x y hxy j]
  exact residueEquiv_sectionMap F'.cartesian F.cartesian f (F'.map F f)
    (F'.map_left_toOriginal f).symm h hₖ hU hV _

/-- Correct a point on an affine open by a family of actual residue sections. -/
def correctOpen {U : Y.left.Opens} (hU : IsAffineOpen U) (x : Z.Points (Sections Y U))
    (d : Index → Γ(F.obj.left, F.toOriginal ⁻¹ᵁ U)) : Z.Points (Sections Y U) := by
  let : Module.Flat R (Sections Y U) := flat hU
  exact b.correctBy x (fun j ↦ (residueEquiv F.cartesian hU).symm (d j))

lemma correctOpen_agree {U : Y.left.Opens} (hU : IsAffineOpen U) (x : Z.Points (Sections Y U))
    (d : Index → Γ(F.obj.left, F.toOriginal ⁻¹ᵁ U)) : Z.Agree I x (correctOpen b F hU x d) := by
  let : Module.Flat R (Sections Y U) := flat hU
  exact b.correctBy_agree _ _

@[simp] lemma openDifference_correctOpen {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x : Z.Points (Sections Y U)) (d : Index → Γ(F.obj.left, F.toOriginal ⁻¹ᵁ U)) (j : Index) :
    openDifference b F hU x (correctOpen b F hU x d) (correctOpen_agree b F hU x d) j = d j := by
  let : Module.Flat R (Sections Y U) := flat hU
  simp [openDifference, correctOpen]

lemma eq_of_openDifference_eq_zero {U : Y.left.Opens} (hU : IsAffineOpen U)
    (x y : Z.Points (Sections Y U)) (h : Z.Agree I x y)
    (h₀ : ∀ j : Index, openDifference b F hU x y h j = 0) : x = y := by
  let : Module.Flat R (Sections Y U) := flat hU
  apply b.eq_of_difference_eq_zero _ _ h
  funext j
  apply (residueEquiv F.cartesian hU).injective
  simpa only [openDifference, Pi.zero_apply, map_zero] using h₀ j

end OpenDifferences

private lemma restrict_trans_point {U V W : Y.left.Opens}
    (h₁ : W ≤ V) (h₂ : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (x : Z.Points (Sections Y U)) :
    Z.restrict (restrict Y h₁) (Z.restrict (restrict Y h₂) x) =
      Z.restrict (restrict Y (h₁.trans h₂)) x := by
  apply Over.OverMorphism.ext
  simp only [Target.restrict_left]
  have h : specMap (restrict Y h₁).toRingHom ≫ specMap (restrict Y h₂).toRingHom =
      specMap (restrict Y (h₁.trans h₂)).toRingHom := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, restrict_fromSpec Y h₂ hU hV, restrict_fromSpec Y h₁ hV hW,
      restrict_fromSpec Y (h₁.trans h₂) hU hW]
  rw [← Category.assoc, h]

omit [IsLocalRing R] in
lemma affine_inf [IsSeparated Y.hom] {U V : Y.left.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  (isAffineHom_diagonal_iff (f := Y.hom)).mp inferInstance ⊤ (isAffineOpen_top _) _
    (by simp) _ (by simp) hU hV

section Cech

variable [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] [IsSeparated Y.hom]
  (b : Z.Coordinates I) (F : Reduction Y (maximalIdeal R))
  {ι : Type*} (U : ι → Y.left.Opens) (hU : ∀ a, IsAffineOpen (U a))
  (x : ∀ a, Z.Points (Sections Y (U a))) (hx : ∀ a, IsLocalLift (g₀ := g₀) B (hU a) (x a))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank
local notation "overlap" => (fun a d ↦ U a ⊓ U d)
local notation "affineOverlap" => (fun a d ↦ affine_inf (Y := Y) (hU a) (hU d))
set_option quotPrecheck false in
local notation "fibreOpen" => (fun V ↦ F.toOriginal ⁻¹ᵁ V)

include hx in
omit [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] in
private theorem overlap_agree (a d : ι) : Z.Agree I
      (Z.restrict (restrict Y (U := U a) (V := overlap a d) inf_le_left) (x a))
      (Z.restrict (restrict Y (U := U d) (V := overlap a d) inf_le_right) (x d)) :=
  (restrict_isLocalLift B inf_le_left (hU a) (affineOverlap a d) _ (hx a)).trans
    (restrict_isLocalLift B inf_le_right (hU d) (affineOverlap a d) _ (hx d)).symm

/-- Difference of two local lifts on their overlap. -/
def cocycle (a d : ι) (j : Index) : Γ(F.obj.left, fibreOpen (overlap a d)) :=
  openDifference b F (affineOverlap a d)
    (Z.restrict (restrict Y inf_le_left) (x a)) (Z.restrict (restrict Y inf_le_right) (x d))
    (overlap_agree B U hU x hx a d) j

private theorem cocycle_affine_restrict (a d : ι) {V : Y.left.Opens}
    (hV : IsAffineOpen V) (h : V ≤ overlap a d) (j : Index) :
    (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono h)).op).hom
        (cocycle B b F U hU x hx a d j) =
      openDifference b F hV (Z.restrict (restrict Y (h.trans inf_le_left)) (x a))
        (Z.restrict (restrict Y (h.trans inf_le_right)) (x d))
        ((restrict_isLocalLift B (h.trans inf_le_left) (hU a) hV _ (hx a)).trans
          (restrict_isLocalLift B (h.trans inf_le_right) (hU d) hV _ (hx d)).symm) j := by
  rw [cocycle, ← openDifference_restrict b F h (affineOverlap a d) hV]
  have h₁ := restrict_trans_point h inf_le_left (hU a) (affineOverlap a d) hV (x a)
  have h₂ := restrict_trans_point h inf_le_right (hU d) (affineOverlap a d) hV (x d)
  exact openDifference_congr b F hV h₁ h₂ _ _ j

/-- On every common open of the three charts the difference satisfies the Čech identity. -/
theorem cocycle_condition (a d e : ι) {O : F.obj.left.Opens}
    (h₁ : O ≤ fibreOpen (overlap a d)) (h₂ : O ≤ fibreOpen (overlap d e))
    (h₃ : O ≤ fibreOpen (overlap a e)) (j : Index) :
    (F.obj.left.presheaf.map (homOfLE h₁).op).hom (cocycle B b F U hU x hx a d j) +
      (F.obj.left.presheaf.map (homOfLE h₂).op).hom (cocycle B b F U hU x hx d e j) =
      (F.obj.left.presheaf.map (homOfLE h₃).op).hom (cocycle B b F U hU x hx a e j) := by
  let V := overlap a d ⊓ U e
  have hV : IsAffineOpen V := affine_inf (affineOverlap a d) (hU e)
  have e₁ : V ≤ overlap a d := inf_le_left
  have e₂ : V ≤ overlap d e := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e₃ : V ≤ overlap a e := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hO : O ≤ fibreOpen V := by
    intro z hz
    exact ⟨h₁ hz, (h₂ hz).2⟩
  have hVsum :
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono e₁)).op).hom
          (cocycle B b F U hU x hx a d j) +
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono e₂)).op).hom
          (cocycle B b F U hU x hx d e j) =
        (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono e₃)).op).hom
          (cocycle B b F U hU x hx a e j) := by
    rw [cocycle_affine_restrict B b F U hU x hx a d hV e₁ j,
      cocycle_affine_restrict B b F U hU x hx d e hV e₂ j,
      cocycle_affine_restrict B b F U hU x hx a e hV e₃ j]
    exact (openDifference_add b F hV _ _ _ _ _ j).symm
  have hsum := congrArg ((F.obj.left.presheaf.map (homOfLE hO).op).hom) hVsum
  simpa only [map_add, Picard.FieldTwoAxisH1Injectivity.map_map_apply] using hsum

/-- Cochains with the prescribed differences correct the local lifts to a global lift. -/
theorem exists_lift_of_coboundary (hc : ⊤ ≤ iSup U)
    (d : ∀ a, Index → Γ(F.obj.left, fibreOpen (U a)))
    (hd : ∀ a c j, cocycle B b F U hU x hx a c j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (show overlap a c ≤ U a from inf_le_left))).op).hom (d a j) -
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (show overlap a c ≤ U c from inf_le_right))).op).hom (d c j)) :
    ∃ g : Y ⟶ Z.X, B.toOriginal ≫ g.left = g₀ ∧
      ∀ a, localPoint g (hU a) = correctOpen b F (hU a) (x a) (d a) := by
  let y (a : ι) := correctOpen b F (hU a) (x a) (d a)
  have hxy (a : ι) : Z.Agree I (x a) (y a) := correctOpen_agree b F _ _ _
  have hy (a : ι) : IsLocalLift (g₀ := g₀) B (hU a) (y a) := (hxy a).symm.trans (hx a)
  apply exists_glue B U hU (fun a c ↦ affineOverlap a c) hc y hy
  intro a c
  let leftMap := restrict Y (U := U a) (V := overlap a c) inf_le_left
  let rightMap := restrict Y (U := U c) (V := overlap a c) inf_le_right
  let xa := Z.restrict leftMap (x a)
  let xc := Z.restrict rightMap (x c)
  let ya := Z.restrict leftMap (y a)
  let yc := Z.restrict rightMap (y c)
  have hxa : Z.Agree I xa ya := Z.restrict_agree I leftMap _ _ (hxy a)
  have hxc : Z.Agree I xc yc := Z.restrict_agree I rightMap _ _ (hxy c)
  have hab : Z.Agree I xa xc := overlap_agree B U hU x hx a c
  have hya : Z.Agree I ya yc := hxa.symm.trans (hab.trans hxc)
  apply eq_of_openDifference_eq_zero b F (affineOverlap a c) ya yc hya
  intro j
  have e₁ := openDifference_add b F (affineOverlap a c) xa xc yc hab hxc j
  have e₂ := openDifference_add b F (affineOverlap a c) xa ya yc hxa hya j
  have da := openDifference_restrict b F inf_le_left (hU a) (affineOverlap a c) (x a) (y a) (hxy a) j
  have dc := openDifference_restrict b F inf_le_right (hU c) (affineOverlap a c) (x c) (y c) (hxy c) j
  simp only [y, openDifference_correctOpen] at da dc
  change openDifference b F (affineOverlap a c) xa ya hxa j = _ at da
  change openDifference b F (affineOverlap a c) xc yc hxc j = _ at dc
  have e₃ : openDifference b F (affineOverlap a c) xa xc hab j = _ := hd a c j
  rw [e₃, dc, sub_add_cancel] at e₁
  rw [da, e₁] at e₂
  exact add_left_cancel (e₂.symm.trans (add_zero _).symm)

end Cech

end Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech
