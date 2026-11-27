import Langlands.AlgebraicGeometry.Deformation.ElementaryLiftAxis
import Mathlib.RingTheory.Artinian.Ring

/-! # Normalization and uniqueness of pointed elementary lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts
open AffineOpenQuotientSections
open SmoothProperConnectedGlobalFunctionsProof (secHom secHom_map appLE_congr_hom)
open Picard.FieldTwoAxisH1Injectivity (exists_affineCover surjective_secHom_top)

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {I : Ideal R} {Z : Target R}
variable {Y : Over (Spec (CommRingCat.of R))}

local notation "S" => Spec (CommRingCat.of R)
local notation "K" => IsLocalRing.ResidueField R
local notation "T" => Over.mk (𝟙 S)

local instance : Smooth (T).hom := by
  change Smooth (𝟙 S)
  infer_instance

local instance : IsAffine (T).left := by
  change IsAffine S
  infer_instance

/-- The terminal object reduces to the terminal object over the quotient base. -/
def baseReduction (L : Ideal R) : Reduction T L where
  obj := Over.mk (𝟙 (Spec (CommRingCat.of (R ⧸ L))))
  toOriginal := specMap (Ideal.Quotient.mk L)
  cartesian := IsPullback.of_id_snd

/-- The spectrum of a local Artinian ring has just its closed point. -/
lemma spec_subsingleton [IsArtinianRing R] : Subsingleton S := by
  change Subsingleton (PrimeSpectrum R)
  refine ⟨fun x y ↦ PrimeSpectrum.ext ?_⟩
  exact (eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal)).trans
    (eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)).symm

/-- An open cover of an Artinian family has a chart containing the section. -/
lemma exists_section_chart [IsArtinianRing R] {ι : Type*} {U : ι → Y.left.Opens}
    (hc : ⊤ ≤ iSup U) (s : T ⟶ Y) : ∃ a, ⊤ ≤ s.left ⁻¹ᵁ U a := by
  have : Subsingleton S := spec_subsingleton
  let pt := IsLocalRing.closedPoint R
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hc (Set.mem_univ (s.left pt)))
  refine ⟨a, fun q _ ↦ ?_⟩
  have hq : (q : S) = pt := @Subsingleton.elim S ‹Subsingleton S› q pt
  change s.left q ∈ U a
  exact hq.symm ▸ ha

section Constants

variable {k : Type u} [CommRing k] {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}

private lemma map_constant {U V : Y₁.left.Opens} (h : V ≤ U) (r : k) :
    (Y₁.left.presheaf.map (homOfLE h).op).hom ((secHom Y₁.hom U).hom r) =
      (secHom Y₁.hom V).hom r := by
  rw [← CommRingCat.comp_apply, secHom_map]

private lemma pull_constant (s : Y₂ ⟶ Y₁) {U : Y₁.left.Opens} {V : Y₂.left.Opens}
    (h : V ≤ s.left ⁻¹ᵁ U) (r : k) :
    (s.left.appLE U V h).hom ((secHom Y₁.hom U).hom r) = (secHom Y₂.hom V).hom r :=
  (sectionMap s h).commutes r

private lemma base_secHom_bijective : Function.Bijective
    (secHom (𝟙 (Spec (CommRingCat.of k))) ⊤).hom := by
  have he : secHom (𝟙 (Spec (CommRingCat.of k))) ⊤ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [secHom]
    let Y := Spec (CommRingCat.of k)
    change _ ≫ Scheme.Hom.appLE (𝟙 Y) (⊤ : Y.Opens) ((𝟙 Y) ⁻¹ᵁ ⊤) le_rfl = _
    rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app, Category.comp_id]
  rw [he]
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.bijective

end Constants

private lemma localAgree (B : Reduction Y I) {g g' : Y ⟶ Z.X}
    (h : B.toOriginal ≫ g.left = B.toOriginal ≫ g'.left)
    {U : Y.left.Opens} (hU : IsAffineOpen U) :
    Z.Agree I (localPoint g hU) (localPoint g' hU) :=
  (localPoint_isLift B h hU).trans (localPoint_isLift B rfl hU).symm

private lemma agree_section (B : Reduction Y I) {g g' : Y ⟶ Z.X}
    (h : B.toOriginal ≫ g.left = B.toOriginal ≫ g'.left) (s : T ⟶ Y) :
    (baseReduction I).toOriginal ≫ (s ≫ g).left =
      (baseReduction I).toOriginal ≫ (s ≫ g').left := by
  rw [Over.comp_left, Over.comp_left, ← Reduction.map_left_toOriginal_assoc (B := B) s, h,
    Reduction.map_left_toOriginal_assoc]

section Differences

variable [Fact (maximalIdeal R * I = ⊥)] [Smooth Y.hom] [IsSeparated Y.hom]
  (B : Reduction Y I) (F : Reduction Y (maximalIdeal R)) (b : Z.Coordinates I)
  {g g' : Y ⟶ Z.X} (h : B.toOriginal ≫ g.left = B.toOriginal ≫ g'.left)

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank
local notation "baseF" => baseReduction (maximalIdeal R)

/-- The coordinate of the difference of two global lifts on one affine chart. -/
def globalDifference {U : Y.left.Opens} (hU : IsAffineOpen U) (j : Index) :
    Γ(F.obj.left, F.toOriginal ⁻¹ᵁ U) :=
  openDifference b F hU (localPoint g hU) (localPoint g' hU) (localAgree B h hU) j

omit [IsSeparated Y.hom] in
lemma globalDifference_restrict {U V : Y.left.Opens} (e : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (j : Index) :
    (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono e)).op).hom
      (globalDifference B F b h hU j) = globalDifference B F b h hV j := by
  rw [globalDifference, ← openDifference_restrict b F e hU hV]
  exact openDifference_congr b F hV (restrict_localPoint g e hU hV)
    (restrict_localPoint g' e hU hV) _ _ j

omit [IsSeparated Y.hom] in
lemma globalDifference_sectionMap (s : T ⟶ Y)
    {U : Y.left.Opens} (hU : IsAffineOpen U) (hs : ⊤ ≤ s.left ⁻¹ᵁ U) (j : Index) :
    let hsₖ : (baseF).toOriginal ⁻¹ᵁ (⊤ : (S).Opens) ≤ ((baseF).map F s).left ⁻¹ᵁ (F.toOriginal ⁻¹ᵁ U) :=
      (((baseF).toOriginal.preimage_mono hs).trans_eq (preimage_fibre_map F baseF s U))
    (((baseF).map F s).left.appLE _ _ hsₖ).hom (globalDifference B F b h hU j) =
      globalDifference (baseReduction I) baseF b (agree_section B h s) (isAffineOpen_top _) j := by
  dsimp only
  rw [globalDifference, ← openDifference_sectionMap b F baseF s hs hU (isAffineOpen_top _)]
  exact openDifference_congr b baseF (isAffineOpen_top _) (sectionMap_localPoint s g hs hU _)
    (sectionMap_localPoint s g' hs hU _) _ _ j

include h b in
/-- When global functions on the residue fibre come from the field, two lifts agreeing at
one section coincide. -/
theorem eq_of_eq_at_section [IsArtinianRing R] [QuasiCompact Y.hom]
    (hF : Function.Surjective (secHom F.obj.hom ⊤).hom)
    (s : T ⟶ Y) (hs : s ≫ g = s ≫ g') : g = g' := by
  obtain ⟨ι, _, U, hU, hUU, hc⟩ := exists_affineCover Y.hom
  obtain ⟨a₀, h₀⟩ := exists_section_chart hc s
  have e (j : Index) : ∃ r : K, ∀ a,
      globalDifference B F b h (hU a) j = (secHom F.obj.hom (F.toOriginal ⁻¹ᵁ U a)).hom r := by
    let V (a : ι) := F.toOriginal ⁻¹ᵁ U a
    let x (a : ι) := globalDifference B F b h (hU a) j
    have hx : TopCat.Presheaf.IsCompatible F.obj.left.sheaf.1 V x := by
      intro a d
      exact (globalDifference_restrict B F b h inf_le_left (hU a) (hUU a d) j).trans
        (globalDifference_restrict B F b h inf_le_right (hU d) (hUU a d) j).symm
    obtain ⟨z, hz, -⟩ := F.obj.left.sheaf.existsUnique_gluing' V ⊤ (fun _ ↦ homOfLE le_top)
      (F.cover_preimage U hc) x hx
    obtain ⟨r, hr⟩ := hF z
    refine ⟨r, fun a ↦ ?_⟩
    change x a = (secHom F.obj.hom (V a)).hom r
    rw [← hz a, ← hr]
    exact map_constant le_top r
  apply Over.OverMorphism.ext
  apply hom_ext_fromSpec U hU hc
  intro a
  have he : localPoint g (hU a) = localPoint g' (hU a) := by
    apply eq_of_openDifference_eq_zero b F (hU a) _ _ (localAgree B h (hU a))
    intro j
    obtain ⟨r, hr⟩ := e j
    have hh := globalDifference_sectionMap B F b h s (hU a₀) h₀ j
    change (((baseF).map F s).left.appLE _ ⊤ _).hom
      (globalDifference B F b h (hU a₀) j) = _ at hh
    rw [hr a₀, pull_constant] at hh
    have hz : (secHom ((baseF).obj.hom) ⊤).hom r = 0 := hh.trans
      ((openDifference_congr b baseF (isAffineOpen_top _) rfl
        (congrArg (fun f ↦ localPoint f (isAffineOpen_top _)) hs.symm) _ rfl j).trans
        (openDifference_same b baseF _ _ j))
    have hr₀ : r = 0 := base_secHom_bijective.1 (hz.trans (map_zero _).symm)
    change globalDifference B F b h (hU a) j = 0
    rw [hr a, hr₀, map_zero]
  exact congrArg (fun f ↦ f.left) he

end Differences

section Normalize

variable [Fact (maximalIdeal R * I = ⊥)] [IsArtinianRing R] [Smooth Y.hom] [IsProper Y.hom]
  (B : Reduction Y I) (F : Reduction Y (maximalIdeal R)) (b : Z.Coordinates I)

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank
local notation "baseF" => baseReduction (maximalIdeal R)

include F b in
/-- A global lift can be adjusted to take a prescribed value at a section when that value
agrees with the reduction. -/
theorem exists_lift_with_value (g : Y ⟶ Z.X) (s : T ⟶ Y) (v : T ⟶ Z.X)
    (hv : (baseReduction I).toOriginal ≫ (s ≫ g).left = (baseReduction I).toOriginal ≫ v.left) :
    ∃ h : Y ⟶ Z.X, B.toOriginal ≫ h.left = B.toOriginal ≫ g.left ∧ s ≫ h = v := by
  classical
  obtain ⟨ι, _, U, hU, hUU, hc⟩ := exists_affineCover Y.hom
  obtain ⟨a₀, h₀⟩ := exists_section_chart hc s
  let x (a : ι) := localPoint g (hU a)
  have hx (a : ι) : IsLocalLift (g₀ := B.toOriginal ≫ g.left) B (hU a) (x a) :=
    localPoint_isLift B rfl (hU a)
  let t (j : Index) := openDifference b baseF (isAffineOpen_top _)
    (localPoint (s ≫ g) (isAffineOpen_top _)) (localPoint v (isAffineOpen_top _))
    (localAgree (baseReduction I) hv (isAffineOpen_top _)) j
  let r (j : Index) : K := Classical.choose (base_secHom_bijective.2 (t j))
  have hr (j : Index) : (secHom (baseF).obj.hom ⊤).hom (r j) = t j :=
    Classical.choose_spec (base_secHom_bijective.2 (t j))
  let d (a : ι) (j : Index) := (secHom F.obj.hom (F.toOriginal ⁻¹ᵁ U a)).hom (r j)
  have hd (a c : ι) (j : Index) : cocycle B b F U hU x hx a c j =
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (show U a ⊓ U c ≤ U a from inf_le_left))).op).hom (d a j) -
      (F.obj.left.presheaf.map (homOfLE (F.toOriginal.preimage_mono
        (show U a ⊓ U c ≤ U c from inf_le_right))).op).hom (d c j) := by
    change _ = (F.obj.left.presheaf.map _).hom ((secHom F.obj.hom (F.toOriginal ⁻¹ᵁ U a)).hom (r j)) -
      (F.obj.left.presheaf.map _).hom ((secHom F.obj.hom (F.toOriginal ⁻¹ᵁ U c)).hom (r j))
    rw [map_constant, map_constant, sub_self]
    change openDifference b F (hUU a c) (Z.restrict (restrict Y inf_le_left) (x a))
      (Z.restrict (restrict Y inf_le_right) (x c)) _ j = 0
    exact (openDifference_congr b F _ (restrict_localPoint g inf_le_left (hU a) (hUU a c))
      (restrict_localPoint g inf_le_right (hU c) (hUU a c)) _ rfl j).trans
      (openDifference_same b F _ (localPoint g (hUU a c)) j)
  obtain ⟨h, hh, hlocal⟩ := exists_lift_of_coboundary B b F U hU x hx hc d hd
  refine ⟨h, hh, ?_⟩
  have hs : (baseReduction I).toOriginal ≫ (s ≫ g).left =
      (baseReduction I).toOriginal ≫ (s ≫ h).left := agree_section B hh.symm s
  apply Over.OverMorphism.ext
  have : IsIso (isAffineOpen_top S).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  apply (cancel_epi ((isAffineOpen_top S).fromSpec)).mp
  suffices heq : localPoint (s ≫ h) (isAffineOpen_top S) = localPoint v (isAffineOpen_top S) by
    exact congrArg (fun f : Z.Points (Sections T ⊤) ↦ f.left) heq
  have hag : Z.Agree I (localPoint (s ≫ g) (isAffineOpen_top S))
      (localPoint (s ≫ h) (isAffineOpen_top S)) := localAgree (baseReduction I) hs _
  have hav : Z.Agree I (localPoint (s ≫ g) (isAffineOpen_top S))
      (localPoint v (isAffineOpen_top S)) := localAgree (baseReduction I) hv _
  apply eq_of_openDifference_eq_zero b baseF (isAffineOpen_top S) _ _ (hag.symm.trans hav)
  intro j
  have hdg := globalDifference_sectionMap B F b hh.symm s (hU a₀) h₀ j
  have hconstant : globalDifference B F b hh.symm (hU a₀) j = d a₀ j := by
    exact (openDifference_congr b F _ rfl (hlocal a₀) _ (correctOpen_agree b F _ _ _) j).trans
      (openDifference_correctOpen b F _ _ _ j)
  change (((baseF).map F s).left.appLE _ ⊤ _).hom
      (globalDifference B F b hh.symm (hU a₀) j) = _ at hdg
  rw [hconstant] at hdg
  change (((baseF).map F s).left.appLE _ ⊤ _).hom
    ((secHom F.obj.hom (F.toOriginal ⁻¹ᵁ U a₀)).hom (r j)) = _ at hdg
  rw [pull_constant, hr] at hdg
  have he := openDifference_add b baseF (isAffineOpen_top S) _ _ _ hag (hag.symm.trans hav) j
  change t j = globalDifference (baseReduction I) baseF b hs (isAffineOpen_top S) j + _ at he
  rw [← hdg] at he
  exact add_left_cancel (he.symm.trans (add_zero _).symm)

end Normalize

end Langlands.AlgebraicGeometry.Deformation.ElementaryLiftCech
