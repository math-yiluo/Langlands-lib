import Langlands.AlgebraicGeometry.Deformation.ElementaryIdealCoefficients
import Langlands.AlgebraicGeometry.AffineChartPoints
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.GroupScheme.HomScheme.GenericReduction

/-! # Coordinate rings on affine opens and their reductions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace IsLocalRing

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections

open SquareZeroAffinePairs SmoothProperConnectedGlobalFunctionsProof
open ElementaryIdealCoefficients
open scoped ElementaryIdealCoefficients

variable {R : Type u} [CommRing R]

local notation "S" => Spec (CommRingCat.of R)

/-- The section ring on an open of a scheme over `Spec R`, with the base map retained. -/
def Sections (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens) : Type u := Γ(Y.left, U)

instance {Y : Over (Spec (CommRingCat.of R))} {U : Y.left.Opens} : CommRing (Sections Y U) :=
  inferInstanceAs (CommRing Γ(Y.left, U))

instance {Y : Over (Spec (CommRingCat.of R))} {U : Y.left.Opens} : Algebra R (Sections Y U) :=
  (secHom Y.hom U).hom.toAlgebra

variable {Y Z W : Over (Spec (CommRingCat.of R))}

/-- Structure map of the spectrum of this ring. -/
abbrev str (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens) : Spec (CommRingCat.of (Sections Y U)) ⟶ S :=
  specMap (algebraMap R (Sections Y U))

lemma fromSpec_hom {U : Y.left.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ Y.hom = str Y U := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hU
    (le_top.trans_eq Y.hom.preimage_top.symm)]
  change _ = Spec.map (secHom Y.hom U)
  rw [secHom, Spec.map_comp, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- An affine open in a smooth scheme has a flat coordinate algebra. -/
lemma flat [Smooth Y.hom] {U : Y.left.Opens} (hU : IsAffineOpen U) :
    Module.Flat R (Sections Y U) := by
  have : Algebra.Smooth R (Sections Y U) := RingHom.smooth_algebraMap.mp (smooth_secHom Y.hom hU)
  infer_instance

/-- Pullback of functions along a morphism mapping the first open into the second. -/
def sectionMap (f : Y ⟶ Z) {U : Z.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) :
    Sections Z U →ₐ[R] Sections Y V :=
  { (f.left.appLE U V h).hom with
    commutes' := fun a ↦ by
      change (secHom Z.hom U ≫ f.left.appLE U V h).hom a = (secHom Y.hom V).hom a
      rw [secHom, Category.assoc, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (Over.w f)]
      rfl }

lemma sectionMap_apply (f : Y ⟶ Z) {U : Z.left.Opens} {V : Y.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (a : Sections Z U) :
    sectionMap f h a = (f.left.appLE U V h).hom a := rfl

@[reassoc]
lemma sectionMap_fromSpec (f : Y ⟶ Z) {U : Z.left.Opens} {V : Y.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    specMap (sectionMap f h).toRingHom ≫ hU.fromSpec = hV.fromSpec ≫ f.left :=
  IsAffineOpen.SpecMap_appLE_fromSpec f.left hU hV h

/-- Restriction of functions along an inclusion of opens. -/
def restrict (Y : Over (Spec (CommRingCat.of R))) {U V : Y.left.Opens} (h : V ≤ U) : Sections Y U →ₐ[R] Sections Y V :=
  { (Y.left.presheaf.map (homOfLE h).op).hom with
    commutes' := fun a ↦ by
      change (secHom Y.hom U ≫ Y.left.presheaf.map (homOfLE h).op).hom a = _
      rw [secHom_map]
      rfl }

@[reassoc]
lemma restrict_fromSpec (Y : Over (Spec (CommRingCat.of R))) {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    specMap (restrict Y h).toRingHom ≫ hU.fromSpec = hV.fromSpec :=
  hU.map_fromSpec hV (homOfLE h).op

variable {L : Ideal R}

local notation "Q" => Spec (CommRingCat.of (R ⧸ L))
local notation "q" => specMap (Ideal.Quotient.mk L)

/-- The section square of the reduction of an affine open is a pushout of rings. -/
lemma isPushout_app {Y₀ : Over Q} {i : Y₀.left ⟶ Y.left}
    (hi : IsPullback i Y₀.hom Y.hom q) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk L)) (secHom Y.hom U)
      (secHom Y₀.hom (i ⁻¹ᵁ U)) (i.app U) := by
  have e : i ⁻¹ᵁ U = i ⁻¹ᵁ U ⊓ Y₀.hom ⁻¹ᵁ ⊤ := by simp
  have hp := (isIso_pushoutSection_iff hi (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top e).mp (isIso_pushoutSection_of_isAffineOpen hi _ _ e
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  refine hp.flip.of_iso' (Scheme.ΓSpecIso (CommRingCat.of R)).symm
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ L))).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.Hom.appLE]
  · simp [secHom]
  · simp [secHom]
  · simp [Scheme.Hom.appLE_eq_app]

private theorem quotientPushout (Y : Over (Spec (CommRingCat.of R))) (U : Y.left.Opens) (L : Ideal R) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk L)) (secHom Y.hom U)
      (CommRingCat.ofHom (algebraMap (R ⧸ L) (Sections Y U ⧸ Extended L (Sections Y U))))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Extended L (Sections Y U)))) := by
  let : Algebra.IsPushout R (Sections Y U) (R ⧸ L) (Sections Y U ⧸ Extended L (Sections Y U)) :=
    Langlands.GroupScheme.HomScheme.quotient_isPushout L (Sections Y U)
  exact (CommRingCat.isPushout_of_isPushout R (Sections Y U) (R ⧸ L)
    (Sections Y U ⧸ Extended L (Sections Y U))).flip

/-- The affine section ring of a scheme-theoretic reduction is the quotient by the
extended ideal. -/
def quotientEquiv {Y₀ : Over Q} {i : Y₀.left ⟶ Y.left}
    (hi : IsPullback i Y₀.hom Y.hom q) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    (Sections Y U ⧸ Extended L (Sections Y U)) ≃+* Γ(Y₀.left, i ⁻¹ᵁ U) :=
  ((quotientPushout Y U L).isoIsPushout _ _ (isPushout_app hi hU)).commRingCatIsoToRingEquiv

@[simp]
lemma quotientEquiv_mk {Y₀ : Over Q} {i : Y₀.left ⟶ Y.left}
    (hi : IsPullback i Y₀.hom Y.hom q) {U : Y.left.Opens} (hU : IsAffineOpen U)
    (a : Sections Y U) : quotientEquiv hi hU (Ideal.Quotient.mk _ a) = (i.app U).hom a := by
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (IsPushout.inr_isoIsPushout_hom _ _ (quotientPushout Y U L) (isPushout_app hi hU))) a

/-- The affine chart of the reduction is the spectrum of the quotient, with its
actual projection to the original chart. -/
@[reassoc]
lemma quotientChart {Y₀ : Over Q} {i : Y₀.left ⟶ Y.left}
    (hi : IsPullback i Y₀.hom Y.hom q) {U : Y.left.Opens} (hU : IsAffineOpen U)
    (hU₀ : IsAffineOpen (i ⁻¹ᵁ U)) :
    specMap (Ideal.Quotient.mk (Extended L (Sections Y U))) ≫ hU.fromSpec =
      specMap (quotientEquiv hi hU).symm.toRingHom ≫ hU₀.fromSpec ≫ i := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec i hU hU₀ le_rfl, Scheme.Hom.appLE_eq_app]
  change specMap (Ideal.Quotient.mk (Extended L (Sections Y U))) ≫ hU.fromSpec =
    specMap (quotientEquiv hi hU).symm.toRingHom ≫ specMap (i.app U).hom ≫ hU.fromSpec
  rw [← specMap_comp_assoc]
  congr 2
  apply RingHom.ext
  intro a
  change Ideal.Quotient.mk _ a = (quotientEquiv hi hU).symm ((i.app U).hom a)
  rw [← quotientEquiv_mk hi hU, RingEquiv.symm_apply_apply]

section Residue

variable [IsLocalRing R] {Yₖ Zₖ : Over (Spec (CommRingCat.of (ResidueField R)))}
  {iY : Yₖ.left ⟶ Y.left} {iZ : Zₖ.left ⟶ Z.left}
  (hY : IsPullback iY Yₖ.hom Y.hom (specMap (residue R)))
  (hZ : IsPullback iZ Zₖ.hom Z.hom (specMap (residue R)))

/-- Affine section comparison for the residue fibre. -/
abbrev residueEquiv {U : Y.left.Opens} (hU : IsAffineOpen U) :
    Fibre (R := R) (Sections Y U) ≃+* Γ(Yₖ.left, iY ⁻¹ᵁ U) :=
  quotientEquiv (L := maximalIdeal R) hY hU

/-- Naturality of the residue section comparison for a map carrying one open into another. -/
theorem residueEquiv_sectionMap (f : Y ⟶ Z) (fₖ : Yₖ ⟶ Zₖ) (hf : iY ≫ f.left = fₖ.left ≫ iZ)
    {U : Z.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (hₖ : iY ⁻¹ᵁ V ≤ fₖ.left ⁻¹ᵁ (iZ ⁻¹ᵁ U)) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (a : Fibre (R := R) (Sections Z U)) :
    residueEquiv hY hV (fibreMap (sectionMap f h) a) =
      (fₖ.left.appLE _ _ hₖ).hom (residueEquiv hZ hU a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change quotientEquiv (L := maximalIdeal R) hY hV
      (Ideal.Quotient.mk _ (sectionMap f h x)) =
    (fₖ.left.appLE _ _ hₖ).hom (quotientEquiv (L := maximalIdeal R) hZ hU (Ideal.Quotient.mk _ x))
  rw [quotientEquiv_mk, quotientEquiv_mk, sectionMap_apply]
  have hcomp : f.left.appLE U V h ≫ iY.app V = iZ.app U ≫ fₖ.left.appLE _ _ hₖ := by
    rw [iY.app_eq_appLE, iZ.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom hf]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcomp) x

/-- Naturality on restrictions of affine opens in one scheme. -/
theorem residueEquiv_restrict {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (a : Fibre (R := R) (Sections Y U)) :
    residueEquiv hY hV (fibreMap (restrict Y h) a) =
    (Yₖ.left.presheaf.map (homOfLE (iY.preimage_mono h)).op).hom (residueEquiv hY hU a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change quotientEquiv (L := maximalIdeal R) hY hV (Ideal.Quotient.mk _ (restrict Y h x)) =
    (Yₖ.left.presheaf.map (homOfLE (iY.preimage_mono h)).op).hom
      (quotientEquiv (L := maximalIdeal R) hY hU (Ideal.Quotient.mk _ x))
  rw [quotientEquiv_mk, quotientEquiv_mk]
  have he := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (iY.naturality (homOfLE h).op)) x
  exact he

end Residue

/-- A presentation of a scheme-theoretic base reduction. -/
structure Reduction (Y : Over (Spec (CommRingCat.of R))) (L : Ideal R) where
  obj : Over (Spec (CommRingCat.of (R ⧸ L)))
  toOriginal : obj.left ⟶ Y.left
  cartesian : IsPullback toOriginal obj.hom Y.hom (specMap (Ideal.Quotient.mk L))

namespace Reduction

/-- The canonical reduction given by base change in the slice category. -/
def pullback (Y : Over (Spec (CommRingCat.of R))) (L : Ideal R) : Reduction Y L where
  obj := (Over.pullback (specMap (Ideal.Quotient.mk L))).obj Y
  toOriginal := pullback.fst Y.hom (specMap (Ideal.Quotient.mk L))
  cartesian := IsPullback.of_hasPullback _ _

variable {A : Reduction Y L} {B : Reduction Z L}

/-- The reduction of a morphism, in the chosen pullback presentations. -/
def map (A : Reduction Y L) (B : Reduction Z L) (f : Y ⟶ Z) : A.obj ⟶ B.obj :=
  Over.homMk (B.cartesian.lift (A.toOriginal ≫ f.left) A.obj.hom (by
    rw [Category.assoc, Over.w, A.cartesian.w])) (B.cartesian.lift_snd _ _ _)

@[reassoc (attr := simp)] lemma map_left_toOriginal (f : Y ⟶ Z) :
    (map A B f).left ≫ B.toOriginal = A.toOriginal ≫ f.left := B.cartesian.lift_fst _ _ _

@[simp] lemma map_id (A : Reduction Y L) : map A A (𝟙 Y) = 𝟙 A.obj := by
  apply Over.OverMorphism.ext
  apply A.cartesian.hom_ext
  · simp
  · exact (Over.w _).trans (Category.id_comp _).symm

lemma map_comp (A : Reduction Y L) (B : Reduction Z L) (C : Reduction W L)
    (f : Y ⟶ Z) (g : Z ⟶ W) : map A C (f ≫ g) = map A B f ≫ map B C g := by
  apply Over.OverMorphism.ext
  apply C.cartesian.hom_ext
  · simp [Category.assoc]
  · simp only [Over.w]

instance (A : Reduction Y L) : IsClosedImmersion A.toOriginal := by
  have : IsClosedImmersion (specMap (Ideal.Quotient.mk L)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.of_isPullback A.cartesian.flip inferInstance

/-- Affine opens remain affine after the quotient base change. -/
lemma affine_preimage (A : Reduction Y L) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (A.toOriginal ⁻¹ᵁ U) := hU.preimage _

/-- A nilpotent quotient covers all points of the original scheme. -/
lemma surjective (A : Reduction Y L) (hL : IsNilpotent L) : Surjective A.toOriginal := by
  let : Surjective (specMap (Ideal.Quotient.mk L)) := ⟨specMap_surjective _
    Ideal.Quotient.mk_surjective (by
      intro x hx
      obtain ⟨n, hn⟩ := hL
      have hm := Ideal.pow_mem_pow ((Ideal.Quotient.eq_zero_iff_mem).mp hx) n
      rw [hn] at hm
      exact ⟨n, Ideal.mem_bot.mp hm⟩)⟩
  exact MorphismProperty.of_isPullback A.cartesian.flip inferInstance

/-- Topological covers of the source give topological covers of its reduction. -/
lemma cover_preimage (A : Reduction Y L) {ι : Type*} (U : ι → Y.left.Opens) (hU : ⊤ ≤ iSup U) :
    ⊤ ≤ ⨆ a, A.toOriginal ⁻¹ᵁ U a := by
  intro z _
  obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hU (Set.mem_univ (A.toOriginal z)))
  exact Opens.mem_iSup.mpr ⟨a, ha⟩

/-- The actual map from the spectrum of the quotient of an affine chart ring. -/
def chart (A : Reduction Y L) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    Spec (CommRingCat.of (Sections Y U ⧸ Extended L (Sections Y U))) ⟶ A.obj.left :=
  specMap (quotientEquiv A.cartesian hU).symm.toRingHom ≫ (A.affine_preimage hU).fromSpec

@[reassoc]
lemma chart_toOriginal (A : Reduction Y L) {U : Y.left.Opens} (hU : IsAffineOpen U) :
    A.chart hU ≫ A.toOriginal = specMap (Ideal.Quotient.mk (Extended L (Sections Y U))) ≫
      hU.fromSpec := by
  rw [chart, Category.assoc, quotientChart A.cartesian hU (A.affine_preimage hU)]

/-- Quotient of an algebra map by the extended ideal on its two tests. -/
def mapQuotient {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    (L : Ideal R) (f : C →ₐ[R] D) : (C ⧸ Extended L C) →+* (D ⧸ Extended L D) :=
  Ideal.quotientMap (Extended L D) f.toRingHom
    (Ideal.map_le_iff_le_comap.mp (map_extended_le L f))

lemma mk_comp_map {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
    (L : Ideal R) (f : C →ₐ[R] D) :
    (Ideal.Quotient.mk (Extended L D)).comp f.toRingHom =
      (mapQuotient L f).comp (Ideal.Quotient.mk (Extended L C)) := rfl

@[reassoc]
lemma chart_map (A : Reduction Y L) (B : Reduction Z L) (f : Y ⟶ Z)
    {U : Z.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    specMap (mapQuotient L (sectionMap f h)) ≫ B.chart hU =
      A.chart hV ≫ (A.map B f).left := by
  apply (cancel_mono B.toOriginal).mp
  rw [Category.assoc, Category.assoc, chart_toOriginal, map_left_toOriginal, chart_toOriginal_assoc,
    ← sectionMap_fromSpec f h hU hV, ← specMap_comp_assoc, ← specMap_comp_assoc, mk_comp_map]

@[reassoc]
lemma chart_restrict (A : Reduction Y L) {U V : Y.left.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    specMap (mapQuotient L (restrict Y h)) ≫ A.chart hU = A.chart hV := by
  apply (cancel_mono A.toOriginal).mp
  rw [Category.assoc, chart_toOriginal, chart_toOriginal, ← restrict_fromSpec Y h hU hV,
    ← specMap_comp_assoc, ← specMap_comp_assoc, mk_comp_map]

end Reduction

end Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
