import Langlands.AlgebraicGeometry.AffinizationBasicOpen
import Langlands.AlgebraicGeometry.SmoothDvrGlobalSections
import Langlands.AlgebraicGeometry.Picard.DvrAbelianAffineSection
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain

/-! # The principal-open argument for smooth schemes over a DVR -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.SmoothDvrPrincipalOpen

open SmoothDvrGlobalSections

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (Y : Over (Spec (CommRingCat.of R)))

/-- Every special-fibre point of a flat scheme over a DVR has a generic-fibre generization. -/
theorem exists_generic_generization [Flat Y.hom] (x : Y.left)
    (hx : Y.hom x = IsLocalRing.closedPoint R) :
    ∃ y : Y.left, y ⤳ x ∧ Y.hom y ≠ IsLocalRing.closedPoint R := by
  have hspec : ((⟨⊥, inferInstance⟩ : PrimeSpectrum R) : Spec (CommRingCat.of R)) ⤳
      Y.hom x := by
    rw [hx]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hyx, hy⟩ := Flat.generalizingMap Y.hom hspec
  refine ⟨y, hyx, ?_⟩
  rw [hy]
  intro heq
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal heq).symm

/-- A fibre-dense affine open in a smooth separated DVR scheme has no purely vertical
component in its complement, expressed by generic-fibre generizations of complement points. -/
theorem exists_generic_generization_not_mem [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {W : Y.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : Y.left, Y.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, Y.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x)
    {z : Y.left} (hz : z ∉ W) :
    ∃ g : Y.left, g ⤳ z ∧ g ∉ W ∧ Y.hom g ≠ IsLocalRing.closedPoint R := by
  have : Y.left.IsSeparated := ⟨by rw [← terminal.comp_from Y.hom]; infer_instance⟩
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Y.left := {}
  obtain ⟨g, hgE, hgz, hgmax⟩ :=
    Picard.DvrAbelianGeometry.exists_maximal_generization ((W : Set Y.left)ᶜ)
      W.isOpen.isClosed_compl z hz
  refine ⟨g, hgz, hgE, fun hgs ↦ ?_⟩
  obtain ⟨ξ, hξW, hξs, hξg⟩ := hdense g hgs
  have hξne : ξ ≠ g := fun h ↦ hgE (h ▸ hξW)
  obtain ⟨y₀, hy₀ξ, hy₀s⟩ := exists_generic_generization Y ξ hξs
  have hy₀ne : y₀ ≠ ξ := fun h ↦ hy₀s (h ▸ hξs)
  have hgen : ∀ y : Y.left, y ⤳ g → y ≠ g → y ∈ W := by
    intro y hyg hyne
    by_contra hyW
    exact hyne (hgmax y hyW hyg)
  have : IsRegularLocalRing (Y.left.presheaf.stalk g) :=
    Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R Y.hom g
  have := IsRegularLocalRing.isDomain (Y.left.presheaf.stalk g)
  have := smoothDVR_factorialStalks R Y.left Y.hom g
  exact FactorialAffineComplement.false_of_generization_chain hW hgE hgen
    hy₀ξ hξg hy₀ne hξne

/-- Nonvanishing at a generization of a special point bounds the uniformizer divisibility
of a global function. No integrality of the total scheme is needed. -/
theorem not_forall_scalar_pow_dvd [Smooth Y.hom] {π : R} (hπ : Irreducible π)
    (f : Γ(Y.left, ⊤)) {x y : Y.left} (hxs : Y.hom x = IsLocalRing.closedPoint R)
    (hyx : y ⤳ x) (hyf : y ∈ Y.left.basicOpen f) :
    ¬ ∀ j : ℕ, ∃ fj : Γ(Y.left, ⊤), f = scalar Y π ^ j * fj := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let germ := Y.left.presheaf.germ ⊤ x trivial
  let c := germ (scalar Y π)
  have hgf : germ f ≠ 0 := by
    intro hzero
    have hmap : (Y.left.presheaf.stalkSpecializes hyx) (germ f) =
        Y.left.presheaf.germ ⊤ y trivial f :=
      congrArg (fun k : Γ(Y.left, ⊤) ⟶ Y.left.presheaf.stalk y => k f)
        (TopCat.Presheaf.germ_stalkSpecializes Y.left.presheaf
          (U := ⊤) (y := x) (x := y) trivial hyx)
    rw [hzero, map_zero] at hmap
    have hunit := (Scheme.mem_basicOpen Y.left f y trivial).mp hyf
    rw [← hmap] at hunit
    exact not_isUnit_zero hunit
  have hc : c ∈ IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_basicOpen_scalar_iff Y hπ x).mp
      ((Scheme.mem_basicOpen Y.left (scalar Y π) x trivial).mpr hu) hxs
  have hI : Ideal.span {c} ≠ ⊤ := by
    intro htop
    have hle : Ideal.span {c} ≤ IsLocalRing.maximalIdeal _ :=
      (Ideal.span_singleton_le_iff_mem _).mpr hc
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
  intro hdiv
  have hmem : germ f ∈ ⨅ i : ℕ, (Ideal.span {c}) ^ i := by
    rw [Ideal.mem_iInf]
    intro i
    obtain ⟨fi, hfi⟩ := hdiv i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfi, map_mul, map_pow]
    exact dvd_mul_right _ _
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI, Ideal.mem_bot] at hmem
  exact hgf hmem

/-- The principal-open existence argument from a supplied affine uniformizer open and
an affine open dense in the special fibre. -/
theorem exists_affine_basicOpen_meeting_closedFibre [Smooth Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] {π : R} (hπ : Irreducible π)
    (hD : IsAffineOpen (Y.left.basicOpen (scalar Y π)))
    {W : Y.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : Y.left, Y.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, Y.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x)
    (hs : ∃ x : Y.left, Y.hom x = IsLocalRing.closedPoint R) :
    ∃ f : Γ(Y.left, ⊤), IsAffineOpen (Y.left.basicOpen f) ∧
      ∃ x ∈ Y.left.basicOpen f, Y.hom x = IsLocalRing.closedPoint R := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let c := scalar Y π
  let D := Y.left.basicOpen c
  obtain ⟨x, hxs⟩ := hs
  obtain ⟨ξ, hξW, hξs, -⟩ := hdense x hxs
  obtain ⟨y, hyξ, hys⟩ := exists_generic_generization Y ξ hξs
  have hyW : y ∈ W := hyξ.mem_open W.isOpen hξW
  have hyD : y ∈ D := (mem_basicOpen_scalar_iff Y hπ y).mpr hys
  obtain ⟨r₀, hr₀W, hyr₀⟩ := hD.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hyD
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ c
  obtain ⟨⟨r₁, _, ⟨k, rfl⟩⟩, hk⟩ := IsLocalization.surj (Submonoid.powers c) r₀
  simp only at hk
  have hunit : IsUnit (algebraMap Γ(Y.left, ⊤) Γ(Y.left, D) (c ^ k)) :=
    IsLocalization.map_units Γ(Y.left, D) (⟨c ^ k, k, rfl⟩ : Submonoid.powers c)
  have hr₁D : D ⊓ Y.left.basicOpen r₁ = Y.left.basicOpen r₀ := by
    have hres : Y.left.basicOpen (algebraMap Γ(Y.left, ⊤) Γ(Y.left, D) r₁) =
        D ⊓ Y.left.basicOpen r₁ :=
      Scheme.basicOpen_res Y.left r₁ (homOfLE (Y.left.basicOpen_le c)).op
    rw [← hres, ← hk, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hunit,
      inf_of_le_left (Y.left.basicOpen_le r₀)]
  have hyr₁ : y ∈ Y.left.basicOpen r₁ := by
    have hy : y ∈ D ⊓ Y.left.basicOpen r₁ := by rwa [hr₁D]
    exact hy.2
  classical
  let Q : ℕ → Prop := fun j ↦ ∃ rj : Γ(Y.left, ⊤), r₁ = c ^ j * rj
  have hQ0 : Q 0 := ⟨r₁, by rw [pow_zero, one_mul]⟩
  have hexQ : ∃ j, ¬ Q j := by
    by_contra hall
    push Not at hall
    exact not_forall_scalar_pow_dvd Y hπ r₁ hξs hyξ hyr₁ hall
  have hi₁ : ¬ Q (Nat.find hexQ) := Nat.find_spec hexQ
  have hi₁pos : Nat.find hexQ ≠ 0 := fun h ↦ hi₁ (h ▸ hQ0)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hi₁pos
  have hQi : Q i := not_not.mp (Nat.find_min hexQ (show i < Nat.find hexQ by omega))
  obtain ⟨r, hr⟩ := hQi
  have hspecial : ∃ z ∈ Y.left.basicOpen r,
      Y.hom z = IsLocalRing.closedPoint R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r', hr'⟩ := exists_eq_scalar_mul_of_vanishing Y hπ r
      (fun z hzs hzr ↦ hcon z hzr hzs)
    apply hi₁
    rw [hi]
    exact ⟨r', by rw [hr, hr', ← mul_assoc, pow_succ]⟩
  have hDpow : D ≤ Y.left.basicOpen (c ^ i) := by
    intro z hz
    have hu := (Scheme.mem_basicOpen Y.left c z trivial).mp hz
    apply (Scheme.mem_basicOpen Y.left (c ^ i) z trivial).mpr
    rw [map_pow]
    exact hu.pow i
  have hrD : D ⊓ Y.left.basicOpen r = Y.left.basicOpen r₀ := by
    rw [← hr₁D, hr, Scheme.basicOpen_mul, ← inf_assoc, inf_of_le_left hDpow]
  have hrW : Y.left.basicOpen r ≤ W := by
    have hgen : ∀ z ∈ Y.left.basicOpen r, Y.hom z ≠ IsLocalRing.closedPoint R →
        z ∈ W := by
      intro z hz hzs
      apply hr₀W
      rw [← hrD]
      exact ⟨(mem_basicOpen_scalar_iff Y hπ z).mpr hzs, hz⟩
    intro z hz
    by_contra hzW
    obtain ⟨g, hgz, hgW, hgs⟩ := exists_generic_generization_not_mem Y hW hdense hzW
    exact hgW (hgen g (hgz.mem_open (Y.left.basicOpen r).isOpen hz) hgs)
  have hraff : IsAffineOpen (Y.left.basicOpen r) := by
    have h := hW.basicOpen (Y.left.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op r)
    rwa [Scheme.basicOpen_res, inf_of_le_right hrW] at h
  exact ⟨r, hraff, hspecial⟩

/-- The basic open of a uniformizer is affine when the actual pullback to a specified
fraction field is affine. -/
theorem isAffineOpen_scalar_of_genericAffine (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    [IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))] :
    IsAffineOpen (Y.left.basicOpen (scalar Y π)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have := isLocalizationAway_fractionRing_of_dvr R K hπ
  have : IsOpenImmersion b := IsOpenImmersion.of_isLocalization π
  have hb : b.opensRange = PrimeSpectrum.basicOpen π :=
    Opens.ext (PrimeSpectrum.localization_away_comap_range K π)
  rw [scalar, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine,
    ← hb, ← Scheme.Hom.opensRange_pullbackFst]
  exact isAffineOpen_opensRange (pullback.fst Y.hom b)

/-- The BLR principal-open construction, given a fibre-dense affine open. The chosen
function has affine nonvanishing locus meeting the special fibre, and the canonical
affinization map restricts there to an isomorphism. -/
def affinePrincipalOpenMeetingClosedFibre (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] [Smooth Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [IsAffine (pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    {W : Y.left.Opens} (hW : IsAffineOpen W)
    (hdense : ∀ x : Y.left, Y.hom x = IsLocalRing.closedPoint R →
      ∃ y ∈ W, Y.hom y = IsLocalRing.closedPoint R ∧ y ⤳ x)
    (hs : ∃ x : Y.left, Y.hom x = IsLocalRing.closedPoint R) :
    { f : Γ(Y.left, ⊤) // IsAffineOpen (Y.left.basicOpen f) ∧
      IsIso (Y.left.toSpecΓ ∣_ PrimeSpectrum.basicOpen f) ∧
      ∃ x ∈ Y.left.basicOpen f, Y.hom x = IsLocalRing.closedPoint R } := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let π := Classical.choose (IsDiscreteValuationRing.exists_irreducible R)
  have hπ : Irreducible π := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible R)
  have hD := isAffineOpen_scalar_of_genericAffine Y K hπ
  let H := exists_affine_basicOpen_meeting_closedFibre Y hπ hD hW hdense hs
  refine ⟨Classical.choose H, (Classical.choose_spec H).1, ?_, (Classical.choose_spec H).2⟩
  exact isIso_toSpecΓ_restrict_basicOpen Y.left _ (Classical.choose_spec H).1

end Langlands.AlgebraicGeometry.SmoothDvrPrincipalOpen
