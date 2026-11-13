import Langlands.AlgebraicGeometry.Picard.DvrLineBundleDivision
import Langlands.AlgebraicGeometry.FactorialAffineComplement
import Langlands.AlgebraicGeometry.Modules.PrincipalGenerationOpenLiftProof
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof

/-! # An affine section meeting the special fibre of an abelian scheme over a DVR -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry

/-- In a noetherian quasi-sober `T₀` space, every point of a closed set has a generization
in that set with no proper generization in the set. -/
theorem exists_maximal_generization {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] [T0Space X] (E : Set X) (hE : IsClosed E) (z : X) (hz : z ∈ E) :
    ∃ g ∈ E, g ⤳ z ∧ ∀ y ∈ E, y ⤳ g → y = g := by
  have : QuasiSober E := hE.isClosedEmbedding_subtypeVal.quasiSober
  have hcl := genericPoints.closure (α := E)
  have hfin := genericPoints.finite (α := E) NoetherianSpace.finite_irreducibleComponents
  have hz' : (⟨z, hz⟩ : E) ∈ closure (genericPoints E) := by
    rw [hcl]
    trivial
  rw [← Set.biUnion_of_singleton (genericPoints E), hfin.closure_biUnion] at hz'
  obtain ⟨g, hg, hgz⟩ := Set.mem_iUnion₂.mp hz'
  refine ⟨g.1, g.2, (specializes_iff_mem_closure.mpr hgz).map continuous_subtype_val, ?_⟩
  intro y hy hyg
  have hyg' : (⟨y, hy⟩ : E) ⤳ g := IsInducing.subtypeVal.specializes_iff.mp hyg
  have hsub : closure {g} ⊆ closure {(⟨y, hy⟩ : E)} :=
    specializes_iff_closure_subset.mp hyg'
  have hsub' : closure {(⟨y, hy⟩ : E)} ⊆ closure {g} :=
    hg.2 isIrreducible_singleton.closure hsub
  have hgy : g ⤳ (⟨y, hy⟩ : E) := specializes_iff_closure_subset.mpr hsub'
  exact congrArg Subtype.val (hyg'.antisymm hgy).eq

open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.ProjectiveBundle

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))

/-- If an affine open `W` meets the special fibre, then every point outside `W` is a
specialization of a generic-fibre point outside `W`. This is where factoriality of the local
rings enters: the complement of `W` has codimension at most one. -/
theorem exists_generic_generization_not_mem
    {W : A.X.left.Opens} (hW : IsAffineOpen W)
    (hWs : ∃ x ∈ W, A.X.hom x = IsLocalRing.closedPoint R)
    {z : A.X.left} (hz : z ∉ W) :
    ∃ g : A.X.left, g ⤳ z ∧ g ∉ W ∧ A.X.hom g ≠ IsLocalRing.closedPoint R := by
  have : IsIntegral A.X.left := isIntegral_total A
  have : A.X.left.IsSeparated := ⟨by rw [← terminal.comp_from A.X.hom]; infer_instance⟩
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsNoetherian A.X.left := {}
  obtain ⟨g, hgE, hgz, hgmax⟩ := exists_maximal_generization ((W : Set A.X.left)ᶜ)
    W.isOpen.isClosed_compl z hz
  refine ⟨g, hgz, hgE, fun hgs ↦ ?_⟩
  obtain ⟨x₁, hx₁W, hx₁s⟩ := hWs
  obtain ⟨ξ, hξs, hξ⟩ := exists_specialGeneric A
  have hξW : ξ ∈ W := (hξ x₁ hx₁s).mem_open W.isOpen hx₁W
  have hξg : ξ ⤳ g := hξ g hgs
  have hξne : ξ ≠ g := fun h ↦ hgE (h ▸ hξW)
  obtain ⟨y₀, hy₀ξ, hy₀s⟩ := exists_generic_generization A ξ hξs
  have hy₀ne : y₀ ≠ ξ := fun h ↦ hy₀s (h ▸ hξs)
  have hgen : ∀ y : A.X.left, y ⤳ g → y ≠ g → y ∈ W := by
    intro y hyg hyne
    by_contra hyW
    exact hyne (hgmax y hyW hyg)
  have := Langlands.AlgebraicGeometry.smoothDVR_factorialStalks R A.X.left A.X.hom g
  exact FactorialAffineComplement.false_of_generization_chain hW hgE hgen hy₀ξ hξg hy₀ne hξne

/-- Generic ampleness yields a global section of a positive power of the total bundle whose
generation open is affine and meets the special fibre. -/
theorem exists_affine_section_meeting_closedFibre (L : LineBundle A.X.left)
    (hη : ((LineBundle.pullback
      (A.X.hom.fiberι (⟨⊥, inferInstance⟩ : PrimeSpectrum R))).obj L).IsAmple) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ τ : L.powSections m, IsAffineOpen (L.sectionOpen τ) ∧
      ∃ x : A.X.left, x ∈ L.sectionOpen τ ∧ A.X.hom x = IsLocalRing.closedPoint R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsIntegral A.X.left := isIntegral_total A
  have := geometricallyIntegral A
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : QuasiSeparatedSpace A.X.left := quasiSeparatedSpace_of_quasiSeparated A.X.hom
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsNoetherian A.X.left := {}
  let c := unifX A π
  let D := A.X.left.basicOpen c
  -- Step B: a global section whose generic part is affine.
  have hA := isAmple_basicOpen A hπ L hη
  obtain ⟨y₀, hy₀⟩ := A.X.hom.surjective (⟨⊥, inferInstance⟩ : PrimeSpectrum R)
  have hy₀D : y₀ ∈ D := by
    rw [mem_basicOpen_unifX_iff A hπ, hy₀]
    exact bot_ne_closedPoint
  obtain ⟨n, hn, s, hys, hsaff⟩ := hA.exists_section ⟨y₀, hy₀D⟩
  obtain ⟨t₀, ht₀⟩ := exists_global_section_of_basicOpen L c s
  let M : LineBundle A.X.left :=
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne A.X.left L n⟩
  have hne : (trivializationOpen M.obj t₀ : Set A.X.left).Nonempty := by
    refine ⟨y₀, ?_⟩
    have h : (⟨y₀, hy₀D⟩ : D.toScheme) ∈ D.ι ⁻¹ᵁ trivializationOpen M.obj t₀ := by
      change _ ∈ D.ι ⁻¹ᵁ trivializationOpen (tensorPow L.obj n) t₀
      rw [ht₀]
      exact hys
    exact h
  -- Step C: divide by the uniformizer as often as possible.
  classical
  let P : ℕ → Prop := fun j ↦ ∃ sj : GlobalSections M.obj, t₀ = c ^ j • sj
  have hP0 : P 0 := ⟨t₀, by rw [pow_zero, one_smul]⟩
  have hex : ∃ j, ¬ P j := by
    by_contra hall
    push Not at hall
    exact not_forall_unifX_pow_smul A hπ M t₀ hne hall
  have hj₁ : ¬ P (Nat.find hex) := Nat.find_spec hex
  have hj₁pos : Nat.find hex ≠ 0 := fun h ↦ hj₁ (h ▸ hP0)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj₁pos
  have hPj : P j := not_not.mp (Nat.find_min hex (show j < Nat.find hex by omega))
  obtain ⟨t, ht⟩ := hPj
  have hspecial : ∃ x₁ ∈ trivializationOpen M.obj t,
      A.X.hom x₁ = IsLocalRing.closedPoint R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t', ht'⟩ := exists_eq_unifX_smul A hπ M t (fun x hx hxt ↦ hcon x hxt hx)
    apply hj₁
    rw [hj]
    exact ⟨t', by rw [ht, ht', smul_smul, pow_succ]⟩
  have htD : D.ι ⁻¹ᵁ trivializationOpen M.obj t = D.ι ⁻¹ᵁ trivializationOpen M.obj t₀ := by
    rw [← lineBundlePullbackSectionOpen A.X.left D.toScheme D.ι M t,
      ← lineBundlePullbackSectionOpen A.X.left D.toScheme D.ι M t₀,
      ← openSection_restriction M.obj D t, ← openSection_restriction M.obj D t₀, ht,
      Scheme.Modules.map_smul, map_pow, openSection_smul, trivializationOpen_smul_unit]
    exact ((A.X.left.toRingedSpace.isUnit_res_basicOpen c).pow j).map D.topIso.inv.hom
  -- Step D: shrink the generation open to an affine open meeting the special fibre.
  obtain ⟨x₁, hx₁t, hx₁s⟩ := hspecial
  let U := trivializationOpen M.obj t
  have hUD : IsAffineOpen (U ⊓ D) := by
    have h1 : D.ι ''ᵁ (D.ι ⁻¹ᵁ U) = U ⊓ D := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    rw [← h1]
    have h2 : IsAffineOpen (D.ι ⁻¹ᵁ U) := by
      change IsAffineOpen (D.ι ⁻¹ᵁ trivializationOpen M.obj t)
      rw [htD]
      change IsAffineOpen (D.ι ⁻¹ᵁ trivializationOpen (tensorPow L.obj n) t₀)
      rw [ht₀]
      exact hsaff
    exact h2.image_of_isOpenImmersion D.ι
  obtain ⟨_, ⟨W, hW, rfl⟩, hx₁W, hWU⟩ :=
    A.X.left.isBasis_affineOpens.exists_subset_of_mem_open hx₁t U.isOpen
  obtain ⟨ξ, hξs, hξ⟩ := exists_specialGeneric A
  have hξW : ξ ∈ W := (hξ x₁ hx₁s).mem_open W.isOpen hx₁W
  obtain ⟨y₁, hy₁ξ, hy₁s⟩ := exists_generic_generization A ξ hξs
  have hy₁W : y₁ ∈ W := hy₁ξ.mem_open W.isOpen hξW
  have hy₁D : y₁ ∈ D := (mem_basicOpen_unifX_iff A hπ y₁).mpr hy₁s
  let V₀ := A.X.left.basicOpen (unifRes A π U)
  have hV₀ : V₀ = U ⊓ D := basicOpen_unifRes A π U
  have hV₀aff : IsAffineOpen V₀ := hV₀ ▸ hUD
  have hy₁V₀ : y₁ ∈ V₀ := by
    rw [hV₀]
    exact ⟨hWU hy₁W, hy₁D⟩
  obtain ⟨r₀, hr₀W, hy₁r₀⟩ := hV₀aff.exists_basicOpen_le (V := W) ⟨y₁, hy₁W⟩ hy₁V₀
  have hUc : IsCompact (U : Set A.X.left) := NoetherianSpace.isCompact _
  have hUq : IsQuasiSeparated (U : Set A.X.left) :=
    isQuasiSeparated_univ.of_subset (Set.subset_univ _)
  have hloc := isLocalization_basicOpen_of_qcqs hUc hUq (unifRes A π U)
  obtain ⟨⟨r₁, _, ⟨k, rfl⟩⟩, hk⟩ :=
    IsLocalization.surj (Submonoid.powers (unifRes A π U)) r₀
  have hWU' : W ≤ U := hWU
  have hWaff : IsAffineOpen W := hW
  simp only at hk
  have hunit : IsUnit (algebraMap Γ(A.X.left, U) Γ(A.X.left, V₀) (unifRes A π U ^ k)) :=
    IsLocalization.map_units Γ(A.X.left, V₀)
      (⟨unifRes A π U ^ k, k, rfl⟩ : Submonoid.powers (unifRes A π U))
  have hr₁V₀ : V₀ ⊓ A.X.left.basicOpen r₁ = A.X.left.basicOpen r₀ := by
    have h1 : A.X.left.basicOpen (algebraMap Γ(A.X.left, U) Γ(A.X.left, V₀) r₁) =
        V₀ ⊓ A.X.left.basicOpen r₁ :=
      Scheme.basicOpen_res A.X.left r₁ (homOfLE (A.X.left.basicOpen_le _)).op
    rw [← h1, ← hk, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hunit,
      inf_of_le_left (A.X.left.basicOpen_le r₀)]
  have hr₁ne : r₁ ≠ 0 := by
    rintro rfl
    have h0 : y₁ ∈ V₀ ⊓ A.X.left.basicOpen (0 : Γ(A.X.left, U)) := by
      rw [hr₁V₀]
      exact hy₁r₀
    rw [Scheme.basicOpen_zero] at h0
    exact h0.2
  let Q : ℕ → Prop := fun j ↦ ∃ rj : Γ(A.X.left, U), r₁ = unifRes A π U ^ j * rj
  have hQ0 : Q 0 := ⟨r₁, by rw [pow_zero, one_mul]⟩
  have hexQ : ∃ j, ¬ Q j := by
    by_contra hall
    push Not at hall
    exact hr₁ne (eq_zero_of_forall_unifRes_pow_dvd A hπ r₁ hx₁t hx₁s hall)
  have hi₁ : ¬ Q (Nat.find hexQ) := Nat.find_spec hexQ
  have hi₁pos : Nat.find hexQ ≠ 0 := fun h ↦ hi₁ (h ▸ hQ0)
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hi₁pos
  have hQi : Q i := not_not.mp (Nat.find_min hexQ (show i < Nat.find hexQ by omega))
  obtain ⟨r, hr⟩ := hQi
  have hspecial' : ∃ x₂ ∈ A.X.left.basicOpen r, A.X.hom x₂ = IsLocalRing.closedPoint R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r', hr'⟩ := exists_eq_unifRes_mul A hπ r (fun x _ hxs hxr ↦ hcon x hxr hxs)
    apply hi₁
    rw [hi]
    exact ⟨r', by rw [hr, hr', ← mul_assoc, pow_succ]⟩
  have hV₀pow : V₀ ≤ A.X.left.basicOpen (unifRes A π U ^ i) := by
    intro x hx
    have hxU : x ∈ U := A.X.left.basicOpen_le _ hx
    rw [Scheme.mem_basicOpen A.X.left _ x hxU] at hx ⊢
    rw [map_pow]
    exact hx.pow i
  have hrV₀ : V₀ ⊓ A.X.left.basicOpen r = A.X.left.basicOpen r₀ := by
    rw [← hr₁V₀, hr, Scheme.basicOpen_mul, ← inf_assoc, inf_of_le_left hV₀pow]
  have hrW : A.X.left.basicOpen r ≤ W := by
    have hgen : ∀ z ∈ A.X.left.basicOpen r, A.X.hom z ≠ IsLocalRing.closedPoint R →
        z ∈ W := by
      intro z hz hzs
      have hzV₀ : z ∈ V₀ := by
        rw [hV₀]
        exact ⟨A.X.left.basicOpen_le r hz, (mem_basicOpen_unifX_iff A hπ z).mpr hzs⟩
      apply hr₀W
      rw [← hrV₀]
      exact ⟨hzV₀, hz⟩
    intro z hz
    by_contra hzW
    by_cases hzs : A.X.hom z = IsLocalRing.closedPoint R
    · obtain ⟨g, hgz, hgW, hgs⟩ :=
        exists_generic_generization_not_mem A hWaff ⟨x₁, hx₁W, hx₁s⟩ hzW
      exact hgW (hgen g (hgz.mem_open (A.X.left.basicOpen r).isOpen hz) hgs)
    · exact hzW (hgen z hz hzs)
  have hraff : IsAffineOpen (A.X.left.basicOpen r) := by
    have h := hWaff.basicOpen (A.X.left.presheaf.map (homOfLE hWU').op r)
    rwa [Scheme.basicOpen_res, inf_of_le_right hrW] at h
  obtain ⟨x₂, hx₂r, hx₂s⟩ := hspecial'
  obtain ⟨N, hN, t', ht'⟩ := principalGenerationOpenLift A.X.left M t r
  let e := tensorPowMulIso L.obj n N
  have hsec : L.sectionOpen (e.hom.app ⊤ t') = A.X.left.basicOpen r := by
    change trivializationOpen (tensorPow L.obj (n * N)) (e.hom.app ⊤ t') = _
    rw [trivializationOpen_mapIso]
    exact ht'
  refine ⟨n * N, by simpa using Nat.mul_le_mul hn hN, e.hom.app ⊤ t', ?_, x₂, ?_, hx₂s⟩
  · rw [hsec]
    exact hraff
  · rw [hsec]
    exact hx₂r

end Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry
