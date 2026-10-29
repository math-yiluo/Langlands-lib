import Langlands.Representation.Derivative.MirabolicMinus
import Langlands.Representation.Derivative.MirabolicLatticeBox
import Langlands.Representation.Jacquet.CharacterAveraging
import Langlands.Group.GL.Padic

/-!
# A smooth mirabolic representation with vanishing `Ψ⁻` and `Φ⁻` is zero

BZ77 §3.2 and §3.5: if both the trivial-character localization and the
`θ_ψ`-localization of a smooth representation `X` of `P_(m+2)` by its abelian
radical `V ≅ F^(m+1)` vanish, then `X = 0`. Every nontrivial character
`u(c) ↦ ψ(a ⬝ c)` of the radical is a Levi conjugate of `θ_ψ`, so every vector lies
in the relations of every character. Averages over growing radical boxes then kill a
fixed vector against all characters of a compact dual box, and a finite Fourier
inversion over the dual box recovers the vector. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Topology
open scoped Matrix

universe uF uV

/-! ## Averages over nested compact open subgroups -/

section Averaging

open Jacquet.Localization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} {N : Subgroup G}

/-- A twisted average vanishing over a compact open subgroup vanishes over every
larger compact open subgroup. -/
theorem characterAverage_eq_zero_of_le (hρ : IsSmooth ρ) {χ : N →* ℂˣ}
    (hχ : IsOpen (χ.ker : Set N)) {H H' : OpenSubgroup N} (hH : IsCompact (H : Set N))
    (hH' : IsCompact (H' : Set N)) (hle : H ≤ H') {v : V}
    (hv : characterAverage hρ hχ H hH v = 0) : characterAverage hρ hχ H' hH' v = 0 := by
  let := finite_orbit_twistedRestriction hρ hχ H hH v
  have hsub : v - characterAverage hρ hχ H hH v ∈
      LinearMap.ker (characterAverage hρ hχ H' hH') := by
    rw [characterAverage_eq_orbitMean hρ hχ H hH v]
    refine sub_orbitMean_mem _ v _ fun h => ?_
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    change characterAverage hρ hχ H' hH' v =
      characterAverage hρ hχ H' hH' (twistedRestriction ρ N χ (h : N) v)
    rw [characterAverage_eq_orbitMean, characterAverage_eq_orbitMean]
    exact (Compact.orbitMean_apply ((twistedRestriction ρ N χ).comp H'.toSubgroup.subtype)
      ⟨(h : N), hle h.property⟩ v).symm
  rw [hv, sub_zero] at hsub
  exact hsub

/-- The twisted average over `H` depends only on the character restricted to `H`. -/
theorem characterAverage_congr (hρ : IsSmooth ρ) {χ χ' : N →* ℂˣ}
    (hχ : IsOpen (χ.ker : Set N)) (hχ' : IsOpen (χ'.ker : Set N)) (H : OpenSubgroup N)
    (hH : IsCompact (H : Set N)) (h : ∀ n ∈ H, χ n = χ' n) (v : V) :
    characterAverage hρ hχ H hH v = characterAverage hρ hχ' H hH v := by
  have hπ : (twistedRestriction ρ N χ).comp H.toSubgroup.subtype =
      (twistedRestriction ρ N χ').comp H.toSubgroup.subtype := by
    ext n w
    change twistedRestriction ρ N χ (n : N) w = twistedRestriction ρ N χ' (n : N) w
    rw [twistedRestriction_apply, twistedRestriction_apply, h _ n.property]
  rw [characterAverage_eq_orbitMean, characterAverage_eq_orbitMean, hπ]

end Averaging

/-! ## Invertible matrices with a prescribed last row -/

/-- Every nonzero row is the last row of an invertible matrix. -/
theorem exists_lastRow_eq_of_ne_zero {K : Type*} [Field K] {m : ℕ} (x : Fin (m + 1) → K)
    (hx : x ≠ 0) : ∃ g : GeneralLinear (m + 1) K, (fun j => g.val (Fin.last m) j) = x := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    exact hx (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  let τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K).updateRow j x).submatrix τ id
  have hsum : (∑ k, x k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) k) = x := by
    funext i
    simp [Matrix.one_apply]
  have hdet : M.det ≠ 0 := by
    have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) j x
    rw [hsum, Matrix.det_one, smul_eq_mul, mul_one] at h1
    simp only [M, Matrix.det_permute, h1]
    refine mul_ne_zero ?_ hj
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr (Ne.isUnit hdet)).unit, ?_⟩
  funext k
  change M (Fin.last m) k = x k
  simp [M, τ, Equiv.swap_apply_right]

/-! ## Radical boxes and coordinate characters -/

section Coordinates

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Every coordinate vector lies in some lattice box. -/
theorem exists_mem_latticeBox {k : ℕ} (c : Fin k → F.Carrier) :
    ∃ M : ℤ, c ∈ latticeBox T k M := by
  have h : ∀ j, ∃ M : ℤ, c j ∈ T.additiveLattice M := fun j => by
    by_cases hx : c j = 0
    · exact ⟨0, hx ▸ (T.additiveLattice 0).zero_mem⟩
    · refine ⟨WithZero.log (T.discreteValuation (c j)), ?_⟩
      rw [PadicField.TopologicalData.mem_additiveLattice,
        WithZero.exp_log ((T.discreteValuation.ne_zero_iff).mpr hx)]
  choose M hM using h
  refine ⟨∑ j, |M j|, (mem_latticeBox T).mpr fun j => T.additiveLattice_mono ?_ (hM j)⟩
  exact (le_abs_self (M j)).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) (Finset.mem_univ j))

/-- The compact open subgroup of radical elements with coordinates in the box
`(π^(-M) O)^(m+1)`. -/
def radicalBox (m : ℕ) (M : ℤ) :
    letI := T.topology
    OpenSubgroup (radical (m + 1) F.Carrier) := by
  letI := T.topology
  exact
    { toSubgroup := (AddSubgroup.toSubgroup (latticeBox T (m + 1) M)).comap
        (radicalEquiv (n := m + 1) (F := F.Carrier)).toMonoidHom
      isOpen' := (isOpen_latticeBox T (m + 1) M).preimage continuous_radicalCoordinates }

theorem mem_radicalBox {m : ℕ} {M : ℤ} {u : radical (m + 1) F.Carrier} :
    u ∈ radicalBox T m M ↔ radicalCoordinates u ∈ latticeBox T (m + 1) M :=
  Iff.rfl

theorem radicalBox_mono (m : ℕ) {M M' : ℤ} (h : M ≤ M') :
    radicalBox T m M ≤ radicalBox T m M' := fun _ hu =>
  (mem_radicalBox T).mpr (latticeBox_mono T h ((mem_radicalBox T).mp hu))

theorem isCompact_radicalBox (m : ℕ) (M : ℤ) :
    letI := T.topology
    IsCompact (radicalBox T m M : Set (radical (m + 1) F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have h : (radicalBox T m M : Set (radical (m + 1) F.Carrier)) =
      radicalElement '' (latticeBox T (m + 1) M : Set (Fin (m + 1) → F.Carrier)) := by
    ext u
    constructor
    · intro hu
      exact ⟨radicalCoordinates u, hu, radicalElement_coordinates u⟩
    · rintro ⟨c, hc, rfl⟩
      change radicalCoordinates (radicalElement c) ∈ latticeBox T (m + 1) M
      rw [radicalCoordinates_element]
      exact hc
  rw [h]
  exact (isCompact_latticeBox T (m + 1) M).image continuous_radicalElement

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The character `u(c) ↦ ψ(a ⬝ c)` of the radical `V_(m+2) ≅ F^(m+1)`. -/
def coordinateCharacter (m : ℕ) (a : Fin (m + 1) → F.Carrier) :
    radical (m + 1) F.Carrier →* ℂˣ := by
  letI := T.topology
  exact Circle.toUnits.comp (ψ.toAddChar.toMonoidHom.comp
    ((AddMonoidHom.mk' (fun c : Fin (m + 1) → F.Carrier => a ⬝ᵥ c)
      (fun c d => dotProduct_add a c d)).toMultiplicative.comp radicalEquiv.toMonoidHom))

theorem coordinateCharacter_apply (m : ℕ) (a : Fin (m + 1) → F.Carrier)
    (u : radical (m + 1) F.Carrier) :
    letI := T.topology
    (coordinateCharacter T ψ m a u : ℂ) = ψ.complex (a ⬝ᵥ radicalCoordinates u) :=
  rfl

theorem coordinateCharacter_zero (m : ℕ) : coordinateCharacter T ψ m 0 = 1 := by
  ext u
  rw [coordinateCharacter_apply, zero_dotProduct, AddChar.map_zero_eq_one, MonoidHom.one_apply]
  rfl

/-- `ψ(a ⬝ c) = 1` for `a` in the dual box of level `n(ψ) - M` and `c` in the box of
level `M`. -/
theorem coordinateCharacter_eq_one (m : ℕ) {M : ℤ} {a : Fin (m + 1) → F.Carrier}
    (ha : a ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M))
    (u : radical (m + 1) F.Carrier) (hu : radicalCoordinates u ∈ latticeBox T (m + 1) M) :
    coordinateCharacter T ψ m a u = 1 := by
  let := T.topology
  apply Units.ext
  rw [coordinateCharacter_apply, Units.val_one, UnitaryAdditiveCharacter.complex_apply,
    character_dotProduct_eq_one T ψ ha hu, Circle.coe_one]

/-- Characters whose parameters differ by an element of the dual box agree on the box. -/
theorem coordinateCharacter_eq_of_sub_mem (m : ℕ) {M : ℤ} {a a' : Fin (m + 1) → F.Carrier}
    (ha : a' - a ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M))
    (u : radical (m + 1) F.Carrier) (hu : radicalCoordinates u ∈ latticeBox T (m + 1) M) :
    coordinateCharacter T ψ m a' u = coordinateCharacter T ψ m a u := by
  have h1 := coordinateCharacter_eq_one T ψ m ha u hu
  apply Units.ext
  have h1' := congrArg (fun z : ℂˣ => (z : ℂ)) h1
  simp only [coordinateCharacter_apply, Units.val_one] at h1' ⊢
  rw [show a' = (a' - a) + a by abel, add_dotProduct, AddChar.map_add_eq_mul, h1', one_mul]

theorem isOpen_ker_coordinateCharacter (m : ℕ) (a : Fin (m + 1) → F.Carrier) :
    letI := T.topology
    IsOpen ((coordinateCharacter T ψ m a).ker : Set (radical (m + 1) F.Carrier)) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  obtain ⟨M, hM⟩ := exists_mem_latticeBox T a
  have hle : (radicalBox T m (T.additiveConductor ψ - M)).toSubgroup ≤
      (coordinateCharacter T ψ m a).ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    refine coordinateCharacter_eq_one T ψ m ?_ u hu
    rw [sub_sub_cancel]
    exact hM
  exact Subgroup.isOpen_mono hle (radicalBox T m _).isOpen

/-- Conjugating by `levi g⁻¹` carries the `θ_ψ`-relations into the relations of the
coordinate character given by the last row of `g`. -/
theorem levi_inv_mem_relations (m : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (g : GeneralLinear (m + 1) F.Carrier) {v : V} :
    letI := T.topology
    v ∈ Jacquet.Localization.relations ρ (radical (m + 1) F.Carrier)
      (T.mirabolicTheta ψ m) →
    ρ (levi g⁻¹) v ∈ Jacquet.Localization.relations ρ (radical (m + 1) F.Carrier)
      (coordinateCharacter T ψ m (fun j => g.val (Fin.last m) j)) := by
  let := T.topology
  intro hv
  set χ := coordinateCharacter T ψ m (fun j => g.val (Fin.last m) j)
  have hspan : Jacquet.Localization.relations ρ (radical (m + 1) F.Carrier)
      (T.mirabolicTheta ψ m) ≤
      (Jacquet.Localization.relations ρ (radical (m + 1) F.Carrier) χ).comap
        (ρ (levi g⁻¹)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, radicalElement c = u :=
      ⟨radicalCoordinates u, radicalElement_coordinates u⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    have hval : ((T.mirabolicTheta ψ m (radicalElement c) : ℂˣ) : ℂ) =
        (χ (radicalElement (g⁻¹.val *ᵥ c)) : ℂ) := by
      change ((theta ψ m (radicalElement c) : ℂˣ) : ℂ) = _
      rw [theta_radicalElement, coordinateCharacter_apply, radicalCoordinates_element]
      congr 1
      have hdot : (fun j => g.val (Fin.last m) j) ⬝ᵥ (g⁻¹.val *ᵥ c) =
          (g.val *ᵥ (g⁻¹.val *ᵥ c)) (Fin.last m) := rfl
      rw [hdot, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, levi_mul_radicalElement, map_mul,
      Module.End.mul_apply, hval]
    exact Jacquet.Localization.sub_mem_relations ρ _ χ _ _
  exact hspan hv

end Coordinates

/-! ## Finite Fourier inversion over the dual box -/

section Inversion

open Jacquet.Localization

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A vector fixed by the radical box of level `l`, whose twisted averages over the
radical box of level `M` vanish for every coordinate character of the dual box of level
`n(ψ) - l`, is zero. -/
theorem eq_zero_of_forall_characterAverage_eq_zero (m : ℕ)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (x : V) (l M : ℤ) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (m + 1 + 1)
    ∀ hρ : IsSmooth ρ,
      (∀ u : radical (m + 1) F.Carrier,
        radicalCoordinates u ∈ latticeBox T (m + 1) l → ρ u x = x) →
      (∀ a ∈ latticeBox T (m + 1) (T.additiveConductor ψ - l),
        characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) (radicalBox T m M)
          (isCompact_radicalBox T m M) x = 0) →
      x = 0 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro hρ hx havg
  let N := radical (m + 1) F.Carrier
  let H := radicalBox T m M
  have : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_radicalBox T m M)
  have : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup (H : Subgroup N))
  let K : Subgroup H := (radicalBox T m l).toSubgroup.comap (H : Subgroup N).subtype
  have hKopen : IsOpen (K : Set H) :=
    (radicalBox T m l).isOpen.preimage continuous_subtype_val
  have : Finite (H ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
  let := Fintype.ofFinite (H ⧸ K)
  let B := latticeBox T (m + 1) (T.additiveConductor ψ - l)
  let L := (latticeBox T (m + 1) (T.additiveConductor ψ - M)).addSubgroupOf B
  have : Finite (B ⧸ L) := finite_latticeBox_quotient T (m + 1) _ _
  let := Fintype.ofFinite (B ⧸ L)
  -- Each average as a normalized sum over `H ⧸ K`.
  have hsum : ∀ a ∈ B, characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) H
      (isCompact_radicalBox T m M) x =
      (Fintype.card (H ⧸ K) : ℂ)⁻¹ • ∑ c : H ⧸ K,
        ψ.complex (-(a ⬝ᵥ radicalCoordinates ((Quotient.out c : H) : N))) •
          ρ (((Quotient.out c : H) : N) : mirabolic (m + 1) F.Carrier) x := by
    intro a ha
    rw [characterAverage_eq_quotient_sum hρ _ H _ x K]
    · refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
      rw [coordinateCharacter_apply, AddChar.map_neg_eq_inv]
    · intro k hk
      rw [coordinateCharacter_eq_one T ψ m ha (k : N) hk, Units.val_one, inv_one, one_smul]
      exact hx _ hk
  -- The character sum over the dual box detects the coset of `K`.
  have hchar : ∀ c : H ⧸ K,
      (∑ b : B ⧸ L, ψ.complex (-(((Quotient.out b : B) : Fin (m + 1) → F.Carrier) ⬝ᵥ
          radicalCoordinates ((Quotient.out c : H) : N)))) •
        ρ (((Quotient.out c : H) : N) : mirabolic (m + 1) F.Carrier) x =
      if c = QuotientGroup.mk 1 then (Fintype.card (B ⧸ L) : ℂ) • x else 0 := by
    intro c
    have hyM : radicalCoordinates ((Quotient.out c : H) : N) ∈ latticeBox T (m + 1) M :=
      (Quotient.out c).property
    split_ifs with hc
    · have hk : Quotient.out c ∈ K := by
        have h' : (QuotientGroup.mk (Quotient.out c) : H ⧸ K) = QuotientGroup.mk 1 := by
          rw [QuotientGroup.out_eq', hc]
        have h'' := QuotientGroup.eq.mp h'
        rw [mul_one] at h''
        exact K.inv_mem_iff.mp h''
      rw [show ρ (((Quotient.out c : H) : N) : mirabolic (m + 1) F.Carrier) x = x from hx _ hk]
      congr 1
      have hone : ∀ b : B ⧸ L, ψ.complex (-(((Quotient.out b : B) : Fin (m + 1) → F.Carrier) ⬝ᵥ
          radicalCoordinates ((Quotient.out c : H) : N))) = 1 := by
        intro b
        rw [AddChar.map_neg_eq_inv, UnitaryAdditiveCharacter.complex_apply,
          character_dotProduct_eq_one T ψ (Quotient.out b).property
            (show radicalCoordinates ((Quotient.out c : H) : N) ∈ latticeBox T (m + 1) l from hk),
          Circle.coe_one, inv_one]
      rw [Finset.sum_congr rfl fun b _ => hone b, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    · have hk : Quotient.out c ∉ K := by
        intro hk
        apply hc
        rw [← QuotientGroup.out_eq' c]
        refine QuotientGroup.eq.mpr ?_
        rw [mul_one]
        exact K.inv_mem hk
      set y := radicalCoordinates ((Quotient.out c : H) : N)
      obtain ⟨b₀, hb₀, hψb₀⟩ : ∃ b₀ ∈ B, ψ (b₀ ⬝ᵥ y) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hy := mem_latticeBox_of_forall_character_eq_one T ψ hcon
        rw [sub_sub_cancel] at hy
        exact hk hy
      let f : B →+ F.Carrier :=
        { toFun := fun b => -((b : Fin (m + 1) → F.Carrier) ⬝ᵥ y)
          map_zero' := by simp
          map_add' := fun b b' => by
            simp only [AddSubgroup.coe_add, add_dotProduct, neg_add] }
      let φ : AddChar B ℂ := ψ.complex.compAddMonoidHom f
      have hφL : ∀ b ∈ L, φ b = 1 := by
        intro b hb
        change ψ.complex (-((b : Fin (m + 1) → F.Carrier) ⬝ᵥ y)) = 1
        rw [AddChar.map_neg_eq_inv, UnitaryAdditiveCharacter.complex_apply,
          character_dotProduct_eq_one T ψ (AddSubgroup.mem_addSubgroupOf.mp hb) hyM,
          Circle.coe_one, inv_one]
      have hφ₀ : φ ⟨b₀, hb₀⟩ ≠ 1 := by
        change ψ.complex (-(b₀ ⬝ᵥ y)) ≠ 1
        rw [AddChar.map_neg_eq_inv, UnitaryAdditiveCharacter.complex_apply, inv_ne_one]
        intro h
        exact hψb₀ (Circle.ext (h.trans Circle.coe_one.symm))
      have h0 := sum_out_eq_zero L φ hφL hφ₀
      change (∑ b : B ⧸ L, φ (Quotient.out b)) • _ = 0
      rw [h0, zero_smul]
  -- Summing the vanishing averages over the dual box.
  have h0 : ∑ b : B ⧸ L, characterAverage hρ
      (isOpen_ker_coordinateCharacter T ψ m (Quotient.out b : B)) H
      (isCompact_radicalBox T m M) x = 0 :=
    Finset.sum_eq_zero fun b _ => havg _ (Quotient.out b).property
  rw [Finset.sum_congr rfl fun b _ => hsum _ (Quotient.out b).property, ← Finset.smul_sum,
    Finset.sum_comm] at h0
  simp_rw [← Finset.sum_smul] at h0
  rw [Finset.sum_congr rfl fun c _ => hchar c] at h0
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, smul_smul] at h0
  refine (smul_eq_zero.mp h0).resolve_left (mul_ne_zero (inv_ne_zero ?_) ?_)
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- If each coordinate character eventually kills `x` under the radical-box averages,
then a single level kills `x` for all characters of a given dual box. -/
theorem exists_forall_characterAverage_eq_zero (m : ℕ)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (x : V) (A : ℤ) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (m + 1 + 1)
    ∀ hρ : IsSmooth ρ,
      (∀ a : Fin (m + 1) → F.Carrier, ∃ M : ℤ,
        characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) (radicalBox T m M)
          (isCompact_radicalBox T m M) x = 0) →
      ∃ M : ℤ, ∀ a ∈ latticeBox T (m + 1) A,
        characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) (radicalBox T m M)
          (isCompact_radicalBox T m M) x = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro hρ h
  choose M hM using h
  let U : (Fin (m + 1) → F.Carrier) → Set (Fin (m + 1) → F.Carrier) := fun a =>
    {a' | a' - a ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M a)}
  have hUopen : ∀ a, IsOpen (U a) := fun a =>
    (isOpen_latticeBox T (m + 1) _).preimage (continuous_id.sub continuous_const)
  have hcover : (latticeBox T (m + 1) A : Set (Fin (m + 1) → F.Carrier)) ⊆ ⋃ a, U a :=
    fun a _ => Set.mem_iUnion.mpr ⟨a, by
      show a - a ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M a)
      rw [sub_self]
      exact zero_mem _⟩
  obtain ⟨t, ht⟩ := (isCompact_latticeBox T (m + 1) A).elim_finite_subcover U hUopen hcover
  obtain ⟨M₀, hM₀⟩ := (t.image M).bddAbove
  refine ⟨M₀, fun a' ha' => ?_⟩
  obtain ⟨a, hat, ha'a⟩ := Set.mem_iUnion₂.mp (ht ha')
  have hle : M a ≤ M₀ := hM₀ (Finset.mem_coe.mpr (Finset.mem_image_of_mem M hat))
  refine characterAverage_eq_zero_of_le hρ _ (isCompact_radicalBox T m (M a))
    (isCompact_radicalBox T m M₀) (radicalBox_mono T m hle) ?_
  rw [characterAverage_congr hρ _ (isOpen_ker_coordinateCharacter T ψ m a) _ _
    (fun n hn => coordinateCharacter_eq_of_sub_mem T ψ m ha'a n hn)]
  exact hM a

end Inversion

/-! ## Vanishing of `Ψ⁻` and `Φ⁻` forces vanishing -/

section Vanishing

open Jacquet.Localization

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- BZ77 §3.2 and §3.5: a smooth representation `X` of `P_(m+2)` with `Ψ⁻ X = 0` and
`Φ⁻ X = 0` is zero. -/
theorem subsingleton_of_psiMinus_phiMinus (m : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier),
      Subsingleton ((Mirabolic.psiMinus T (m + 1)).obj X) →
      Subsingleton ((Mirabolic.phiMinus T ψ m).obj X) → Subsingleton X := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro X h1 h2
  let ρ := X.representation
  have hρ : IsSmooth ρ := X.isSmooth
  change Subsingleton (Coinvariants ρ (radical (m + 1) F.Carrier) 1) at h1
  change Subsingleton (Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m)) at h2
  have hrel1 := Submodule.Quotient.subsingleton_iff.mp h1
  have hrelθ := Submodule.Quotient.subsingleton_iff.mp h2
  -- Every vector lies in the relations of every coordinate character.
  have hall : ∀ (a : Fin (m + 1) → F.Carrier) (v : X),
      v ∈ relations ρ (radical (m + 1) F.Carrier) (coordinateCharacter T ψ m a) := by
    intro a v
    by_cases ha : a = 0
    · rw [ha, coordinateCharacter_zero, hrel1]
      exact Submodule.mem_top
    · obtain ⟨g, hg⟩ := exists_lastRow_eq_of_ne_zero a ha
      have hv := levi_inv_mem_relations T ψ m ρ g (v := ρ (levi g) v)
        (by rw [hrelθ]; exact Submodule.mem_top)
      rw [hg, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at hv
      exact hv
  suffices h : ∀ x : X, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  -- A radical lattice box fixing `x`.
  obtain ⟨K, hK⟩ := hρ x
  have hfix : ∀ k ∈ K, ρ k x = x := fun k hk =>
    (Representation.mem_invariants _ x).mp hK ⟨k, hk⟩
  have hrad0 : {d : Fin (m + 1) → F.Carrier |
      (radicalElement d : mirabolic (m + 1) F.Carrier) ∈ K} ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  have hx : ∀ u : radical (m + 1) F.Carrier,
      radicalCoordinates u ∈ latticeBox T (m + 1) l → ρ u x = x := by
    intro u hu
    have h := hfix _ (hl hu)
    rwa [radicalElement_coordinates] at h
  -- Each coordinate character eventually kills `x` along the radical boxes.
  have hcover : ∀ n : radical (m + 1) F.Carrier, ∃ k : ℕ, n ∈ radicalBox T m k := by
    intro n
    obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates n)
    exact ⟨M.toNat, radicalBox_mono T m (Int.self_le_toNat M) hM⟩
  have hev : ∀ a : Fin (m + 1) → F.Carrier, ∃ M : ℤ,
      characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) (radicalBox T m M)
        (isCompact_radicalBox T m M) x = 0 := by
    intro a
    obtain ⟨k₀, hk₀⟩ := eventually_characterAverage_eq_zero hρ
      (isOpen_ker_coordinateCharacter T ψ m a) (fun k : ℕ => radicalBox T m k)
      (fun k => isCompact_radicalBox T m k)
      (fun j k hjk => radicalBox_mono T m (Nat.cast_le.mpr hjk)) hcover (hall a x)
    exact ⟨k₀, hk₀ k₀ le_rfl⟩
  obtain ⟨M, hM⟩ := exists_forall_characterAverage_eq_zero T ψ m ρ x
    (T.additiveConductor ψ - l) hρ hev
  exact eq_zero_of_forall_characterAverage_eq_zero T ψ m ρ x l M hρ hx hM

end Vanishing

end Langlands.Derivative.Mirabolic
