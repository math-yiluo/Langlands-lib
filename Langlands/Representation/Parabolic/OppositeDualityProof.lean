import Langlands.Representation.Parabolic.OppositeDualityStatement
import Langlands.Representation.Parabolic.NaturalJacquetDualityProof
import Langlands.Representation.Jacquet.StablePairingAsymptotics

/-!
# Canonical pairing and opposite Jacquet duality for block parabolics of `GL_n`

The abstract stable evaluation pairing, instantiated with the opposite radical as
its upper subgroup and the upper radical as its opposite subgroup, gives the
unique bilinear form with Casselman's asymptotics and the induced equivalence of
the opposite Jacquet module of the smooth dual with the smooth dual of the upper
Jacquet module.
-/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear
open scoped Topology NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section Data

variable {n : ℕ} (B : BlockShape n)

/-- A block Iwahori factorization also writes each element as upper times Levi
times lower. -/
theorem HasBlockIwahoriFactorization.factor_upper :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization T K →
      ∀ k ∈ K, ∃ u ∈ K, u ∈ B.unipotentSubgroup F.Carrier ∧
        ∃ m ∈ K, m ∈ B.leviSubgroup F.Carrier ∧
          ∃ l ∈ K, l ∈ B.oppositeUnipotentSubgroup F.Carrier ∧ k = u * m * l := by
  let := T.topology
  intro K hK k hk
  obtain ⟨l, hlK, hlN, m, hmK, hmM, u, huK, huN, hkf⟩ :=
    HasBlockIwahoriFactorization.factor F T B hK k⁻¹ (inv_mem hk)
  refine ⟨u⁻¹, inv_mem huK, (B.unipotentSubgroup F.Carrier).inv_mem huN,
    m⁻¹, inv_mem hmK, (B.leviSubgroup F.Carrier).inv_mem hmM,
    l⁻¹, inv_mem hlK, (B.oppositeUnipotentSubgroup F.Carrier).inv_mem hlN, ?_⟩
  rw [← inv_inv k, hkf]
  group

/-- Powers of an inverse block scalar keep lower elements of a factorized subgroup
inside it. -/
theorem HasBlockIwahoriFactorization.lower_conj_inv_pow :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)}, B.HasBlockIwahoriFactorization T K →
      ∀ {a : Fin B.length → F.Carrierˣ}, B.IsWeaklyContracting T a →
        ∀ l ∈ K, l ∈ B.oppositeUnipotentSubgroup F.Carrier → ∀ r : ℕ,
          (B.blockScalar F.Carrier a)⁻¹ ^ r * l * ((B.blockScalar F.Carrier a)⁻¹ ^ r)⁻¹ ∈ K := by
  let := T.topology
  intro K hK a ha l hl hlN r
  suffices h : (B.blockScalar F.Carrier a)⁻¹ ^ r * l * ((B.blockScalar F.Carrier a)⁻¹ ^ r)⁻¹ ∈
      B.iwahoriLower F.Carrier K.toSubgroup from h.1
  induction r with
  | zero => simpa using (⟨hl, hlN⟩ : l ∈ B.iwahoriLower F.Carrier K.toSubgroup)
  | succ r ih =>
    have e : (B.blockScalar F.Carrier a)⁻¹ ^ (r + 1) * l *
        ((B.blockScalar F.Carrier a)⁻¹ ^ (r + 1))⁻¹ =
        (B.blockScalar F.Carrier a)⁻¹ *
          ((B.blockScalar F.Carrier a)⁻¹ ^ r * l * ((B.blockScalar F.Carrier a)⁻¹ ^ r)⁻¹) *
            B.blockScalar F.Carrier a := by
      rw [pow_succ', mul_inv_rev, inv_inv]
      simp only [mul_assoc]
    rw [e]
    exact (hK.2 a ha).2 _ ih

/-- High powers of an inverse strict block scalar conjugate a compact set of lower
elements into any identity neighbourhood. -/
theorem eventually_pow_inv_conj_mem :
    letI := T.topology
    ∀ (a : Fin B.length → F.Carrierˣ), B.IsStrictlyContracting T a →
      ∀ (C : Set (GeneralLinear n F.Carrier)), IsCompact C →
        ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
          ∃ r : ℕ, ∀ s : ℕ, r ≤ s → ∀ l ∈ C, l ∈ B.oppositeUnipotentSubgroup F.Carrier →
            (B.blockScalar F.Carrier a)⁻¹ ^ s * l * ((B.blockScalar F.Carrier a)⁻¹ ^ s)⁻¹ ∈
              U := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro a ha C hC U hU
  obtain ⟨ε, hε, -, hc⟩ := B.uniformCompactBlockContraction T ∅
    (C ∩ (B.oppositeUnipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)))
    isCompact_empty (Set.empty_subset _)
    (hC.inter_right (B.isClosed_oppositeUnipotentSubgroup F.Carrier)) Set.inter_subset_right
    U hU
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  refine ⟨r, fun s hs l hl hlN => ?_⟩
  have hpow : B.blockScalar F.Carrier (fun i => a i ^ s) = B.blockScalar F.Carrier a ^ s :=
    map_pow (B.blockScalar F.Carrier) a s
  rw [inv_pow, inv_inv, ← hpow]
  exact (hc _ (hr s hs)).2 l ⟨hl, hlN⟩

/-- Stable pairing data for the opposite orientation: the opposite radical is the
upper subgroup of the data, the upper radical its opposite subgroup, and the
contracting element is the inverse block scalar of a strictly contracting tuple. -/
def oppositePairingData (a : Fin B.length → F.Carrierˣ) (ha : B.IsStrictlyContracting T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Jacquet.StablePairingData (GeneralLinear n F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact
    { N := B.oppositeUnipotentSubgroup F.Carrier
      Nbar := B.unipotentSubgroup F.Carrier
      M := B.leviSubgroup F.Carrier
      hMN := B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier
      hMNbar := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
      g := (B.blockScalar F.Carrier a)⁻¹
      commute := fun m hm => by
        have h : Commute m (B.blockScalar F.Carrier a) :=
          blockScalar_commute_of_mem_leviSubgroup F B a hm
        exact h.inv_right.eq
      Good := fun K => IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        B.HasBlockIwahoriFactorization T K
      isCompact := fun K hK => hK.1
      exists_good_subset := fun O hO h1 => by
        obtain ⟨K, hKc, hKO, hfac⟩ :=
          B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T (hO.mem_nhds h1)
        exact ⟨K, ⟨hKc, hfac⟩, hKO⟩
      good_conj := fun m hm K hK =>
        ⟨Jacquet.isCompact_conjOpenSubgroup m K hK.1,
          hasBlockIwahoriFactorization_conj F T B hm hK.2⟩
      factor := fun K hK => HasBlockIwahoriFactorization.factor_upper F T B hK.2
      lower_conj := fun K hK l hl hlN => by
        rw [inv_inv]
        exact ((hK.2.2 a ha.weak).1 l ⟨hl, hlN⟩).1
      upper_conj := fun K hK l hl hlN r =>
        HasBlockIwahoriFactorization.lower_conj_inv_pow F T B hK.2 ha.weak l hl hlN r
      deep := fun K₀ K₁ hK₀ _ => by
        obtain ⟨r, hr⟩ := eventually_pow_inv_conj_mem F T B a ha K₀ hK₀.1 K₁
          (K₁.isOpen.mem_nhds K₁.one_mem)
        exact ⟨r, fun l hl hlN => hr r le_rfl l hl hlN⟩ }

theorem oppositePairingData_g_inv (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (oppositePairingData F T B a ha).g⁻¹ = B.blockScalar F.Carrier a :=
  inv_inv _

/-- Admissible representations satisfy the stable-duality and canonical-lift
hypotheses of the opposite pairing data. -/
theorem oppositePairingData_admits (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsAdmissible ρ),
      (oppositePairingData F T B a ha).Admits ρ hρ.1 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ
  have hcof : ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
      ∃ L : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK, -⟩ :=
      B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  have hρ' := isAdmissible_smoothContragredient_of_compact_cofinal hcof ρ hρ
  have hg := oppositePairingData_g_inv F T B a ha
  exact
    { duality := fun K _ =>
        Jacquet.compactCompression_stableEvaluationDuality ρ hρ.1 K _ _ (hρ.2 K)
      upper_surjective := fun K hK =>
        (Jacquet.blockOppositeStableImageJacquetBijective F T B (SmoothDual ρ)
          (smoothContragredient ρ) hρ' K hK.1 hK.2 a ha).2
      upper_kernel := fun K hK =>
        (Jacquet.blockOppositePowerKernelJacquet F T B (SmoothDual ρ)
          (smoothContragredient ρ) hρ' K hK.1 hK.2 a ha).ge
      lower_surjective := fun K hK => by
        rw [hg]
        exact (Jacquet.blockStableImageJacquetBijective F T B V ρ hρ K hK.1 hK.2 a ha).2
      lower_kernel := fun K hK => by
        rw [hg]
        exact (Jacquet.blockPowerKernelJacquet F T B V ρ hρ K hK.1 hK.2 a ha).ge }

/-- Block scalars of weakly contracting tuples are contracting elements of the
opposite pairing data. -/
theorem isContractingElement_blockScalar (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) {c : Fin B.length → F.Carrierˣ}
    (hc : B.IsWeaklyContracting T c) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (oppositePairingData F T B a ha).IsContractingElement (B.blockScalar F.Carrier c) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine ⟨fun m hm => blockScalar_commute_of_mem_leviSubgroup F B c hm, ?_, ?_, ?_⟩
  · change B.blockScalar F.Carrier c * (B.blockScalar F.Carrier a)⁻¹ =
      (B.blockScalar F.Carrier a)⁻¹ * B.blockScalar F.Carrier c
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm]
  · intro K hK l hl hlN
    exact ((hK.2.2 c hc).1 l ⟨hl, hlN⟩).1
  · intro K hK u hu huN
    exact ((hK.2.2 c hc).2 u ⟨hu, huN⟩).1

end Data

section Pairing

variable {n : ℕ} (B : BlockShape n)

/-- The positive half modulus cancels the inverse half in the normalized upper
action, on quotient representatives. -/
theorem leviHalfModulus_mul_normalizedAction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (f : Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ)
    (m : B.Levi F.Carrier) (w : V) :
    (T.leviHalfModulus B m : ℂ) *
        f (Jacquet.normalizedActionOfModulus ρ
          (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
          ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)
          (B.leviEquiv F.Carrier m) (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) w)) =
      f (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (ρ (B.leviEmbedding F.Carrier m) w)) := by
  rw [Jacquet.normalizedActionOfModulus_mk, map_smul, smul_eq_mul, ← mul_assoc]
  have hδ : ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)
      (B.leviEquiv F.Carrier m) = T.leviModulus B m := by
    simp
  rw [hδ, T.leviHalfModulus_apply]
  have hs : (((NNReal.sqrt (T.leviModulus B m : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by
    simp [(T.leviModulus B m).ne_zero]
  rw [mul_inv_cancel₀ hs, one_mul]
  rfl

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The canonical asymptotics in unnormalized form: for each vector and smooth
functional the pairing computes the matrix coefficient on all sufficiently deep
block scalars. -/
theorem canonicalPairingAsymptotics_iff :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
      (b : Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ),
      CanonicalPairingAsymptotics F T B V ρ b ↔
        ∀ (v : V) (ℓ : SmoothDual ρ), ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
          ∀ c : Fin B.length → F.Carrierˣ, B.IsDeeplyContracting T ε c →
            smoothDualPairing ρ ℓ (ρ (B.blockScalar F.Carrier c) v) =
              b (Jacquet.mk (smoothContragredient ρ) (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
                (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier)
                  (ρ (B.blockScalar F.Carrier c) v)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ b
  have key : ∀ (v : V) (ℓ : SmoothDual ρ) (c : Fin B.length → F.Carrierˣ),
      (T.leviHalfModulus B (B.blockScalarLevi F.Carrier c) : ℂ) *
          b (Jacquet.mk (smoothContragredient ρ) (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
            (Jacquet.normalizedActionOfModulus ρ
              (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
              (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
              ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)
              (B.leviEquiv F.Carrier (B.blockScalarLevi F.Carrier c))
              (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v)) =
        b (Jacquet.mk (smoothContragredient ρ) (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
          (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (ρ (B.blockScalar F.Carrier c) v)) :=
    fun v ℓ c => leviHalfModulus_mul_normalizedAction F T B ρ _ _ v
  constructor
  · intro h v ℓ
    obtain ⟨ε, hε, hε1, H⟩ := h v ℓ
    exact ⟨ε, hε, hε1, fun c hc => (H c hc).trans (key v ℓ c)⟩
  · intro h v ℓ
    obtain ⟨ε, hε, hε1, H⟩ := h v ℓ
    exact ⟨ε, hε, hε1, fun c hc => (H c hc).trans (key v ℓ c).symm⟩

/-- A stable pairing of the opposite data has the canonical asymptotics. -/
theorem canonicalPairingAsymptotics_of_isStablePairing (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsAdmissible ρ)
      (b : Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ),
      (oppositePairingData F T B a ha).IsStablePairing ρ hρ.1 b →
        CanonicalPairingAsymptotics F T B V ρ b := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro ρ hρ b hb
  have hA := oppositePairingData_admits F T B a ha ρ hρ
  rw [canonicalPairingAsymptotics_iff]
  intro v ℓ
  obtain ⟨K, hK, S, hS, H⟩ := (hb.hasAsymptotics hA).exists hρ.1 v ℓ
  obtain ⟨ε, hε, hε1, hc⟩ := B.uniformCompactBlockContraction T (S : Set _) ∅
    S.finite_toSet.isCompact hS isCompact_empty (Set.empty_subset _) (K : Set _)
    (K.isOpen.mem_nhds K.one_mem)
  refine ⟨ε, hε, hε1, fun c hdeep => ?_⟩
  exact H _ (isContractingElement_blockScalar F T B a ha
    (fun i j hij => ((hdeep i j hij).trans_le hε1).le))
    (fun x hx => (hc c hdeep).1 x hx)

/-- Every bilinear form with the canonical asymptotics is a stable pairing of the
opposite data. -/
theorem isStablePairing_of_canonicalPairingAsymptotics (a : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsAdmissible ρ)
      (b : Jacquet.Coinvariants (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
          Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ),
      CanonicalPairingAsymptotics F T B V ρ b →
        (oppositePairingData F T B a ha).IsStablePairing ρ hρ.1 b := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  classical
  intro ρ hρ b hb
  rw [canonicalPairingAsymptotics_iff] at hb
  set D := oppositePairingData F T B a ha with hD
  intro K hK ℓ t ht
  -- The matrix-coefficient identity for one block scalar and one vector.
  let P : (Fin B.length → F.Carrierˣ) → V → Prop := fun c w =>
    smoothDualPairing ρ ℓ (ρ (B.blockScalar F.Carrier c) w) =
      b (Jacquet.mk (smoothContragredient ρ) (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
        (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (ρ (B.blockScalar F.Carrier c) w))
  have hadd : ∀ c w₁ w₂, P c w₁ → P c w₂ → P c (w₁ + w₂) := by
    intro c w₁ w₂ h₁ h₂
    simp only [P, map_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hsmul : ∀ c (z : ℂ) w, P c w → P c (z • w) := by
    intro c z w h
    simp only [P, map_smul, smul_eq_mul] at h ⊢
    rw [h]
  have hzero : ∀ c, P c 0 := by
    intro c
    simp only [P, map_zero]
  -- A uniform depth for all `K`-fixed vectors, by finite-dimensionality.
  have hfin : Module.Finite ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hset : ∀ s' : Finset (fixedVectors ρ K.toSubgroup),
      ∃ ε : ℝ, 0 < ε ∧ ∀ c, B.IsDeeplyContracting T ε c → ∀ w ∈ s', P c (w : V) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => exact ⟨1, one_pos, fun c _ w hw => absurd hw (Finset.notMem_empty w)⟩
    | insert x s' hx ih =>
      obtain ⟨ε₁, h₁, H₁⟩ := ih
      obtain ⟨ε₂, h₂, -, H₂⟩ := hb (x : V) (ℓ : SmoothDual ρ)
      refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun c hc w hw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact H₂ c (fun i j hij => (hc i j hij).trans_le (min_le_right _ _))
      · exact H₁ c (fun i j hij => (hc i j hij).trans_le (min_le_left _ _)) w hw
  obtain ⟨ε, hε, H⟩ := hset s
  have hunif : ∀ c, B.IsDeeplyContracting T ε c →
      ∀ w : fixedVectors ρ K.toSubgroup, P c (w : V) := by
    intro c hc w
    have hw : w ∈ Submodule.span ℂ (s : Set (fixedVectors ρ K.toSubgroup)) := by
      rw [hs]
      exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact H c hc x hx
    | zero => exact hzero c
    | add x y _ _ hx hy => exact hadd c _ _ hx hy
    | smul z x _ hx => exact hsmul c z _ hx
  -- Compare a stable vector with a deep translate.
  obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  obtain ⟨w, hw⟩ := (Jacquet.mem_stableImage ρ hρ.1 K (D.isCompact K hK) D.g⁻¹ t).mp ht r
  have ht' : (t : V) =
      Compact.averageMap ρ hρ.1 K (D.isCompact K hK) (ρ (D.g⁻¹ ^ r) w) := by
    rw [← hw, D.compressedAction_inv_pow_apply ρ hρ.1 K hK r w]
  have hgr : D.g⁻¹ ^ r = B.blockScalar F.Carrier (fun i => a i ^ r) := by
    rw [oppositePairingData_g_inv F T B a ha]
    exact (map_pow (B.blockScalar F.Carrier) a r).symm
  have hup : ∀ u ∈ K, u ∈ D.N → (D.g⁻¹ ^ r)⁻¹ * u * D.g⁻¹ ^ r ∈ K := by
    intro u hu huN
    rw [inv_pow, inv_inv]
    exact D.upper_conj K hK u hu huN r
  have hmk := D.mk_averageMap_apply ρ hρ.1 K hK (fun m hm => D.commute_pow m hm r) hup w.property
  have hP : smoothDualPairing ρ ℓ (ρ (D.g⁻¹ ^ r) w) =
      b (Jacquet.mk (smoothContragredient ρ) (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
        (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) (ρ (D.g⁻¹ ^ r) w)) := by
    rw [hgr]
    exact hunif _ (hr r le_rfl) w
  change b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar t) =
    smoothDualPairing ρ ℓ t
  rw [ht', hmk, Jacquet.smoothDualPairing_averageMap ρ hρ.1 K _ ℓ.property]
  exact hP.symm

/-- Two stable pairings for the same data coincide. -/
theorem stablePairing_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (D : Jacquet.StablePairingData G)
    {ρ : Representation ℂ G W} {hρ : IsSmooth ρ} (hA : D.Admits ρ hρ)
    {b₁ b₂ : Jacquet.Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ]
      Jacquet.Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}
    (h₁ : D.IsStablePairing ρ hρ b₁) (h₂ : D.IsStablePairing ρ hρ b₂) : b₁ = b₂ := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  obtain ⟨K, hK, ℓ, -, t, -, ht, -, rfl, -, rfl, -⟩ := D.exists_common_lift hA x x y y
  rw [h₁ K hK ℓ t ht, h₂ K hK ℓ t ht]

/-- Existence and uniqueness of the canonical pairing. -/
theorem canonicalPairingClause : CanonicalPairingClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ
  obtain ⟨a, ha⟩ := B.deepChamberNonempty T 1 zero_lt_one
  have has : B.IsStrictlyContracting T a := ha
  have hA := oppositePairingData_admits F T B a has ρ hρ
  obtain ⟨b, hb⟩ := (oppositePairingData F T B a has).exists_isStablePairing hA
  refine ⟨b, canonicalPairingAsymptotics_of_isStablePairing F T B V a has ρ hρ b hb,
    fun b' hb' => ?_⟩
  exact stablePairing_eq _ hA
    (isStablePairing_of_canonicalPairingAsymptotics F T B V a has ρ hρ b' hb') hb

/-- Every pairing with the canonical asymptotics induces the equivalence of the
normalized opposite Jacquet module of the smooth dual with the smooth dual of the
normalized upper Jacquet module. -/
theorem oppositeJacquetDualityClause : OppositeJacquetDualityClause F T B V := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  intro ρ hρ b hb
  obtain ⟨a, ha⟩ := B.deepChamberNonempty T 1 zero_lt_one
  have has : B.IsStrictlyContracting T a := ha
  have hA := oppositePairingData_admits F T B a has ρ hρ
  have hst := isStablePairing_of_canonicalPairingAsymptotics F T B V a has ρ hρ b hb
  intro δ J JopDual
  have hδ : IsOpen (δ.ker : Set (B.leviSubgroup F.Carrier)) :=
    (T.isOpen_ker_leviModulus B).preimage (B.leviEquivContinuous F.Carrier).symm.continuous
  obtain ⟨E, hE⟩ := hst.exists_equiv hA (ContinuousMulEquiv.refl _)
    (fun m => (Jacquet.inverseHalfCharacter δ⁻¹ m : ℂ)) (Jacquet.inverseHalfCharacter δ)
    (fun m => by
      rw [mul_comm]
      exact inverseHalfCharacter_mul_inverseHalfCharacter_inv δ m)
    (Jacquet.isOpen_ker_inverseHalfCharacter δ hδ) JopDual (LinearEquiv.refl ℂ _)
    (fun m x => by
      obtain ⟨ℓ, rfl⟩ := Jacquet.mk_surjective _ _ x
      rfl)
    J (fun m y => by
      obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ y
      rfl)
  exact ⟨E, fun ℓ v => hE _ _⟩

/-- Existence of a pairing with the canonical asymptotics. -/
theorem exists_canonicalPairingAsymptotics :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V, IsAdmissible ρ →
      ∃ b : Jacquet.Coinvariants (smoothContragredient ρ)
          (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
            Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ,
        CanonicalPairingAsymptotics F T B V ρ b :=
  fun ρ hρ => (canonicalPairingClause F T B V ρ hρ).exists

/-- Two pairings with the canonical asymptotics coincide. -/
theorem eq_of_canonicalPairingAsymptotics :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V, IsAdmissible ρ →
      ∀ b₁ b₂ : Jacquet.Coinvariants (smoothContragredient ρ)
          (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
            Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ,
        CanonicalPairingAsymptotics F T B V ρ b₁ →
          CanonicalPairingAsymptotics F T B V ρ b₂ → b₁ = b₂ :=
  fun ρ hρ _ _ h₁ h₂ => (canonicalPairingClause F T B V ρ hρ).unique h₁ h₂

/-- One equivalence of the normalized opposite Jacquet module of the smooth dual with
the smooth dual of the normalized upper Jacquet module is induced by every pairing with
the canonical asymptotics. -/
theorem exists_oppositeJacquetDualityEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V, IsAdmissible ρ →
      let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
      let J := Jacquet.normalizedActionOfModulus ρ
        (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) δ
      let JopDual := Jacquet.normalizedActionOfModulus (smoothContragredient ρ)
        (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier) δ⁻¹
      ∃ E : Representation.Equiv JopDual (smoothContragredient J),
        ∀ b : Jacquet.Coinvariants (smoothContragredient ρ)
            (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ]
              Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier) →ₗ[ℂ] ℂ,
          CanonicalPairingAsymptotics F T B V ρ b →
            ∀ (ℓ : SmoothDual ρ) (v : V),
              (E (Jacquet.mk (smoothContragredient ρ)
                (B.oppositeUnipotentSubgroup F.Carrier) ℓ)).1
                  (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v) =
              b (Jacquet.mk (smoothContragredient ρ)
                (B.oppositeUnipotentSubgroup F.Carrier) ℓ)
                  (Jacquet.mk ρ (B.unipotentSubgroup F.Carrier) v) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ δ J JopDual
  obtain ⟨b₀, hb₀⟩ := exists_canonicalPairingAsymptotics F T B V ρ hρ
  obtain ⟨E, hE⟩ := oppositeJacquetDualityClause F T B V ρ hρ b₀ hb₀
  refine ⟨E, fun b hb ℓ v => ?_⟩
  rw [eq_of_canonicalPairingAsymptotics F T B V ρ hρ b b₀ hb hb₀]
  exact hE ℓ v

/-- If the upper Jacquet module of an admissible representation vanishes, so does the
opposite Jacquet module of its smooth dual. -/
theorem subsingleton_oppositeJacquet_smoothContragredient :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V, IsAdmissible ρ →
      Subsingleton (Jacquet.Coinvariants ρ (B.unipotentSubgroup F.Carrier)) →
        Subsingleton (Jacquet.Coinvariants (smoothContragredient ρ)
          (B.oppositeUnipotentSubgroup F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ hsub
  obtain ⟨E, -⟩ := exists_oppositeJacquetDualityEquiv F T B V ρ hρ
  have : Subsingleton (SmoothDual (Jacquet.normalizedActionOfModulus ρ
      (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
      (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
      ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom))) := by
    refine ⟨fun f g => Subtype.ext (LinearMap.ext fun x => ?_)⟩
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  exact E.toLinearEquiv.injective.subsingleton

end Pairing

/-- **Casselman's canonical pairing and opposite Jacquet duality** for the
standard block parabolics of `GL_n` over a finite extension of `ℚ_p`. -/
theorem oppositeDualityStatement {n : ℕ} (B : BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    OppositeDualityStatement F T B V :=
  ⟨canonicalPairingClause F T B V, oppositeJacquetDualityClause F T B V⟩

end Langlands.Parabolic
