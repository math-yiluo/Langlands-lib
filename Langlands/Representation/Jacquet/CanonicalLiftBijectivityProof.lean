import Langlands.Representation.Jacquet.BlockPowerKernelProof
import Langlands.Representation.Jacquet.CompressionStabilizationProof

/-! # Bijectivity of the actual stable-image Jacquet map -/

namespace Langlands.Jacquet

universe uF uV

section Block

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Block scalars commute with every element of the embedded common Levi. -/
theorem blockScalar_mul_eq_of_mem_leviSubgroup (a : Fin B.length → F.Carrierˣ)
    {m : GeneralLinear n F.Carrier} (hm : m ∈ B.leviSubgroup F.Carrier) :
    B.blockScalar F.Carrier a * m = m * B.blockScalar F.Carrier a := by
  obtain ⟨m', rfl⟩ := hm
  change B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a) *
      B.leviEmbedding F.Carrier m' =
    B.leviEmbedding F.Carrier m' * B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)
  rw [← map_mul, ← map_mul, B.blockScalarLevi_commute F.Carrier a m']

/-- Some power of a strict block scalar carries any vector to a vector fixed by the
whole compact lower radical intersection `K ∩ N⁻`. The compact set `K ∩ N⁻` is
uniformly contracted into an open stabilizer of the vector. -/
theorem exists_blockScalar_pow_iwahoriLower_fixed :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsSmooth ρ →
      ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier)),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∀ v : V, ∃ s : ℕ, ∀ l ∈ B.iwahoriLower F.Carrier K.toSubgroup,
        ρ l (ρ (B.blockScalar F.Carrier a ^ s) v) = ρ (B.blockScalar F.Carrier a ^ s) v := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK a ha v
  obtain ⟨U, hU⟩ := hρ v
  have hclosed : IsClosed
      (B.oppositeUnipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) := by
    let := T.valuativeRel
    let := T.localField
    let := T.fieldT2
    exact B.isClosed_oppositeUnipotentSubgroup F.Carrier
  have hLc : IsCompact
      (B.iwahoriLower F.Carrier K.toSubgroup : Set (GeneralLinear n F.Carrier)) :=
    hK.inter_right hclosed
  obtain ⟨ε, hε, -, hc⟩ := B.uniformCompactBlockContraction T ∅
    (B.iwahoriLower F.Carrier K.toSubgroup : Set (GeneralLinear n F.Carrier))
    isCompact_empty (Set.empty_subset _) hLc (fun x hx => hx.2)
    (U : Set (GeneralLinear n F.Carrier)) (U.isOpen.mem_nhds U.one_mem)
  obtain ⟨s, hs⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  refine ⟨s, fun l hl => ?_⟩
  have hpow : B.blockScalar F.Carrier (fun i => a i ^ s) = B.blockScalar F.Carrier a ^ s :=
    map_pow (B.blockScalar F.Carrier) a s
  have hlU := (hc (fun i => a i ^ s) (hs s le_rfl)).2 l hl
  rw [hpow] at hlU
  calc
    ρ l (ρ (B.blockScalar F.Carrier a ^ s) v) =
        ρ (B.blockScalar F.Carrier a ^ s)
          (ρ ((B.blockScalar F.Carrier a ^ s)⁻¹ * l * B.blockScalar F.Carrier a ^ s) v) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = ρ (B.blockScalar F.Carrier a ^ s) v :=
      congrArg (ρ (B.blockScalar F.Carrier a ^ s)) (hU ⟨_, hlU⟩)

/-- Bijectivity of the actual stable-image Jacquet map for a smooth representation
whose `K`-fixed vectors are finite dimensional. -/
theorem stableImageJacquetMap_bijective_of_finiteDimensional
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) →
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        Function.Bijective (stableImageJacquetMap ρ hρ K hK (B.blockScalar F.Carrier a)
          (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfin hfac a ha
  have hcompl := powerKernelSup_isCompl_stableImage ρ hρ K hK
    (B.blockScalar F.Carrier a) hfin
  have hker := blockPowerKernel_eq_jacquetKernel F T B V ρ hρ K hK hfac a ha
  -- Every fixed vector has the quotient of a stable-image vector.
  have hsplit : ∀ x : fixedVectors ρ K.toSubgroup,
      ∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) =
          mk ρ (B.unipotentSubgroup F.Carrier) (x : V) := by
    intro x
    have hx : x ∈ powerKernelSup ρ hρ K hK (B.blockScalar F.Carrier a) ⊔
        stableImage ρ hρ K hK (B.blockScalar F.Carrier a) := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hker, LinearMap.mem_ker] at hk
    have hk0 : mk ρ (B.unipotentSubgroup F.Carrier) (k : V) = 0 :=
      congrArg Subtype.val hk
    rw [Submodule.coe_add, map_add, hk0, zero_add]
  -- Powers of the Levi scalar can be cancelled on the image of the stable image.
  have hstep : ∀ z : Coinvariants ρ (B.unipotentSubgroup F.Carrier),
      (∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) =
          action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
            (B.blockScalarInLevi F.Carrier a) z) →
      ∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    rintro z ⟨t, htz⟩
    obtain ⟨t', rfl⟩ :=
      (stableImageAction_bijective ρ hρ K hK (B.blockScalar F.Carrier a) hfin).2 t
    refine ⟨t', ?_⟩
    apply (Representation.apply_bijective
      (action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))
      (B.blockScalarInLevi F.Carrier a)).injective
    rw [← htz]
    exact (blockCompressedAction_mk F T n B V ρ hρ K hK hfac a ha.weak
      (t' : fixedVectors ρ K.toSubgroup)).symm
  have hpow : ∀ (s : ℕ) (z : Coinvariants ρ (B.unipotentSubgroup F.Carrier)),
      (∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) =
          action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
            (B.blockScalarInLevi F.Carrier a ^ s) z) →
      ∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) = z := by
    intro s
    induction s with
    | zero =>
      intro z hz
      simpa using hz
    | succ s ih =>
      intro z hz
      apply hstep
      apply ih
      simpa only [pow_succ, map_mul, Module.End.mul_apply] using hz
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have h1 : (t : fixedVectors ρ K.toSubgroup) ∈ LinearMap.ker (fixedJacquetMap ρ
        (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) K.toSubgroup) := ht
    rw [← hker] at h1
    have h0 := hcompl.disjoint.le_bot ⟨h1, t.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro y
    suffices h : ∃ t : stableImage ρ hρ K hK (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier) ((t : fixedVectors ρ K.toSubgroup) : V) =
          (y : Coinvariants ρ (B.unipotentSubgroup F.Carrier)) by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, Subtype.ext ht⟩
    obtain ⟨v, hv⟩ := mk_surjective ρ (B.unipotentSubgroup F.Carrier)
      (y : Coinvariants ρ (B.unipotentSubgroup F.Carrier))
    obtain ⟨s, hs⟩ := exists_blockScalar_pow_iwahoriLower_fixed F T B V ρ hρ K hK a ha v
    -- The Levi factor of `K` acts through the fixed vector `y`.
    have hlevi : ∀ m ∈ B.iwahoriLevi F.Carrier K.toSubgroup,
        mk ρ (B.unipotentSubgroup F.Carrier) (ρ m (ρ (B.blockScalar F.Carrier a ^ s) v)) =
          action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
            (B.blockScalarInLevi F.Carrier a ^ s)
            (y : Coinvariants ρ (B.unipotentSubgroup F.Carrier)) := by
      intro m hm
      have hc : m * B.blockScalar F.Carrier a ^ s = B.blockScalar F.Carrier a ^ s * m :=
        ((Commute.pow_left
          (blockScalar_mul_eq_of_mem_leviSubgroup F B a hm.2 : Commute _ _) s)).symm
      have hgs : ((B.blockScalarInLevi F.Carrier a ^ s : B.leviSubgroup F.Carrier) :
          GeneralLinear n F.Carrier) = B.blockScalar F.Carrier a ^ s := by
        simp
      have hy := y.property ⟨⟨m, hm.2⟩, hm.1⟩
      calc
        mk ρ (B.unipotentSubgroup F.Carrier) (ρ m (ρ (B.blockScalar F.Carrier a ^ s) v)) =
            mk ρ (B.unipotentSubgroup F.Carrier)
              (ρ (B.blockScalarInLevi F.Carrier a ^ s : B.leviSubgroup F.Carrier) (ρ m v)) := by
          rw [hgs, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
        _ = action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
              (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
              (B.blockScalarInLevi F.Carrier a ^ s)
              (action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
                (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) ⟨m, hm.2⟩
                (mk ρ (B.unipotentSubgroup F.Carrier) v)) := by
          rw [action_mk, action_mk]
        _ = _ := by
          rw [hv]
          exact congrArg _ hy
    -- Every `K`-translate of `ρ(g^s) v` has quotient `A^s y`.
    have hconst : ∀ k : K,
        mk ρ (B.unipotentSubgroup F.Carrier) (ρ k.val (ρ (B.blockScalar F.Carrier a ^ s) v)) =
          action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
            (B.blockScalarInLevi F.Carrier a ^ s)
            (y : Coinvariants ρ (B.unipotentSubgroup F.Carrier)) := by
      intro k
      obtain ⟨⟨l, m, u⟩, hprod⟩ := hfac.1.2 k⁻¹
      have h1 : l.val * m.val * u.val = k.val⁻¹ := congrArg Subtype.val hprod
      have heq : k.val = u.val⁻¹ * (m.val⁻¹ * l.val⁻¹) := by
        rw [← inv_inv k.val, ← h1]
        group
      rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        hs _ ((B.iwahoriLower F.Carrier K.toSubgroup).inv_mem l.property)]
      rw [mk_apply_subgroup ρ (B.unipotentSubgroup F.Carrier)
        ⟨u.val⁻¹, (B.unipotentSubgroup F.Carrier).inv_mem u.property.2⟩]
      exact hlevi _ ((B.iwahoriLevi F.Carrier K.toSubgroup).inv_mem m.property)
    apply hpow s
    obtain ⟨t, ht⟩ := hsplit ⟨Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier a ^ s) v),
      Compact.averageMap_mem_fixedVectors ρ hρ K hK _⟩
    exact ⟨t, ht.trans
      (map_averageMap_of_forall_eq ρ hρ K hK (mk ρ (B.unipotentSubgroup F.Carrier)) _ _ hconst)⟩

/-- The exact published bijectivity clause, with its full telescope. -/
theorem blockStableImageJacquetBijective (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    BlockStableImageJacquetBijectiveClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  exact stableImageJacquetMap_bijective_of_finiteDimensional F T B V ρ hAdmissible.1 K hK
    (hAdmissible.2 K) hfac a ha

/-- Both core canonical-lift clauses, combining the published kernel proof with
the bijectivity proof above. -/
theorem blockCanonicalLift (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    BlockCanonicalLiftStatement F T B V :=
  ⟨blockPowerKernelJacquet F T B V, blockStableImageJacquetBijective F T B V⟩

end Block

end Langlands.Jacquet
