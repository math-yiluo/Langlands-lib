import Langlands.Representation.Jacquet.StableImageAverageBridgeStatement
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.Representation.Jacquet.StablePairingProof
import Langlands.Group.GL.BlockContractionProof

/-!
# Geometric averaging bridge for nested factorizing compact subgroups

For nested compact open subgroups `K₁ ≤ K₀` with block Iwahori factorization
and a strictly contracting block scalar `A`, normalized `K₀`-averaging sends
the actual `K₁` stable image into the actual `K₀` stable image, and it
preserves the upper Jacquet class whenever that class is fixed by `K₀ ∩ M`.
-/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- One power of a strict block scalar conjugates the whole compact lower radical
intersection `K ∩ N⁻` into an arbitrary open subgroup `U`, uniformly in its
elements and for every larger exponent. -/
theorem exists_blockScalar_pow_inv_conj_iwahoriLower_mem :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (K U : OpenSubgroup (GeneralLinear n F.Carrier)),
      IsCompact (K : Set (GeneralLinear n F.Carrier)) →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∃ R : ℕ, ∀ s : ℕ, R ≤ s → ∀ l ∈ B.iwahoriLower F.Carrier K.toSubgroup,
        (B.blockScalar F.Carrier a ^ s)⁻¹ * l * B.blockScalar F.Carrier a ^ s ∈ U := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro K U hK a ha
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
  obtain ⟨R, hR⟩ := B.strictPowersEventuallyDeep T a ha ε hε
  refine ⟨R, fun s hs l hl => ?_⟩
  have hpow : B.blockScalar F.Carrier (fun i => a i ^ s) = B.blockScalar F.Carrier a ^ s :=
    map_pow (B.blockScalar F.Carrier) a s
  have hlU := (hc (fun i => a i ^ s) (hR s hs)).2 l hl
  rw [hpow] at hlU
  exact hlU

/-- Powers of a weakly contracting tuple remain weakly contracting. -/
theorem isWeaklyContracting_pow_of_averageBridge {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (r : ℕ) :
    B.IsWeaklyContracting T (a ^ r) := by
  induction r with
  | zero => simpa only [pow_zero] using B.isWeaklyContracting_one T
  | succ r hr =>
    simpa only [pow_succ] using GeneralLinear.BlockShape.IsWeaklyContracting.mul B T hr ha

/-- Powers of normalized block compression are compressions by powers of the
block scalar: `C^r x = e (ρ(A^r) x)` on fixed vectors. -/
theorem blockCompressedAction_pow_apply (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting T a →
      ∀ (r : ℕ) (x : fixedVectors ρ K.toSubgroup),
        ((compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) ^ r) x : V) =
          Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier a ^ r) (x : V)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac a ha r x
  have hpow : compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) ^ r =
      compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a ^ r)) := by
    induction r with
    | zero => simp only [pow_zero, map_one, compressedAction_one]; rfl
    | succ r hr =>
      rw [pow_succ, hr, pow_succ,
        blockCompressedAction_mul F T n B V ρ hρ K hK hfac _ _
          (isWeaklyContracting_pow_of_averageBridge F T B ha r) ha]
  rw [hpow, compressedAction_apply, map_pow]

/-- Reversed block Iwahori factorization: every element of `K` is a product
`u * m * l` of an upper, a Levi and a lower factor of `K`. -/
theorem exists_iwahori_reversed_factorization :
    letI := T.topology
    ∀ {K : OpenSubgroup (GeneralLinear n F.Carrier)},
      B.HasBlockIwahoriFactorization T K →
      ∀ k : K, ∃ u ∈ B.iwahoriUpper F.Carrier K.toSubgroup,
        ∃ m ∈ B.iwahoriLevi F.Carrier K.toSubgroup,
        ∃ l ∈ B.iwahoriLower F.Carrier K.toSubgroup, (k : GeneralLinear n F.Carrier) = u * m * l := by
  let := T.topology
  intro K hfac k
  obtain ⟨⟨l, m, u⟩, hprod⟩ := hfac.1.2 k⁻¹
  refine ⟨u.val⁻¹, inv_mem u.property, m.val⁻¹, inv_mem m.property,
    l.val⁻¹, inv_mem l.property, ?_⟩
  have hi := congrArg (fun x : K => (x : GeneralLinear n F.Carrier)⁻¹) hprod
  simpa only [GeneralLinear.BlockShape.iwahoriProduct_val,
    InvMemClass.coe_inv, inv_inv, mul_inv_rev, mul_assoc] using hi.symm


/-- A strict block-scalar translate is fixed by `K ∩ N⁻` once the conjugates of
`K ∩ N⁻` lie in a subgroup fixing the original vector. -/
theorem blockScalar_pow_apply_fixed_of_conj_mem (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (U : Subgroup (GeneralLinear n F.Carrier)) (x : fixedVectors ρ U)
    (g : GeneralLinear n F.Carrier) (l : GeneralLinear n F.Carrier) (hl : g⁻¹ * l * g ∈ U) :
    ρ l (ρ g (x : V)) = ρ g (x : V) := by
  calc
    ρ l (ρ g (x : V)) = ρ g (ρ (g⁻¹ * l * g) (x : V)) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = ρ g (x : V) := congrArg (ρ g) (x.property ⟨_, hl⟩)

/-- Compression past the `K`-average of a vector fixed by `K ∩ N⁻`: for every
weakly contracting `b`, `e (ρ(b) (e y)) = e (ρ(b) y)`. -/
theorem averageMap_blockScalar_averageMap_of_lower_fixed
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ b : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting T b →
      ∀ y : V, (∀ l ∈ B.iwahoriLower F.Carrier K.toSubgroup, ρ l y = y) →
        Compact.averageMap ρ hρ K hK
            (ρ (B.blockScalar F.Carrier b) (Compact.averageMap ρ hρ K hK y)) =
          Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier b) y) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac b hb y hy
  apply map_averageMap_of_forall_eq ρ hρ K hK
    ((Compact.averageMap ρ hρ K hK).comp (ρ (B.blockScalar F.Carrier b))) y
  intro k
  obtain ⟨u, hu, m, hm, l, hl, hk⟩ := exists_iwahori_reversed_factorization F T B hfac k
  have huK := (hfac.2 b hb).1 u hu
  have hcomm := blockScalar_mul_eq_of_mem_leviSubgroup F B b hm.2
  have he : B.blockScalar F.Carrier b * (k : GeneralLinear n F.Carrier) =
      (B.blockScalar F.Carrier b * u * (B.blockScalar F.Carrier b)⁻¹) *
        (B.blockScalar F.Carrier b * m) * l := by
    rw [hk]
    group
  rw [hcomm] at he
  change Compact.averageMap ρ hρ K hK
    (ρ (B.blockScalar F.Carrier b) (ρ (k : GeneralLinear n F.Carrier) y)) = _
  calc
    Compact.averageMap ρ hρ K hK
        (ρ (B.blockScalar F.Carrier b) (ρ (k : GeneralLinear n F.Carrier) y)) =
        Compact.averageMap ρ hρ K hK
          (ρ (B.blockScalar F.Carrier b * (k : GeneralLinear n F.Carrier)) y) := by
      rw [map_mul ρ, Module.End.mul_apply]
    _ = Compact.averageMap ρ hρ K hK
          (ρ (B.blockScalar F.Carrier b * u * (B.blockScalar F.Carrier b)⁻¹)
            (ρ m (ρ (B.blockScalar F.Carrier b) (ρ l y)))) := by
      rw [he, map_mul ρ _ l, map_mul ρ _ (m * B.blockScalar F.Carrier b),
        map_mul ρ m]
      rfl
    _ = Compact.averageMap ρ hρ K hK (ρ (B.blockScalar F.Carrier b) y) := by
      rw [hy l hl, averageMap_apply_of_mem ρ hρ K hK huK.1,
        averageMap_apply_of_mem ρ hρ K hK hm.1]

/-- Finite-orbit averaging over `K` preserves the upper Jacquet class of a
vector fixed by `K ∩ N⁻` whose class is fixed by `K ∩ M`. -/
theorem mk_averageMap_eq_of_lower_fixed (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ y : V, (∀ l ∈ B.iwahoriLower F.Carrier K.toSubgroup, ρ l y = y) →
        mk ρ (B.unipotentSubgroup F.Carrier) y ∈
          fixedVectors (action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))
            (K.toSubgroup.comap (B.leviSubgroup F.Carrier).subtype) →
        mk ρ (B.unipotentSubgroup F.Carrier) (Compact.averageMap ρ hρ K hK y) =
          mk ρ (B.unipotentSubgroup F.Carrier) y := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac y hy hfix
  apply map_averageMap_of_forall_eq ρ hρ K hK (mk ρ (B.unipotentSubgroup F.Carrier)) y
  intro k
  obtain ⟨u, hu, m, hm, l, hl, hk⟩ := exists_iwahori_reversed_factorization F T B hfac k
  rw [hk, map_mul ρ (u * m) l, map_mul ρ u m, Module.End.mul_apply, Module.End.mul_apply,
    hy l hl]
  calc
    mk ρ (B.unipotentSubgroup F.Carrier) (ρ u (ρ m y)) =
        mk ρ (B.unipotentSubgroup F.Carrier) (ρ m y) :=
      mk_apply_subgroup ρ (B.unipotentSubgroup F.Carrier) ⟨u, hu.2⟩ (ρ m y)
    _ = mk ρ (B.unipotentSubgroup F.Carrier) y := hfix ⟨⟨m, hm.2⟩, hm.1⟩

/-- Clause (a): the normalized `K₀`-average of an actual `K₁` stable-image vector
lies in the actual `K₀` stable image of the same strict block scalar. -/
theorem blockStableImage_averageMap_mem_stableImage
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K1 K0 : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK1 : IsCompact (K1 : Set (GeneralLinear n F.Carrier)))
      (hK0 : IsCompact (K0 : Set (GeneralLinear n F.Carrier))),
      K1 ≤ K0 →
      B.HasBlockIwahoriFactorization T K1 →
      B.HasBlockIwahoriFactorization T K0 →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∀ w : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a),
        (⟨Compact.averageMap ρ hρ K0 hK0
            (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w),
          Compact.averageMap_mem_fixedVectors ρ hρ K0 hK0 _⟩ :
            fixedVectors ρ K0.toSubgroup) ∈
          stableImage ρ hρ K0 hK0 (B.blockScalar F.Carrier a) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K1 K0 hK1 hK0 hle hfac1 hfac0 a ha w
  obtain ⟨R, hR⟩ := exists_blockScalar_pow_inv_conj_iwahoriLower_mem F T B K0 K1 hK0 a ha
  rw [mem_stableImage]
  intro m
  obtain ⟨x, hx⟩ := (mem_stableImage ρ hρ K1 hK1 _ _).mp w.property (R + m)
  have hylow : ∀ l ∈ B.iwahoriLower F.Carrier K0.toSubgroup,
      ρ l (ρ (B.blockScalar F.Carrier a ^ R) (x : V)) =
        ρ (B.blockScalar F.Carrier a ^ R) (x : V) := fun l hl =>
    blockScalar_pow_apply_fixed_of_conj_mem F V ρ K1.toSubgroup x _ l (hR R le_rfl l hl)
  have hw : (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w : V) =
      Compact.averageMap ρ hρ K1 hK1
        (ρ (B.blockScalar F.Carrier a ^ (R + m)) (x : V)) := by
    change ((w : fixedVectors ρ K1.toSubgroup) : V) = _
    rw [← hx, blockCompressedAction_pow_apply F T B V ρ hρ K1 hK1 hfac1 a ha.weak]
  refine ⟨⟨Compact.averageMap ρ hρ K0 hK0 (ρ (B.blockScalar F.Carrier a ^ R) (x : V)),
    Compact.averageMap_mem_fixedVectors ρ hρ K0 hK0 _⟩, ?_⟩
  apply Subtype.ext
  rw [blockCompressedAction_pow_apply F T B V ρ hρ K0 hK0 hfac0 a ha.weak m]
  change Compact.averageMap ρ hρ K0 hK0
      (ρ (B.blockScalar F.Carrier a ^ m)
        (Compact.averageMap ρ hρ K0 hK0 (ρ (B.blockScalar F.Carrier a ^ R) (x : V)))) =
    Compact.averageMap ρ hρ K0 hK0
      (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w)
  have hAm : B.blockScalar F.Carrier a ^ m = B.blockScalar F.Carrier (a ^ m) :=
    (map_pow (B.blockScalar F.Carrier) a m).symm
  rw [hAm, averageMap_blockScalar_averageMap_of_lower_fixed F T B V ρ hρ K0 hK0 hfac0
      (a ^ m) (isWeaklyContracting_pow_of_averageBridge F T B ha.weak m) _ hylow,
    ← hAm, hw, averageMap_averageMap_of_le ρ hρ K0 K1 hK0 hK1 hle,
    add_comm R m, pow_add, map_mul ρ, Module.End.mul_apply]

/-- Clause (b): if the upper Jacquet class of an actual `K₁` stable-image vector
is fixed by `K₀ ∩ M` under the unnormalized quotient action, then normalized
`K₀`-averaging preserves that class. -/
theorem blockStableImage_mk_averageMap_eq
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K1 K0 : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK1 : IsCompact (K1 : Set (GeneralLinear n F.Carrier)))
      (hK0 : IsCompact (K0 : Set (GeneralLinear n F.Carrier))),
      K1 ≤ K0 →
      B.HasBlockIwahoriFactorization T K1 →
      B.HasBlockIwahoriFactorization T K0 →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∀ w : stableImage ρ hρ K1 hK1 (B.blockScalar F.Carrier a),
        mk ρ (B.unipotentSubgroup F.Carrier)
            (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w) ∈
          fixedVectors (action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))
            (K0.toSubgroup.comap (B.leviSubgroup F.Carrier).subtype) →
        mk ρ (B.unipotentSubgroup F.Carrier)
            (Compact.averageMap ρ hρ K0 hK0
              (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w)) =
          mk ρ (B.unipotentSubgroup F.Carrier)
            (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K1 K0 hK1 hK0 hle hfac1 hfac0 a ha w hfix
  obtain ⟨R, hR⟩ := exists_blockScalar_pow_inv_conj_iwahoriLower_mem F T B K0 K1 hK0 a ha
  obtain ⟨x, hx⟩ := (mem_stableImage ρ hρ K1 hK1 _ _).mp w.property R
  have hylow : ∀ l ∈ B.iwahoriLower F.Carrier K0.toSubgroup,
      ρ l (ρ (B.blockScalar F.Carrier a ^ R) (x : V)) =
        ρ (B.blockScalar F.Carrier a ^ R) (x : V) := fun l hl =>
    blockScalar_pow_apply_fixed_of_conj_mem F V ρ K1.toSubgroup x _ l (hR R le_rfl l hl)
  have hw : (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w : V) =
      Compact.averageMap ρ hρ K1 hK1 (ρ (B.blockScalar F.Carrier a ^ R) (x : V)) := by
    change ((w : fixedVectors ρ K1.toSubgroup) : V) = _
    rw [← hx, blockCompressedAction_pow_apply F T B V ρ hρ K1 hK1 hfac1 a ha.weak]
  -- The published compressed quotient law identifies the two classes.
  have hclass : mk ρ (B.unipotentSubgroup F.Carrier)
        (stableImageToRepresentation ρ hρ K1 hK1 (B.blockScalar F.Carrier a) w) =
      mk ρ (B.unipotentSubgroup F.Carrier) (ρ (B.blockScalar F.Carrier a ^ R) (x : V)) := by
    have hq := blockCompressedAction_mk F T n B V ρ hρ K1 hK1 hfac1 (a ^ R)
      (isWeaklyContracting_pow_of_averageBridge F T B ha.weak R) x
    have hpowC : compressedAction ρ hρ K1 hK1 (B.blockScalar F.Carrier (a ^ R)) x =
        (compressedAction ρ hρ K1 hK1 (B.blockScalar F.Carrier a) ^ R) x := by
      apply Subtype.ext
      rw [blockCompressedAction_pow_apply F T B V ρ hρ K1 hK1 hfac1 a ha.weak,
        compressedAction_apply, map_pow (B.blockScalar F.Carrier) a R]
    rw [hpowC, hx, action_mk] at hq
    change mk ρ (B.unipotentSubgroup F.Carrier) ((w : fixedVectors ρ K1.toSubgroup) : V) = _
    rw [hq]
    change mk ρ (B.unipotentSubgroup F.Carrier)
      (ρ (B.blockScalar F.Carrier (a ^ R)) (x : V)) = _
    rw [map_pow (B.blockScalar F.Carrier) a R]
  rw [hclass] at hfix
  rw [hw, averageMap_averageMap_of_le ρ hρ K0 K1 hK0 hK1 hle,
    mk_averageMap_eq_of_lower_fixed F T B V ρ hρ K0 hK0 hfac0 _ hylow hfix, ← hw, hclass]

/-- The exact published geometric stable-image averaging bridge. -/
theorem blockStableImageAverageBridge (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    BlockStableImageAverageBridgeStatement F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K1 K0 hK1 hK0 hle hfac1 hfac0 a ha w v e0 N M hMN
  exact ⟨blockStableImage_averageMap_mem_stableImage F T B V ρ hρ K1 K0 hK1 hK0
      hle hfac1 hfac0 a ha w,
    blockStableImage_mk_averageMap_eq F T B V ρ hρ K1 K0 hK1 hK0
      hle hfac1 hfac0 a ha w⟩

end Langlands.Jacquet
