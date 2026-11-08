import Langlands.Representation.RankinSelberg.HighlyRamified.RankReduction
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Classification.SegmentHeadProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentProductConcatenation
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Whittaker.Transport
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.AdjacentRankCoefficientTransport
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Classification.SegmentProductOrderedAssembly

/-!
# Genericity of `A × μ_z` for all but finitely many `z`

This module proves `PairInductionGenericity`, the genericity input of the rank
reduction in `HighlyRamified.RankReduction`: for a generic representation `A` of
`GL_(n+1)(F)`, the induced representation `A × μ_z` is generic for all but finitely
many `z : ℂˣ`, where `μ_z` is the unramified character `x ↦ z ^ ord(x)` of `GL_1(F)`.

By `GenericSegmentProductExhaustion` (Zelevinsky 1980, Theorem 9.7), `A` is
isomorphic to a product `i(d)` of segment heads over an unlinked multisegment.
Appending the one-term segment `{[μ_z]}` gives a datum whose product is `A × μ_z`;
it is again a product of segment heads, and its multisegment is unlinked unless
`[μ_z] = ν^k b(Δ)` for a segment `Δ` of `d` and `-1 ≤ k ≤ length Δ`. Since
`z ↦ [μ_z]` is injective, this excludes finitely many `z`, and the backward
direction of the exhaustion gives genericity of `A × μ_z` for the others.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open CategoryTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime]

/-- A block shape of rank one has exactly one block. -/
theorem blockShape_one_length (B : BlockShape 1) : B.length = 1 := by
  have h := B.sum_eq
  have hle : B.length ≤ ∑ i, B.size i := by
    calc B.length = ∑ _i : Fin B.length, 1 := by simp
      _ ≤ ∑ i, B.size i := Finset.sum_le_sum fun i _ => B.positive i
  rcases Nat.eq_zero_or_pos B.length with h0 | h0
  · have hz : (∑ i, B.size i) = 0 :=
      Finset.sum_eq_zero fun i _ => absurd i.isLt (by omega)
    omega
  · omega

/-- An admissible representation of `GL_1` is supercuspidal: every block parabolic
of `GL_1` is the whole group. -/
theorem isSupercuspidal_rankOne {F : Type uF} [Field F] [TopologicalSpace F]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Langlands.GeneralLinear 1 F) V} (hρ : IsAdmissible ρ) :
    IsSupercuspidal ρ :=
  ⟨hρ, fun B hB => absurd (B.singleBlock_parabolic_eq_top (blockShape_one_length B) F) hB⟩

/-- The rank-one character `μ_z` is admissible. -/
theorem isAdmissible_unramifiedRankOne (F : PadicField.{uF} p) (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    IsAdmissible (unramifiedRankOne.{uF, uX} F z).representation :=
  (padicUnitaryAdditiveCharacterExists F F.canonicalTopologicalData).elim fun ψ =>
    (rankOneExtensionCharacter_isOfWhittakerType.{uF, uX} F ψ
      (F.canonicalTopologicalData.unramifiedCharacterContinuous z)).1

/-- The rank-one character `μ_z` as a supercuspidal representation of `GL_1`. -/
def unramifiedSupercuspidal (F : PadicField.{uF} p) (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    SupercuspidalRep.{uF, uX} (F := F.Carrier) (n := 1) :=
  letI := F.canonicalTopologicalData.topology
  ⟨unramifiedRankOne.{uF, uX} F z,
    Classification.UnlinkedSegmentSocleProductIrreducibleProof.isIrreducible_of_finrank_eq_one
      (unramifiedRankOne.{uF, uX} F z).representation finrank_ulift_complex,
    isSupercuspidal_rankOne (isAdmissible_unramifiedRankOne.{uF, uX} F z)⟩

/-- The cuspidal datum `[μ_z]` of rank one. -/
def unramifiedCuspidalDatum (F : PadicField.{uF} p) (z : ℂˣ) :
    F.canonicalTopologicalData.CuspidalDatum.{uX, uF} :=
  letI := F.canonicalTopologicalData.topology
  ⟨1, Nat.one_pos, (unramifiedSupercuspidal.{uF, uX} F z).isoClass⟩

/-- Distinct `z` give distinct cuspidal data: an isomorphism `μ_z ≅ μ_w` carries the
scalar character of `μ_w` to `μ_z`, and evaluation at a uniformizer recovers `z`. -/
theorem unramifiedCuspidalDatum_injective (F : PadicField.{uF} p) :
    Function.Injective (unramifiedCuspidalDatum.{uF, uX} F) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  intro z w h
  have h' := eq_of_heq (PadicField.TopologicalData.CuspidalDatum.mk.inj h).2
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff _ _).mp h'
  let E := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier) (n := 1)).ι.mapIso e)
  have hw := hasScalarCharacter_unramifiedRankOne.{uF, uX} F w
  have hz := hasScalarCharacter_unramifiedRankOne.{uF, uX} F z
  have hw' := hw.of_injective E.toIntertwiningMap (fun a b hab => E.toLinearEquiv.injective hab)
  have h1 := congrArg ULift.down
    ((hz T.uniformizerUnit (ULift.up 1)).symm.trans (hw' T.uniformizerUnit (ULift.up 1)))
  have key : ∀ u : ℂˣ, (((F.canonicalTopologicalData.unramifiedCharacter u).comp
      (determinant (n := 1))).comp (GeneralLinear.scalar (n := 1))) T.uniformizerUnit = u := by
    intro u
    change F.canonicalTopologicalData.unramifiedCharacter u (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 1) T.uniformizerUnit)) = u
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_one]
    exact F.canonicalTopologicalData.unramifiedCharacter_uniformizer u
  have h2 : (((((F.canonicalTopologicalData.unramifiedCharacter z).comp
      (determinant (n := 1))).comp (GeneralLinear.scalar (n := 1))) T.uniformizerUnit : ℂˣ) : ℂ) =
      (((((F.canonicalTopologicalData.unramifiedCharacter w).comp
      (determinant (n := 1))).comp (GeneralLinear.scalar (n := 1))) T.uniformizerUnit : ℂˣ) : ℂ) :=
    (mul_one _).symm.trans (h1.trans (mul_one _))
  rw [key, key] at h2
  exact Units.ext h2


section Segments

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

open PadicField.TopologicalData

/-- Integral twist freeness: distinct natural twists of a cuspidal datum differ. -/
theorem twist_natCast_injective
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (β : T.CuspidalDatum.{uV, uF}) {a b : ℕ}
    (h : β.twist (a : ℝ) = β.twist (b : ℝ)) : a = b := by
  have hk : (β.twist (b : ℝ)).twist (((a : ℤ) - b : ℤ) : ℝ) = β.twist (b : ℝ) := by
    rw [CuspidalDatum.twist_twist]
    convert h using 2
    push_cast
    ring
  have := (hfree _ _).mp hk
  omega

/-- The support of the one-term segment `{ρ}` is `{ρ}`. -/
theorem mem_support_singletonSegment {ρ σ : T.CuspidalDatum.{uV, uF}} :
    σ ∈ (T.singletonSegment ρ).support ↔ σ = ρ := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    change i < 1 at hi
    obtain rfl : i = 0 := by omega
    exact Segment.member_zero _
  · rintro rfl
    exact (T.singletonSegment σ).base_mem_support

/-- If the one-term segment `{ρ}` is linked with `Δ`, then `ρ = ν^k b(Δ)` with
`-1 ≤ k ≤ length Δ`: the union of `{ρ}` and `Δ` is a segment, so `ρ` is adjacent to
`Δ`. -/
theorem exists_twist_of_singletonSegment_isLinked
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {ρ : T.CuspidalDatum.{uV, uF}} {Δ : T.Segment.{uV, uF}}
    (h : (T.singletonSegment ρ).IsLinked Δ) :
    ∃ k ∈ Set.Icc (-1 : ℤ) Δ.length, ρ = Δ.base.twist (k : ℝ) := by
  obtain ⟨h1, -, Δ', hΔ'⟩ := h
  have hρ : ρ ∉ Δ.support := fun hρ => h1 fun σ hσ => by
    rw [mem_support_singletonSegment.mp hσ]
    exact hρ
  have hsub : ∀ σ, σ ∈ Δ'.support ↔ σ = ρ ∨ σ ∈ Δ.support := by
    intro σ
    rw [hΔ', Set.mem_union, mem_support_singletonSegment]
  obtain ⟨i₀, hi₀, hb⟩ := (hsub Δ.base).mpr (Or.inr Δ.base_mem_support)
  obtain ⟨j₀, hj₀, hr⟩ := (hsub ρ).mpr (Or.inl rfl)
  have hother : ∀ i < Δ'.length, i ≠ j₀ → i₀ ≤ i ∧ i < i₀ + Δ.length := by
    intro i hi hij
    rcases (hsub _).mp (Δ'.member_mem_support hi) with h | ⟨l, hl, hle⟩
    · exact absurd (twist_natCast_injective hfree Δ'.base (h.trans hr.symm)) hij
    · have heq : Δ'.base.twist (((l + i₀ : ℕ)) : ℝ) = Δ'.base.twist (i : ℝ) := by
        have h' : Δ'.base.twist (((l + i₀ : ℕ)) : ℝ) =
            (Δ'.base.twist (i₀ : ℝ)).twist (l : ℝ) := by
          rw [CuspidalDatum.twist_twist, Nat.cast_add]
        rw [h']
        change (Δ'.member i₀).twist (l : ℝ) = Δ'.member i
        rw [hb]
        exact hle
      have := twist_natCast_injective hfree Δ'.base heq
      omega
  have hne : i₀ ≠ j₀ := by
    rintro rfl
    have hρb : ρ = Δ.base := hr.symm.trans hb
    exact hρ (hρb ▸ Δ.base_mem_support)
  have hlow : i₀ ≤ j₀ + 1 := by
    by_contra hcon
    have := hother (i₀ - 1) (by omega) (by omega)
    omega
  have hhigh : j₀ ≤ i₀ + Δ.length := by
    by_contra hcon
    have := hother (i₀ + Δ.length) (by omega) (by omega)
    omega
  refine ⟨(j₀ : ℤ) - i₀, ⟨by omega, by omega⟩, ?_⟩
  rw [← hr, ← hb]
  change Δ'.base.twist (j₀ : ℝ) = (Δ'.base.twist (i₀ : ℝ)).twist _
  rw [CuspidalDatum.twist_twist]
  congr 1
  push_cast
  ring

/-- A one-term segment with a saturated supercuspidal representative as block is a
segment head: the induced representation of `{ρ}` is `ρ` itself. -/
theorem singletonSegment_isSegmentHead (ρ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    T.IsSegmentHead (T.singletonSegment ρ)
      (T.castRank (T.singletonSegment_degree ρ).symm A.obj) := by
  let := T.topology
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (T.singletonSegment_degree ρ).symm A.obj A.property.1
  exact ⟨A, hA, (Classification.isIrreducibleHead_iff_of_equiv e).mpr
    (Classification.isIrreducibleHead_self _ hB)⟩

end Segments

section Pair

variable (F : PadicField.{uF} p)

open PadicField.TopologicalData

/-- The one-segment datum `{[μ_z]}` of rank one, with block `μ_z`. -/
def unramifiedSingletonDatum (z : ℂˣ) :
    F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} 1 :=
  letI := F.canonicalTopologicalData.topology
  { length := 1
    segments := fun _ => F.canonicalTopologicalData.singletonSegment
      (unramifiedCuspidalDatum.{uF, max uF uX} F z)
    degree_sum := Fin.sum_univ_one _
    blocks := fun _ => F.canonicalTopologicalData.castRank
      (F.canonicalTopologicalData.singletonSegment_degree _).symm
      (unramifiedRankOne.{uF, max uF uX} F z) }

/-- The block of `{[μ_z]}` is a segment head. -/
theorem unramifiedSingletonDatum_hasSegmentHeads (z : ℂˣ) :
    (unramifiedSingletonDatum.{uF, uX} F z).HasSegmentHeads :=
  fun _ => singletonSegment_isSegmentHead (unramifiedCuspidalDatum.{uF, max uF uX} F z)
    (unramifiedSupercuspidal.{uF, max uF uX} F z) (by exact rfl)

/-- The product of the datum `{[μ_z]}` is `μ_z`. -/
def unramifiedSingletonDatumEquiv (z : ℂˣ) :
    letI := F.canonicalTopologicalData.topology
    (unramifiedRankOne.{uF, uX} F z).representation.Equiv
      (unramifiedSingletonDatum.{uF, uX} F z).induced.representation :=
  letI := F.canonicalTopologicalData.topology
  (rankOneExtensionCharacterUniverseEquiv.{uF, uX, max uF uX} F
    (F.canonicalTopologicalData.unramifiedCharacterContinuous z)).trans
    (SmoothRep.equivOfIso (Classification.SegmentProductOrderedAssembly.singletonIso
      (unramifiedSingletonDatum.{uF, uX} F z) rfl ⟨0, Nat.one_pos⟩)).symm

/-- Every segment of `{[μ_z]}` is `{[μ_z]}`. -/
theorem mem_unramifiedSingletonDatum_multisegment {z : ℂˣ}
    {Δ : F.canonicalTopologicalData.Segment.{max uF uX, uF}}
    (h : Δ ∈ (unramifiedSingletonDatum.{uF, uX} F z).multisegment) :
    Δ = F.canonicalTopologicalData.singletonSegment
      (unramifiedCuspidalDatum.{uF, max uF uX} F z) := by
  obtain ⟨_, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp h)
  rfl

/-- The two inner data `(d, s)` over the block shape `(n + 1, 1)`. -/
def pairDatum {n : ℕ}
    (d : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} (n + 1))
    (s : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} 1) :
    ∀ k, F.canonicalTopologicalData.SegmentProductDatum.{uV, uF}
      ((succBlockShape (pairSizes n) (pairSizes_sum n)).size k) :=
  Fin.cases d (Fin.cases s finZeroElim)

variable {F} in
/-- Both inner data of `(d, s)` are products of segment heads when `d` and `s` are. -/
theorem pairDatum_hasSegmentHeads {n : ℕ}
    {d : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} (n + 1)}
    {s : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} 1}
    (hd : d.HasSegmentHeads) (hs : s.HasSegmentHeads) :
    ∀ k, (pairDatum F d s k).HasSegmentHeads := by
  intro k
  induction k using Fin.cases with
  | zero => exact hd
  | succ k =>
    induction k using Fin.cases with
    | zero => exact hs
    | succ k => exact k.elim0

variable {F} in
/-- A segment of an inner datum of `(d, s)` is a segment of `d` or of `s`. -/
theorem mem_pairDatum_multisegment {n : ℕ}
    {d : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} (n + 1)}
    {s : F.canonicalTopologicalData.SegmentProductDatum.{uV, uF} 1}
    {k : Fin (succBlockShape (pairSizes n) (pairSizes_sum n)).length}
    {Δ : F.canonicalTopologicalData.Segment.{uV, uF}}
    (h : Δ ∈ (pairDatum F d s k).multisegment) :
    Δ ∈ d.multisegment ∨ Δ ∈ s.multisegment := by
  induction k using Fin.cases with
  | zero => exact Or.inl h
  | succ k =>
    induction k using Fin.cases with
    | zero => exact Or.inr h
    | succ k => exact k.elim0

variable {F} in
/-- Transport an equivalence `ρ ≃ Y` of smooth representations along `π = ρ` and
`X = Y`. -/
def equivOfEq {m : ℕ}
    {π ρ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear m F.Carrier)}
    {X Y : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uX} ℂ (Langlands.GeneralLinear m F.Carrier)}
    (hπ : π = ρ) (hX : X = Y)
    (e : letI := F.canonicalTopologicalData.topology
      ρ.representation.Equiv Y.representation) :
    letI := F.canonicalTopologicalData.topology
    π.representation.Equiv X.representation := by
  subst hπ
  subst hX
  exact e

variable {F} in
/-- The block equivalences `A ≃ i(d)` and `B ≃ i(s)` as a family over the two
blocks of `(n + 1, 1)`. -/
def pairBlockEquiv {n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (d : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} (n + 1))
    (s : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} 1)
    (eA : letI := F.canonicalTopologicalData.topology
      A.representation.Equiv d.induced.representation)
    (eB : letI := F.canonicalTopologicalData.topology
      B.representation.Equiv s.induced.representation) :
    letI := F.canonicalTopologicalData.topology
    ∀ i, (pairFamily F A B i).representation.Equiv
      (pairDatum F d s i).induced.representation :=
  letI := F.canonicalTopologicalData.topology
  Fin.cases
    (equivOfEq (m := n + 1) (ρ := A) (Y := d.induced) (by exact rfl) (by exact rfl) eA)
    (Fin.cases
      (equivOfEq (m := 1) (ρ := B) (Y := s.induced) (by exact rfl) (by exact rfl) eB)
      finZeroElim)

variable {F} in
/-- `A × B` is the product of the concatenation of `(d, s)` when `A ≅ i(d)` and
`B ≅ i(s)`: regroup the outer product of the inner products into one flat product.
The data `d` and `s` are kept abstract here; unfolding concrete data inside the
inner products makes elaboration very slow. -/
def pairConcatenateEquiv {n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (d : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} (n + 1))
    (s : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} 1)
    (eA : letI := F.canonicalTopologicalData.topology
      A.representation.Equiv d.induced.representation)
    (eB : letI := F.canonicalTopologicalData.topology
      B.representation.Equiv s.induced.representation) :
    letI := F.canonicalTopologicalData.topology
    (pairInduced F A B).Equiv
      (PadicField.TopologicalData.SegmentProductDatum.concatenate
        (succBlockShape (pairSizes n) (pairSizes_sum n)) (pairDatum F d s)).induced.representation :=
  letI := F.canonicalTopologicalData.topology
  (F.canonicalTopologicalData.normalizedProductInducedEquiv _
      (pairBlockEquiv A B d s eA eB)).trans
    (PadicField.TopologicalData.SegmentProductDatum.concatenateInducedEquiv _ _)

end Pair

section Concatenate

variable {F : PadicField.{uF} p} {T : F.TopologicalData} {n : ℕ} (D : BlockShape n)
  (a : ∀ k, T.SegmentProductDatum.{uV, uF} (D.size k))

open PadicField.TopologicalData

/-- A concatenation of products of segment heads is a product of segment heads. -/
theorem concatenate_hasSegmentHeads (ha : ∀ k, (a k).HasSegmentHeads) :
    (SegmentProductDatum.concatenate D a).HasSegmentHeads :=
  fun l => ha (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2

/-- Every segment of a concatenation is a segment of one of the inner data. -/
theorem mem_concatenate_multisegment {Δ : T.Segment.{uV, uF}}
    (h : Δ ∈ (SegmentProductDatum.concatenate D a).multisegment) :
    ∃ k, Δ ∈ (a k).multisegment := by
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp h)
  exact ⟨(finSigmaFinEquiv.symm l).1,
    Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨(finSigmaFinEquiv.symm l).2, rfl⟩)⟩

end Concatenate

/-- `A × B` is generic when the concatenation of `(d, s)` has generic product, for
`A ≅ i(d)` and `B ≅ i(s)`. -/
theorem isGeneric_pairInduced_of_concatenate (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (d : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} (n + 1))
    (s : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} 1)
    (eA : letI := F.canonicalTopologicalData.topology
      A.representation.Equiv d.induced.representation)
    (eB : letI := F.canonicalTopologicalData.topology
      B.representation.Equiv s.induced.representation)
    (hgen : letI := F.canonicalTopologicalData.topology
      Whittaker.IsGeneric ψ (n + 1)
        (PadicField.TopologicalData.SegmentProductDatum.concatenate
          (succBlockShape (pairSizes n) (pairSizes_sum n))
          (pairDatum F d s)).induced.representation) :
    letI := F.canonicalTopologicalData.topology
    Whittaker.IsGeneric ψ (n + 1) (pairInduced F A B) :=
  letI := F.canonicalTopologicalData.topology
  (Whittaker.isGeneric_iff_of_equiv ψ (n + 1) (pairConcatenateEquiv A B d s eA eB)).mpr hgen

/-- `A × B` is generic when `A ≅ i(d)` and `B ≅ i(s)` for products `d` and `s` of
segment heads, `d` over an unlinked multisegment and `s` over copies of one segment
`Δ` linked with no segment of `d`: the concatenation of `(d, s)` is then a product
of segment heads over an unlinked multisegment, whose product is `A × B`, generic by the backward direction of
`genericSegmentProductExhaustion` (Ze80 Theorem 9.7). -/
theorem isGeneric_pairInduced_of_datum (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ}
    (A : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
    (B : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uX} ℂ (Langlands.GeneralLinear 1 F.Carrier))
    (d : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} (n + 1))
    (s : F.canonicalTopologicalData.SegmentProductDatum.{max uF uX, uF} 1)
    (eA : letI := F.canonicalTopologicalData.topology
      A.representation.Equiv d.induced.representation)
    (eB : letI := F.canonicalTopologicalData.topology
      B.representation.Equiv s.induced.representation)
    (hdh : d.HasSegmentHeads) (hdu : d.multisegment.IsUnlinked) (hsh : s.HasSegmentHeads)
    (Δ : F.canonicalTopologicalData.Segment.{max uF uX, uF})
    (hs : ∀ Δ' ∈ s.multisegment, Δ' = Δ)
    (hlink : ∀ Δ' ∈ d.multisegment, ¬ Δ.IsLinked Δ') :
    letI := F.canonicalTopologicalData.topology
    Whittaker.IsGeneric ψ (n + 1) (pairInduced F A B) := by
  let := F.canonicalTopologicalData.topology
  have hmem : ∀ Δ' ∈ (PadicField.TopologicalData.SegmentProductDatum.concatenate
      (succBlockShape (pairSizes n) (pairSizes_sum n)) (pairDatum F d s)).multisegment,
      Δ' ∈ d.multisegment ∨ Δ' = Δ := by
    intro Δ' hΔ'
    obtain ⟨k, hk⟩ := mem_concatenate_multisegment _ _ hΔ'
    exact (mem_pairDatum_multisegment hk).imp_right (hs Δ')
  have hcu : (PadicField.TopologicalData.SegmentProductDatum.concatenate
      (succBlockShape (pairSizes n) (pairSizes_sum n))
      (pairDatum F d s)).multisegment.IsUnlinked := by
    intro Δ₁ h₁ Δ₂ h₂
    rcases hmem Δ₁ h₁ with h₁ | rfl <;> rcases hmem Δ₂ h₂ with h₂ | rfl
    · exact hdu Δ₁ h₁ Δ₂ h₂
    · exact fun h => hlink Δ₁ h₁ h.symm
    · exact hlink Δ₂ h₂
    · exact fun h => h.1 subset_rfl
  exact isGeneric_pairInduced_of_concatenate F ψ A B d s eA eB
    ((Classification.genericSegmentProductExhaustion.{uF, uX} (F := F)
      F.canonicalTopologicalData ψ (n + 1) _).mpr
      ⟨_, concatenate_hasSegmentHeads _ _ (pairDatum_hasSegmentHeads hdh hsh), hcu,
        ⟨Iso.refl _⟩⟩)

/-- If `A` is generic, then `A × μ_z` is generic for all but finitely many `z`.
Write `A ≅ i(d)` as a product of segment heads for an unlinked multisegment `d`
(Ze80 Theorem 9.7(b)). Appending the segment `{[μ_z]}` gives a datum whose
product is `A × μ_z`; it is again a product of segment heads, and its multisegment
is unlinked unless `[μ_z] = ν^k b(Δ)` for some `Δ ∈ d` and `-1 ≤ k ≤ length Δ`.
That excludes finitely many `z`, since `z ↦ [μ_z]` is injective. -/
theorem pairInductionGenericity : PairInductionGenericity.{uF, uX} := by
  intro p' _ F ψ n A hA
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  have hA' : Whittaker.IsGeneric ψ n (SmoothRep.universeLift.{uF} A).representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ n (SmoothRep.universeLiftEquiv.{uF} A)).mp hA
  obtain ⟨d, hdh, hdu, ⟨e⟩⟩ :=
    (Classification.genericSegmentProductExhaustion.{uF, uX} (F := F) T ψ n
      (SmoothRep.universeLift.{uF} A)).mp hA'
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF, max uF uX} F T
  let S : Set ℂˣ := ⋃ i : Fin d.length, ⋃ k ∈ Set.Icc (-1 : ℤ) (d.segments i).length,
    {z | unramifiedCuspidalDatum.{uF, max uF uX} F z = (d.segments i).base.twist (k : ℝ)}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => (Set.finite_Icc _ _).biUnion fun k _ => ?_
    exact Set.Subsingleton.finite fun z hz w hw =>
      unramifiedCuspidalDatum_injective.{uF, max uF uX} F (hz.trans hw.symm)
  refine hS.subset fun z hz => ?_
  by_contra hzS
  apply hz
  refine isGeneric_pairInduced_of_datum F ψ A (unramifiedRankOne.{uF, uX} F z) d
    (unramifiedSingletonDatum.{uF, uX} F z)
    ((SmoothRep.universeLiftEquiv.{uF} A).trans (SmoothRep.equivOfIso e))
    (unramifiedSingletonDatumEquiv.{uF, uX} F z) hdh hdu
    (unramifiedSingletonDatum_hasSegmentHeads.{uF, uX} F z)
    (T.singletonSegment (unramifiedCuspidalDatum.{uF, max uF uX} F z))
    (fun _ h => mem_unramifiedSingletonDatum_multisegment.{uF, uX} F h) ?_
  intro Δ hΔ hl
  obtain ⟨k, hk, hρk⟩ := exists_twist_of_singletonSegment_isLinked hfree hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΔ)
  exact hzS (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨k, hk, hρk⟩⟩)

/-- The reduction of the target to adjacent ranks and rank one, with the genericity
input `PairInductionGenericity` discharged by `pairInductionGenericity`. -/
theorem highlyRamifiedGammaStability_of_adjacent_and_rankOne
    (hadj : ∀ n, PairStability.{uF, uV, uW} (n + 1) n)
    (hadjV : ∀ n, PairStability.{uF, max uF uV, uW} (n + 1) n)
    (hadjW : ∀ n, PairStability.{uF, uV, max uF uW} (n + 1) n)
    (hone : ∀ r, PairStability.{uF, uV, uW} r 0)
    (honeW : ∀ r, PairStability.{uF, uV, max uF uW} r 0) :
    HighlyRamifiedGammaStabilityStatement.{uF, uV, uW} :=
  highlyRamifiedGammaStability_of_adjacent_of_rankOne hadj hadjV hadjW hone honeW
    pairInductionGenericity.{uF, uV} pairInductionGenericity.{uF, max uF uV}
    pairInductionGenericity.{uF, uW} pairInductionGenericity.{uF, max uF uW}

end Langlands.RankinSelberg.HighlyRamified
