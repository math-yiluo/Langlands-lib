import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Correspondence.AssemblyRelation
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Correspondence.SupercuspidalEpsilonComparison
import Langlands.Representation.RankinSelberg.LanglandsFactorDescent

/-!
# Reduction of assembled epsilon inheritance to segment pairs

For a fixed local-constant system, pair epsilon compatibility of an assembled
full map follows from three explicit premises: Langlands data of multisegment
heads consist of segment heads, arithmetic pair epsilon factors are multiplicative
on direct sums of Weil–Deligne representations, and segment heads of the segments
`[c0 σ, …, ν^a c0 σ]` have the epsilon factors of the blocks `σ ⊗ Sp(a + 1)`.
None of the three premises is proved here.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor LocalFactor.CommonClosure PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyEpsilonFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyEpsilonGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Epsilon inheritance at a fixed local-constant system: if the supercuspidal
correspondence `c0` satisfies the supercuspidal pair-factor condition for the
system `(eC, ε, hε)`, then every assembly `c` of `c0` satisfies full pair epsilon
compatibility for the same system. -/
def AssemblyPairEpsilonSystemInheritance : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε),
    IsSupercuspidalCorrespondence F c0 → IsAssemblyOf F c0 c →
      SupercuspidalPairFactorCompatibility F eC ε hε c0 →
        FullPairEpsilonCompatibility F eC ε hε c

/-- `Q` is a model of the head of the segment `Δ` with carrier in the universe
`uA`: its rank is `deg Δ`, and after transport along that equality it is
equivalent to a representation `P` with carrier in `max uF uA` that is the
irreducible head of the induced representation of `Δ`. -/
def IsSegmentHeadModel (Δ : Segment.{uA, uF} F.canonicalTopologicalData) {n : ℕ}
    (Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  ∃ (h : n = Δ.degree)
    (P : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear Δ.degree F.Carrier)),
    F.canonicalTopologicalData.IsSegmentHead Δ P ∧
      Nonempty ((h ▸ Q).representation.Equiv P.representation)

/-- Square-integrable Langlands data of multisegment heads, with blocks in the
universe `uA`: if `J` is the Langlands head of the multisegment `{Δ_1, …, Δ_r}`,
then `J` is a Langlands quotient of some such datum, and the blocks of every such
datum are, after a permutation `φ`, models of the segment heads `Q(Δ_(φ k))`. -/
def MultisegmentHeadDatumMatching : Prop :=
  ∀ (r : ℕ) (Δ : Fin r → Segment.{uA, uF} F.canonicalTopologicalData) {n : ℕ}
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier)),
    Multisegment.IsLanglandsHead
        (List.ofFn Δ : Multisegment.{uA, uF} F.canonicalTopologicalData) J →
      (∃ d : SquareIntegrableLanglandsDatum.{uA, uF} F.canonicalTopologicalData n,
        d.IsLanglandsQuotient J) ∧
      ∀ d : SquareIntegrableLanglandsDatum.{uA, uF} F.canonicalTopologicalData n,
        d.IsLanglandsQuotient J →
          ∃ φ : Fin d.shape.length ≃ Fin r, ∀ k, IsSegmentHeadModel F (Δ (φ k)) (d.blocks k)

/-- Multiplicativity of arithmetic pair epsilon factors for the supplied system:
if `A ≅ ⊕_i B_i` and `A' ≅ ⊕_j B'_j` with `r, t > 0` summands, and `e_ij` is the
arithmetic epsilon factor of `B_i ⊗ B'_j`, then the product monomial of the `e_ij`
is the arithmetic epsilon factor of `A ⊗ A'`. -/
def ArithmeticPairEpsilonDirectSum (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε) :
    Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) {r t : ℕ}, 0 < r → 0 < t →
    ∀ (B : Fin r → Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
      (B' : Fin t → Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
      (A A' : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F)
      (e : Fin r → Fin t → ℂˣ × ℤ),
      Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B) A) →
      Nonempty (WeilDeligneRepresentation.Equiv (WeilDeligneRepresentation.directSum B') A') →
      (∀ i j, IsArithmeticPairEpsilonFactor F eC ε hε ψ
        (WeilDeligneRepresentation.classOf (B i)) (WeilDeligneRepresentation.classOf (B' j))
        (e i j).1 (e i j).2) →
      IsArithmeticPairEpsilonFactor F eC ε hε ψ (WeilDeligneRepresentation.classOf A)
        (WeilDeligneRepresentation.classOf A')
        (RankinSelberg.epsilonFactorProduct e).1 (RankinSelberg.epsilonFactorProduct e).2

/-- Segment-pair epsilon compatibility of `c0` for the supplied system: for
irreducible Weil classes `σ`, `τ` with representatives `B`, `B'`, and models
`Q`, `Q'` of the heads of the segments `[c0 σ, …, ν^a c0 σ]` and
`[c0 τ, …, ν^b c0 τ]`, one monomial is both the pair epsilon factor of `(Q, Q')`
for every self-dual `ν` and the arithmetic epsilon factor of the uncentered special
blocks `σ ⊗ Sp(a + 1)` and `τ ⊗ Sp(b + 1)`. -/
def SegmentPairEpsilonCompatibility (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
    ∀ {d a t b : ℕ} (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat)
      (τ : IrreducibleWeilClass.{uF, uP} F t.succPNat)
      (B B' : Weil.Local.LocalWeilRepresentation.{uF, uP} F),
      FiniteRepresentation.classOf B = weilClassForget F σ →
      FiniteRepresentation.classOf B' = weilClassForget F τ →
      ∀ {n n' : ℕ} (Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n F.Carrier))
        (Q' : SmoothRep.{0, uF, uA} ℂ (GeneralLinear n' F.Carrier)),
        IsSegmentHeadModel F (segmentOf F c0 σ a) Q →
        IsSegmentHeadModel F (segmentOf F c0 τ b) Q' →
        ∃ e : ℂˣ × ℤ,
          RankinSelberg.IsPadicRankEpsilonFactor F ψ ν Q.representation Q'.representation e ∧
          IsArithmeticPairEpsilonFactor F eC ε hε ψ
            (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
              (Weil.Local.localNormCharacter F).toMonoidHom B (a + 1)))
            (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
              (Weil.Local.localNormCharacter F).toMonoidHom B' (b + 1)))
            e.1 e.2

/-- A block shape of positive rank has a block. -/
private theorem blockShape_length_pos {n : ℕ} (s : GeneralLinear.BlockShape (n + 1)) :
    0 < s.length := by
  apply Nat.pos_of_ne_zero
  intro h
  have : IsEmpty (Fin s.length) := by rw [h]; infer_instance
  have hs := s.sum_eq
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
  omega

/-- Full pair epsilon compatibility of an assembly from the three premises and the
existence of self-dual measures. The epsilon factor of `(c D, c D')` is the product
of the segment-pair factors, indexed by the blocks of the decompositions chosen
for `D` and `D'`. -/
theorem fullPairEpsilonCompatibility_of_segmentPairs
    {eC : ReciprocityFamily F} {ε : NonabelianSystem.Assignment.{uF, uP} F}
    {hε : NonabelianSystem.IsSystem F eC ε} {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c : FullMap.{uF, uP, uA} F}
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hD : ArithmeticPairEpsilonDirectSum F eC ε hε)
    (hS : SegmentPairEpsilonCompatibility F eC ε hε c0)
    (hν : ∀ ψ : NontrivialAdditiveCharacter F,
      ∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν)
    (hc : IsAssemblyOf F c0 c) :
    FullPairEpsilonCompatibility F eC ε hε c := by
  intro ψ r t D D'
  refine ⟨hν ψ, fun ν hνψ => ?_⟩
  obtain ⟨k, dd, m, σ, ⟨B, AD, hB, hAD, ⟨hsum⟩⟩, A, J, hA, hJ, ⟨hJA⟩⟩ := hc r.succPNat D
  obtain ⟨k', dd', m', τ, ⟨B', AD', hB', hAD', ⟨hsum'⟩⟩, A', J', hA', hJ', ⟨hJA'⟩⟩ :=
    hc t.succPNat D'
  obtain ⟨⟨d0, hd0⟩, hmatch⟩ := hP k (fun i => segmentOf F c0 (σ i) (m i)) J hJ
  obtain ⟨⟨d0', hd0'⟩, hmatch'⟩ := hP k' (fun j => segmentOf F c0 (τ j) (m' j)) J' hJ'
  obtain ⟨φ0, hφ0⟩ := hmatch d0 hd0
  obtain ⟨φ0', hφ0'⟩ := hmatch' d0' hd0'
  have hk : 0 < k := by
    have := blockShape_length_pos (n := r) d0.shape
    rw [← Fintype.card_fin k, ← Fintype.card_congr φ0, Fintype.card_fin]
    exact this
  have hk' : 0 < k' := by
    have := blockShape_length_pos (n := t) d0'.shape
    rw [← Fintype.card_fin k', ← Fintype.card_congr φ0', Fintype.card_fin]
    exact this
  have hblock : ∀ i j, ∃ e : ℂˣ × ℤ, IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
        (Weil.Local.localNormCharacter F).toMonoidHom (B i) (m i + 1)))
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.block
        (Weil.Local.localNormCharacter F).toMonoidHom (B' j) (m' j + 1))) e.1 e.2 := by
    intro i j
    obtain ⟨l, rfl⟩ := φ0.surjective i
    obtain ⟨l', rfl⟩ := φ0'.surjective j
    obtain ⟨e, -, he⟩ := hS ψ ν hνψ (σ (φ0 l)) (τ (φ0' l')) (B _) (B' _) (hB _) (hB' _)
      _ _ (hφ0 l) (hφ0' l')
    exact ⟨e, he⟩
  choose E hE using hblock
  refine ⟨RankinSelberg.epsilonFactorProduct E,
    ⟨A, A', J, J', hA, hA', ⟨hJA⟩, ⟨hJA'⟩, ⟨d0, hd0⟩, ⟨d0', hd0'⟩, fun d d' hd hd' => ?_⟩, ?_⟩
  · obtain ⟨φ, hφ⟩ := hmatch d hd
    obtain ⟨φ', hφ'⟩ := hmatch' d' hd'
    refine ⟨fun l l' => E (φ l) (φ' l'), fun l l' => ?_,
      (RankinSelberg.epsilonFactorProduct_reindex φ φ' E).symm⟩
    obtain ⟨e, he, ha⟩ := hS ψ ν hνψ (σ (φ l)) (τ (φ' l')) (B (φ l)) (B' (φ' l'))
      (hB _) (hB' _) _ _ (hφ l) (hφ' l')
    obtain ⟨h1, h2⟩ := IsArithmeticPairEpsilonFactor.unique F ha (hE (φ l) (φ' l'))
    have heq : e = E (φ l) (φ' l') := Prod.ext h1 h2
    subst heq
    exact he
  · rw [← hAD, ← hAD']
    exact hD ψ hk hk' _ _ AD AD' E ⟨hsum⟩ ⟨hsum'⟩ hE

/-- Segment-level inheritance: whenever the supercuspidal correspondence `c0`
satisfies the supercuspidal pair-factor condition for a system, it satisfies
segment-pair epsilon compatibility for that system. -/
def SupercuspidalSegmentPairInheritance : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε),
    IsSupercuspidalCorrespondence F c0 → SupercuspidalPairFactorCompatibility F eC ε hε c0 →
      SegmentPairEpsilonCompatibility F eC ε hε c0

/-- Epsilon inheritance at every fixed system from multisegment datum matching,
arithmetic multiplicativity for every system, and segment-level inheritance. -/
theorem assemblyPairEpsilonSystemInheritance_of_segmentPairs
    (hP : MultisegmentHeadDatumMatching.{uF, uA} F)
    (hD : ∀ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
      (hε : NonabelianSystem.IsSystem F eC ε), ArithmeticPairEpsilonDirectSum F eC ε hε)
    (hS : SupercuspidalSegmentPairInheritance.{uF, uP, uA} F) :
    AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F := by
  intro c0 c eC ε hε hc0 hc hcompat
  exact fullPairEpsilonCompatibility_of_segmentPairs F hP (hD eC ε hε)
    (hS c0 eC ε hε hc0 hcompat) (hcompat.exists_selfDualMeasure F) hc

end Langlands.Correspondence
