import Langlands.Representation.Classification.TadicComplementarySeriesStatement
import Langlands.Representation.Classification.BernsteinUnitaryStatement
import Langlands.Representation.Classification.SpehUnitarizabilityStatement
import Langlands.Representation.Induction.BinaryProduct

/-!
# Tadic's local reduction of the unitarizability of Speh representations

Three properties of the Speh representations `u(delta, k)` of `GL_(k r)` over a
p-adic field, for an actual square-integrable `delta` of `GL_r`: irreducibility of
the complementary products `nu^alpha u(delta,k) x nu^(-alpha) u(delta,k)` for
`0 < |alpha| < 1/2`; for `k >= 2`, irreducibility of `u(delta,k+1) x u(delta,k-1)`;
and, when that product is irreducible, its occurrence as a subquotient of the end
point `nu^(1/2) u(delta,k) x nu^(-1/2) u(delta,k)`. With Tadic 1986,
Proposition 2.9, Bernstein's Theorem 2.5(i) and the weak form of 2.5(ii), and the
Hermitian property of Speh representations, they are the inputs of Tadic's local
induction for the unitarizability of `u(delta, k)` (Tadic 1986, Lemma 6.2;
Badulescu 2014, Theorem 1(b)). The last definition states that induction as an
implication. All assertions are proposition definitions; none is proved here.
-/

noncomputable section

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

namespace SpehDatum

variable {F T} (d : SpehDatum.{uF, uV} F T)

/-- The datum with the same rank `r` and square-integrable candidate `delta`,
and Speh length replaced by the positive integer `k`. -/
def withLength (k : ℕ) (hk : 0 < k) : SpehDatum.{uF, uV} F T where
  rank := d.rank
  rank_pos := d.rank_pos
  length := k
  length_pos := hk
  delta := d.delta

end SpehDatum

/-- For every discrete-series datum `d = (delta, k)`, every representative `S` of
`u(delta, k)` and every real `alpha` with `0 < |alpha| < 1/2`, the actual
complementary product `nu^alpha S x nu^(-alpha) S` on `GL_(2 k r)` is
irreducible. For `0 < |alpha| < 1/2` the cuspidal supports of the two factors
lie on different straight lines, so this is Zelevinsky 1980, Propositions 8.5
and 8.6, the step used in the proof of Tadic 1986, Proposition 4.2; see also
Badulescu 2014, Theorem 1(c) and its proof. -/
def SpehComplementaryIrreducibility : Prop :=
  letI := T.topology
  ∀ d : SpehDatum.{uF, uV} F T, d.IsDiscreteSeries →
    ∀ S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier),
      d.IsSpeh S → ∀ α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), α ≠ 0 →
        Representation.IsIrreducible (d.complementaryInduced S α).representation

/-- For every discrete-series datum `d = (delta, k)` with `k ≥ 2` and
representatives `Sup`, `Sdown` of `u(delta, k+1)` and `u(delta, k-1)`, the actual
normalized product `Sup x Sdown` on `GL_((k+1) r + (k-1) r)` is irreducible.
Badulescu 2014, Theorem 1(b), assertion (ii), and its proof. -/
def SpehNeighborProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (d : SpehDatum.{uF, uV} F T) (hk : 2 ≤ d.length), d.IsDiscreteSeries →
    ∀ (Sup : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength (d.length + 1) (Nat.succ_pos _)).degree F.Carrier))
      (Sdown : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)).degree
          F.Carrier)),
      (d.withLength (d.length + 1) (Nat.succ_pos _)).IsSpeh Sup →
        (d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)).IsSpeh Sdown →
        Representation.IsIrreducible
          ((T.binaryPositiveProductFunctor
            (Nat.mul_pos (Nat.succ_pos d.length) d.rank_pos)
            (Nat.mul_pos (Nat.sub_pos_of_lt hk) d.rank_pos)).obj
            (Sup, Sdown)).representation

/-- For every discrete-series datum `d = (delta, k)` with `k ≥ 2` and
representatives `S`, `Sup`, `Sdown` of `u(delta, k)`, `u(delta, k+1)` and
`u(delta, k-1)`: if the actual normalized product `Sup x Sdown` is irreducible,
then after the exact rank transport to `GL_(2 k r)` it is a subquotient of the
end point `nu^(1/2) S x nu^(-1/2) S` of the complementary series.
Tadic 1986, Proposition A.4(ii) and Corollary A.6(i), applied to the
multisegments `nu^(1/2) a(delta, k)` and `nu^(-1/2) a(delta, k)`, whose sum is
`a(delta, k+1) + a(delta, k-1)`. -/
def SpehNeighborProductEndpointSubquotient : Prop :=
  letI := T.topology
  ∀ (d : SpehDatum.{uF, uV} F T) (hk : 2 ≤ d.length), d.IsDiscreteSeries →
    ∀ (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
      (Sup : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength (d.length + 1) (Nat.succ_pos _)).degree F.Carrier))
      (Sdown : SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)).degree
          F.Carrier)),
      d.IsSpeh S → (d.withLength (d.length + 1) (Nat.succ_pos _)).IsSpeh Sup →
        (d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)).IsSpeh Sdown →
        Representation.IsIrreducible
            ((T.binaryPositiveProductFunctor
              (Nat.mul_pos (Nat.succ_pos d.length) d.rank_pos)
              (Nat.mul_pos (Nat.sub_pos_of_lt hk) d.rank_pos)).obj
              (Sup, Sdown)).representation →
          ∀ h : (d.withLength (d.length + 1) (Nat.succ_pos _)).degree +
              (d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)).degree = 2 * d.degree,
            SmoothRep.IsSubquotient
              (h ▸ (T.binaryPositiveProductFunctor
                (Nat.mul_pos (Nat.succ_pos d.length) d.rank_pos)
                (Nat.mul_pos (Nat.sub_pos_of_lt hk) d.rank_pos)).obj
                (Sup, Sdown))
              (d.complementaryInduced S (1 / 2))

/-- The three Speh inputs together. -/
def SpehUnitarityInputs : Prop :=
  SpehComplementaryIrreducibility.{uF, uV} F T ∧
    SpehNeighborProductIrreducibility.{uF, uV} F T ∧
      SpehNeighborProductEndpointSubquotient.{uF, uV} F T

/-- Tadic's local reduction: Tadic 1986, Proposition 2.9 (unitarity at the end
points of complementary series), Bernstein's Theorem 2.5(i) (irreducibility and
unitarity of unitary products), the weak form of 2.5(ii) (unitarity of Hermitian
factors of an irreducible unitarizable product) and the three Speh inputs imply
that every Speh representation `u(delta, k)` is unitarizable. Tadic 1986,
Lemma 6.2 with Appendix A.4 and A.6; Badulescu 2014, Theorem 1(b). -/
def SpehUnitarizabilityLocalReduction : Prop :=
  ComplementarySeriesUnitarity.{uF, uV} F T →
    BernsteinUnitaryProductIrreducibility.{uF, uV} F T →
      BernsteinUnitaryProductFactorUnitarity.{uF, uV} F T →
        SpehUnitarityInputs.{uF, uV} F T →
          SpehUnitarizability.{uF, uV} F T

end Langlands.Classification
