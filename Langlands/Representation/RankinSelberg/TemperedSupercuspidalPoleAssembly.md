# Assembling a supercuspidal pole from a square-integrable block

Author: Worker 1779.

This internal support module supplies conditional steps in the proof of
`TemperedTwistSupercuspidalPoleStatement`. It does not prove that statement.
The JPSS (8.1)(ii), (8.2) and (8.4) proposition targets remain explicit
hypotheses. The provenance is their combination through the Library's
existing L-polynomial uniqueness, determinant-twist and normalized-induction
equivalences. No new external mathematical result is introduced.

The namespace `TemperedSupercuspidalPoleAssembly` contains the following.

- `HasPadicRankPoleAtZero` packages existence of a polynomial with the full
  `IsPadicRankLPolynomial` certificate for a given pair and self-dual Haar
  measure, together with a root at `1`. The source and partner ranks and
  carrier universes are independent. This is a proposition definition,
  without any existence assertion.
- `isRoot_one_of_contragredient` and
  `exists_isRoot_one_of_contragredient` apply
  `SupercuspidalEqualRankLFactorStatement` to an irreducible supercuspidal
  representation and an irreducible representation of Whittaker type of
  equal rank. An explicit equivalence to the second representation's smooth
  contragredient places `1` in the finite twist parameter set, by the
  published `one_mem_iff_of_supercuspidalTwistSet`. Thus the denominator
  product contains `1 - X` and vanishes at `1`. Uniqueness transfers this
  root to any certified polynomial for that pair; the existence version
  also supplies the certificate from (8.1)(ii).
- `isIrreducibleComponent_of_equiv` realizes an equivalent irreducible
  representation as a quotient of the whole subrepresentation.
  `centeredSegment_zero_component` uses the published one-block evaluation
  equivalence and the zero real twist to construct the component
  certificate for a centered segment of length one.
- `exists_squareIntegrable_isRoot_one` applies
  `SquareIntegrableLFactorStatement` to an essentially square-integrable
  component of a centered segment, paired with an irreducible
  supercuspidal representation that is explicitly assumed essentially
  square-integrable and of Whittaker type. Its centered segment has length
  one, so the product in (8.2) has one factor. The equivalence of the first
  centered block to the partner's smooth contragredient supplies a root by
  (8.1)(ii). The block-rank identity gives the rank inequality needed by
  (8.2).
- `exists_induced_isRoot_one` applies
  `TemperedLFactorStatement.commonRealTwistsOfEquiv` to square-integrable
  blocks and a smooth square-integrable seed considered as a one-block
  induction. Smoothness of the seed is an explicit input for this
  equivalence; it is not inferred from square-integrability.
  Both families may have arbitrary common real twists. A supplied certified
  polynomial for one selected block pair, with a root at `1`, equals the
  corresponding product factor by L-polynomial uniqueness. Evaluation of
  the finite product then gives a root for the whole induced pair. The
  actual equivalence to the requested representation and the complete
  L-polynomial certificate are retained.

In particular, the product result permits a partner that is a real twist of
a square-integrable seed, without asserting that the twisted partner itself
is square-integrable. The square-integrable result keeps the segment
component, supercuspidality, essential square-integrability, Whittaker type
and contragredient equivalence as visible inputs. Constructing these inputs
from tempered classification, producing a partner in an arbitrary carrier
universe, and discharging the JPSS formula propositions remain separate
obligations.
