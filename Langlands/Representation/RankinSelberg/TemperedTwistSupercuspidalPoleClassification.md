# Classification inputs in the forms used by JPSS (8.2) and (8.4)

Authors: Worker 1722 (classification bridges), Worker 1779 (component
certificate and submission integration).

This internal support module is for the proof of
`TemperedTwistSupercuspidalPoleStatement`. It does not prove that statement.
It restates published classification results for `GL_n(F)` so that they match
the hypotheses of `SquareIntegrableLFactorStatement` (JPSS 1983, (8.2)) and
`TemperedLFactorStatement` (JPSS 1983, (8.4)) in
`TemperedLFactorStatement.lean`. The content is derived. It combines the
Library's segment classification (Zelevinsky 1980, §9), the
tempered block exhaustion proposition, the universe lift and normalized
induction equivalences. No new external result is introduced, and the module
introduces only a certificate packaging the centered-segment conclusion.

Throughout, `F : PadicField.{uF} p` with its canonical topological data
`T = F.canonicalTopologicalData`, `ν = α = |det|_F`, and normalized induction is
from the standard upper block parabolic.

## Declarations

- `HasCenteredSupercuspidalComponent F r σ` is the proposition that there
  exist `a`, `m`, the exact rank identity
  `∑ _ : Fin (m + 1), (a + 1) = r + 1`, and an irreducible supercuspidal
  smooth seed `π₀` whose centered normalized induction has `σ` as an
  irreducible component. The seed and `σ` have carriers in
  `Type (max uF uV)`. This certificate retains the rank identity and the
  actual induction; it does not assert a pole or construct a dual partner.
  `hasCenteredSupercuspidalComponent_of_essentiallySquareIntegrable`
  packages the output of
  `essentiallySquareIntegrableCenteredSegmentComponent`, under the same
  irreducibility and essential square-integrability hypotheses.

- `isIrreducibleComponent_of_injective`, imported from
  `Langlands.Representation.RankinSelberg.IrreducibleComponentEmbedding`: for any group `G`, an irreducible
  representation `π` with an injective intertwiner `j : π → ξ` is an
  irreducible component of `ξ` (`IsIrreducibleComponent ξ π`). The
  subrepresentation is the range of `j`. The surjection onto `π` is the inverse
  of `j` corestricted to its range, `LinearEquiv.ofInjective`. Its
  equivariance follows from that of `j` and injectivity.

- `temperedSquareIntegrableBlockDecomposition` (the (8.4) form). It assumes
  `Classification.TemperedBlockExhaustion.{uF, uV} F T` as an explicit
  hypothesis, and that hypothesis is not proved here. Let `τ` be an irreducible
  tempered smooth representation of `GL_(k+1)(F)` with carrier in `Type uV`.
  The theorem gives `l`, `m : Fin l → ℕ` with `∑ i, (m i + 1) = k + 1`, and
  irreducible, square-integrable, unitarizable smooth blocks `σ i` of
  `GL_(m i + 1)(F)`, with carriers in `Type (max uF uV)`. It also gives an
  equivalence of `τ.representation` with
  `F.canonicalNormalizedProductInduced (succBlockShape m hm) (σ · ).representation`.
  Proof: the universe lift `SmoothRep.universeLift` moves `τ` to
  `Type (max uF uV)` with an equivalence that keeps irreducibility and
  temperedness. Exhaustion then gives a block shape `⟨l, size, pos, sum⟩`, the
  blocks and an isomorphism with the product induction. Writing
  `size = fun i => m i + 1` (with `m i = size i - 1`) and substituting turns the
  shape into `succBlockShape m sum`. The isomorphism becomes an equivalence by
  `SmoothRep.equivOfIso`. It is retyped first at the functor object and then at
  `normalizedProductInduced`, which is definitionally the same, and composed
  with the universe-lift equivalence.

- `essentiallySquareIntegrable_uniformComponent` (private core of the (8.2)
  form, over any rank `N > 0`). Let `σ` be an irreducible essentially
  square-integrable smooth representation of `GL_N(F)` with carrier in
  `Type (max uF uV)`. The theorem gives `a, m` with
  `∑ _ : Fin (m + 1), (a + 1) = N` and an irreducible supercuspidal `π₀` of
  `GL_(a+1)(F)`. Then `σ` is an irreducible component of the normalized
  induction of `centeredSegmentBlocks F m π₀`, that is,
  `(π₀ ⊗ α^(m/2), π₀ ⊗ α^(m/2 - 1), …, π₀ ⊗ α^(-m/2))`, along the shape
  `⟨m + 1, fun _ => a + 1, _, _⟩`. Proof:
  1. `Classification.segmentEssentialSquareIntegrableClassification` gives a
     segment `Δ` of degree `N` of which `σ` is the special head
     (`IsSegmentHead`). Its cuspidal base has rank `a + 1`, length `m + 1`, and
     a supercuspidal representative `A`.
  2. `IsSegmentHead.isIrreducibleSocle_down` gives an injective intertwiner `j`
     from `σ` into the decreasing product
     `T.segmentInducedDown A.obj (m + 1) _ = i(ν^m A, …, νA, A)`.
  3. Put `π₀ = ν^(m/2) A`, the twist `SupercuspidalRep.twist` by
     `T.determinantPowerCharacter (a + 1) (m / 2)`. It is irreducible and
     supercuspidal. By `realPowerTwist_add`, block `i` of
     `centeredSegmentBlocks F m π₀` is `ν^(m/2 - i) ν^(m/2) A = ν^(m - i) A`.
     This is the representation of block `i` of the decreasing product.
  4. The block equalities give block equivalences. The Library's
     `normalizedProductInducedEquiv` turns them into an equivalence of the two
     normalized inductions along `BlockShape.uniform (m + 1) (a + 1) _`.
     Composing it with `j` gives an injective intertwiner into the centered
     induction, and `isIrreducibleComponent_of_injective` concludes. To keep
     elaboration cheap, `j` is retyped together with its injectivity in two
     steps, first to the functor object and then to `normalizedProductInduced`,
     before the composition.

- `essentiallySquareIntegrableCenteredSegmentComponent` (the (8.2) form). This
  is the core with `N = r + 1`. Its conclusion uses
  `F.canonicalNormalizedProductInduced (succBlockShape (fun _ => a) hr)` and
  `π₀` with carrier in `Type (max uF uV)`. The blocks are `π₀ ⊗ α^(m/2 - i)`,
  so `σ` is a component of the induction from these blocks, as JPSS (8.2)
  requires. In fact `σ` embeds in that induction.

- `supercuspidal_isEssentiallySquareIntegrable`: an irreducible supercuspidal
  smooth representation `π₀` of `GL_(n+1)(F)`, with carrier in any universe
  `Type uW`, is essentially square-integrable. Proof: lift `π₀` to
  `Type (max uF uW)` by `SmoothRep.universeLift`, keeping irreducibility and
  supercuspidality, and form the cuspidal datum of rank `n + 1` with its class.
  `singletonSegmentInducedEquiv` identifies the induction of the one-term
  segment with the rank-transported representative. So that representative is
  a segment quotient (`IsSegmentQuotient`), and
  `Classification.segmentSpecialEssentialSquareIntegrability` makes it
  essentially square-integrable. Elimination of the rank equality
  (`isEssentiallySquareIntegrable_of_castRank`, private) and the universe-lift
  equivalence (`isEssentiallySquareIntegrable_iff_of_equiv`) bring the result
  back to `π₀`.

## Hypotheses and scope

Only the (8.4) bridge has an unproved hypothesis: `TemperedBlockExhaustion`
for the canonical realization. The (8.2) bridge and the supercuspidal bridge
use only Library theorems and are unconditional. The module does not discharge
any JPSS L-factor proposition and does not prove
`TemperedTwistSupercuspidalPoleStatement`.

## References

- H. Jacquet, I. I. Piatetskii-Shapiro, J. A. Shalika, *Rankin–Selberg
  convolutions*, Amer. J. Math. 105 (1983), (8.2) and (8.4).
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
  Ann. Sci. ÉNS 13 (1980), §9. The Library theorems cited above formalize the
  segment classification used here.
