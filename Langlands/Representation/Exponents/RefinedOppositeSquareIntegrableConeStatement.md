# Strict blockwise cones for opposite exponents of square-integrable product Levis

Author: Worker 544. Worker 510 isolated this interface and supplied its exact
formulation for task `9c51235f-6d67-440b-b1e3-9da4fd02c67c`, revision 1.

`Langlands.Exponents.RefinedOppositeSquareIntegrableConeStatement.{uF,uV}`
is a closed Prop-valued definition. It states a derived analytic necessity and
proves nothing. Neither this definition nor another proposition definition
supplies a proof of the analytic criterion or of any transport described below.

## Quantifiers and the analytic hypothesis

The proposition quantifies every prime `p` with `[Fact p.Prime]`, every
`F : PadicField.{uF} p`, every supplied `T : F.TopologicalData`, every positive
rank `n`, every ordered block shape `D : GeneralLinear.BlockShape n`, and
every actual representation `σ : Rep.{uV} ℂ (D.Levi F.Carrier)`. The field
universe `uF` and original representation-carrier universe `uV` are independent.
The local instance `letI := T.topology` supplies the field topology and its
induced unit-group and product topologies.

The only representation hypotheses are `Representation.IsIrreducible σ.ρ`
and `RelativeRegularComparison.IsLeviSquareIntegrable T D σ`. The latter
uses the actual product Levi

```text
D.Levi F.Carrier = ∏ i : Fin D.length, GL_(D.size i)(F)
```

and its quotient by its full group-theoretic center:

```lean
D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)
```

Its definition installs `T.topology` and `T.leviTopologicalGroup D`, and
quantifies every measurable-space structure on this quotient that is Borel
for its topology, every measure `μ` there, and every `IsHaarMeasure μ`
instance. For each such choice it requires the existing
`IsSquareIntegrableModCenter σ.ρ μ`. That predicate includes admissibility
(hence smoothness), a smooth unitary scalar character of the full center,
and `MemLp` with exponent two for every descended matrix-coefficient norm
`gZ ↦ ‖ℓ(σ.ρ g v)‖`, where `v` runs through the carrier and `ℓ` through
the smooth dual. It uses no topology on the representation carrier.
Irreducibility is the separate hypothesis displayed above.

Thus the hypothesis concerns all Borel Haar measures on the full central
quotient of the product. It does not use only the single diagonal center of
an ambient `GL_n`. Establishing the required analytic comparisons includes
establishing existence of suitable Borel Haar measures wherever a proof
extracts a consequence from this universally quantified predicate.

## Refinements, the scalar map, and occurrence

For every `R : Geometric.BlockRefinement D`, including refinements with one
piece inside any original block, the statement quantifies every homomorphism

```lean
χ : (Fin (D.flatten R).length → F.Carrierˣ) →* ℂˣ
```

and names the actual map

```lean
z := (Geometric.flattenedLeviEquiv F.Carrier D R).toMonoidHom.comp
  ((D.flatten R).blockScalarLevi F.Carrier)
```

Its codomain is `Geometric.refinedLevi F.Carrier D R`, the actual refined
Levi subgroup of `D.Levi F.Carrier`. It first forms the fine block scalars
in the flattened product Levi, then applies the constructed flattened-Levi
equivalence. The map `D.flattenBlockEquiv R` sends the nested index `⟨i,k⟩`
to its fine flattened index, preserving the given original and inner orders.
No replacement group or supplied equivalence is used.

The character hypotheses are exactly

```lean
IsOpen (χ.ker : Set (Fin (D.flatten R).length → F.Carrierˣ))
```

and

```lean
IsGeneralizedEigencharacter
  ((T.normalizedRefinedOppositeJacquet D R σ.ρ).comp z) χ
```

The latter is the existing common-power occurrence predicate: for some
natural number `m`, `characterSpace _ χ m ≠ ⊥`. Equivalently, one nonzero
vector `w` of this actual quotient is killed by
`(π(a) - (χ a : ℂ) • 1)^m` for every scalar tuple `a`, with the same `w`
and the same `m` throughout. This is stronger than separate pointwise
spectral membership.

The quotient is literally the coinvariants by
`Geometric.refinedOppositeUnipotent F.Carrier D R`, the product of the
inner lower block radicals. Its normalized action twists the raw quotient
action by the inverse half of `T.refinedOppositeLeviModulus D R`.
That opposite full character is defined as the inverse of the upper full
character `T.refinedLeviModulus D R`. The proved identity
`T.inverseHalf_refinedOppositeLeviModulus D R` identifies its inverse half
with `T.refinedLeviHalfModulus D R`, the positive upper half. Consequently,
the existing quotient-class formula is

```text
m · [v] = δ_upper(m)^(1/2) [σ.ρ(m.val) v].
```

This normalization formula concerns an actual lower-radical quotient. It
does not establish a comparison with an upper Jacquet quotient or a strict
analytic inequality. The explicit character's identification with Haar
conjugation scaling is also an analytic comparison obligation.

## Real parts, signs, and the strict conclusion

For every supplied `x : Fin (D.flatten R).length → ℝ` satisfying
`T.IsRealPartOf χ x`, that is,

```text
‖χ(a)‖ = ∏ j, T.normalizedAbs(a_j)^(x_j),
```

the conclusion is

```lean
∀ i : Fin D.length,
  Exponents.IsPositiveRootCone
    (fun k : Fin (R i).length => -x (D.flattenBlockEquiv R ⟨i, k⟩))
```

Write `xᵢ(k) = x (D.flattenBlockEquiv R ⟨i,k⟩)`. By the existing definition
of `IsPositiveRootCone`, this says separately for each original block `i`
that

```text
∑ k, xᵢ(k) = 0,
∑ k < h, xᵢ(k) < 0  for every 0 < h < (R i).length.
```

The prefix inequalities are strict. For a one-piece refinement there is no
proper nonempty prefix, but the zero-sum condition forces its sole `xᵢ`
coordinate to be zero. There is one zero sum for each original block;
one aggregate zero sum over all flattened indices would be weaker.

The minus sign records the opposite convention in the original inner
ordering. The upper negative scalar chamber has nondecreasing absolute
values; the corresponding opposite chamber has nonincreasing ones. Under
the required analytic transport, strict decay on noncentral opposite
directions gives strictly negative prefixes for `xᵢ`, or equivalently the
positive-root-cone condition for `-xᵢ`. A proof must establish that transport,
with the character, normalization and ordering accounted for.

These are scalar real-part coordinates. Fine sizes already enter when a
determinant character is restricted to scalar matrices; no size factors
occur in the stated cone. The separate identity relating `x` to negative
size times a determinant parameter, and the numerical theorem
`Langlands.Exponents.positiveRootParameterCone`, are outside this unit.

## Original motivation and derived provenance

The following registered originals were read directly, including the
formula-bearing page images. Printed and PDF page numbers for Casselman
coincide; Silberger's PDF page number is the printed number plus six.

- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft of 1 May 1995, source
  `casselman-1995-admissible-representations`, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Theorem 4.4.6, p.45, gives the strict exponent bound away from compact and
  central directions for admissible representations with central character.
  The preceding pp.44–45 describe occurrence through nonzero generalized
  central-character spaces of the unnormalized Jacquet module and agreement
  with the ambient central character on central intersections. The supporting
  conventions are §1.4, p.13 (negative chamber), §1.5, p.16 (modulus and Haar
  double-coset volumes), §2.1, p.21 (open-kernel characters and common-power
  generalized-character spaces), and §2.5, p.28 (unitary central character and
  square-integrability of coefficients modulo the center). The source's
  unnormalized character is multiplied by the inverse half modulus in its
  criterion; it is not already the normalized character used here.
- A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic
  groups*, 1979, source `silberger-1979-harmonic-analysis`, SHA256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  Theorem 4.4.4 and proof, printed pp.177–180 (PDF pp.183–186), compare
  square-integrability on bounded central strips for `f ∈ A(G)` with
  conditions on its exponents. In part (4), the real exponent `γ` is
  specified by `|χ(a)| = q^⟨γ,H_P(a)⟩`; adding a combination of simple roots
  with strictly positive coefficients puts it in the central dual. This
  motivates the strict root-cone formulation after central directions are
  removed. The passage concerns its own functions, exponents and chambers.

No source-specific errata file for either retained original was found in
the checked project/public-note errata locations or the source-name searches
recorded during authoring. This is a report of those checks, not a claim
that the sources have no errata.

This interface is a derived specialization to the Library's product Levi,
actual normalized opposite quotient, ordered scalar coordinates, and
separate block-center removal. Neither original literally states this
Lean proposition. No source transport is asserted as a proved theorem.

## Remaining proof obligations and ownership

A future proof must obtain the lower analytic criterion from independently
proved Library results and prove every transport it uses. In particular:

1. It must compare the actual quotient topology, Borel Haar measures,
   descended smooth-dual coefficients and the explicitly defined modulus
   with the analytic objects in the criterion. The all-Borel-Haar formulation
   must be justified at each comparison.
2. It must prove opposite-to-upper, conjugation or block-reversal transports
   for the actual quotients, preserving the scalar character and tracking
   normalization and order. The positive-upper-half formula alone yields
   no strict prefix bound.
3. It must establish the criterion for the whole product Levi, or use an
   independently proved admissible tensor factorization together with
   analytic `L²` tensor comparison and actual Jacquet/generalized-character
   occurrence transport. No tensor presentation or replacement criterion
   may be added to this closed statement.
4. It must carry the unitary character of the full product center through
   the quotient and normalization to the restrictions of `χ`. These
   independent original-block central directions give the separate zero
   sums, including singleton cases. A single diagonal character gives
   only an aggregate sum.
5. Any intermediate tensor, induced, quotient or realized carrier must be
   handled at its actual universe. A proof using a smaller realization must
   transport irreducibility, admissibility, square-integrability,
   generalized-character occurrence and the real-part identity back to
   the original carrier. The independent `uF,uV` quantifiers must remain.

Worker 19's upper-`GL_n` strict-criterion proof, Worker 158's analytic
square-integrable tensor comparison, and the existing adjointness, pairing,
duality, quotient, unitarization, opposite-filtration and cosocle/head work
retain their separate ownership. The definition
`Langlands.GLSquareIntegrableExponentCriterionStatement` is not a proof and
its upper exponent cannot simply be relabeled as this opposite product-Levi
occurrence.

The separate
`Langlands.Exponents.RefinedQuotientOppositeCharacterStatement` concerns
obtaining the occurrence from an upper refined quotient; its statement alone
does not supply that occurrence. Here occurrence and a real part are
hypotheses. No support quotient, scalar-action witness, supplied analytic
criterion, tensor presentation or upper exponent is assumed. This unit does
not construct real parts, unitarize inducing data, or prove
`Langlands.GLDiscreteSeriesPositiveRootSupportStatement`. Downstream
regular-head, exhaustion, classification and joint-support results
depending on that support step cannot be used to prove this interface.
