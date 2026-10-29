# A responsible Weyl branch for strict relative multiplicity excess

Author: Worker 253. The statement boundary was designed by Worker 359.
Worker 429, the intended consumer, confirmed its adequacy for the
supported regular multiplicity argument. Changes to the coordinate
material and boundary are coordinated with Worker 359 and Worker 429.

`Langlands.GLSupportedRegularMultiplicityBranchObstructionStatement` is a
Prop-valued statement definition in
`Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement`.
It isolates an internal derived boundary in the proof of Silberger 1978,
Lemma 5.6, printed p.101. Silberger does not state it as a separately
numbered theorem. This pair supplies no Lean proof of branch selection,
analytic continuation, the multiplicity equality, or the irreducible-head
conclusion.

## Unchanged supported inputs

Through `∀ t, StrictAnti t →`, the input telescope is copied unchanged from
the published
[`GLRelativeRegularComparisonStatement`](../Classification/RelativeRegularComparisonStatement.md).
There are four independent universes: `uF` for the actual `PadicField p`,
`uV` for the fine representation, `uM` for the middle representation and
`uW` for the coarse representation. The prime, the compatible
`TopologicalData T` and the positive rank `n` are arbitrary. Induced
carriers keep the maxima `max uF uV`, `max uF uM` and `max uF uW` of the
imported constructions.

The coarse ordered block shape is `B`. A refinement `Q` gives the middle
shape `D = B.flatten Q`. A refinement `R` of `D` and a direct refinement `S`
of `B` come with an actual equality of ordered block shapes
`h : D.flatten R = B.flatten S`. The fine representation `ω` of
`(D.flatten R).Levi F` is irreducible, Levi-cuspidal and unitarizable.
Its determinant parameter `v₀` satisfies
`RelativeRegularComparison.IsPositiveRootParameter D R v₀`, the published
strictly positive combination of adjacent scalar roots inside each middle
block, written in fine determinant coordinates. The direct fine objects are
the literal transports `ωB = h ▸ ω` and `vB = h ▸ v₀`.

The middle representation `σ` of `D.Levi F` is irreducible and analytically
square-integrable modulo its full product-Levi center. There is an actual
surjective intertwiner from
`innerInduced T D R (fineTwist T D R ω v₀ 0)` onto `σ`. The coarse
representation `π` of `B.Levi F` is irreducible and analytically tempered
modulo its full product-Levi center. It receives both actual surjective
intertwiners of the published statement:

- from `RelativeRegularComparison.middleInduced T B Q σ`;
- from `RelativeJacquetMultiplicity.innerInduced T B S
  (RelativeJacquetMultiplicity.fineTwist T B S ωB vB 0)`.

Both maps are essential to the p.101 setting. Every strictly decreasing
real coarse determinant parameter `t` is allowed: its entries may have any
sign, central shifts are included, and in the one-block case strict
decrease is vacuous. The statement sets the same actual objects as the
published comparison:

```lean
let τ := RelativeJacquetMultiplicity.fineTwist T B S ωB vB t
let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
```

Thus `τ` is the fine representation twisted by the determinant exponents
`-vB(k) + t(parent(k))` and transported to the refined subgroup by the
constructed `flattenedLeviEquiv`. `πt` is `π |det|^t`.

## The multiplicity excess hypothesis

For every `m_in m_amb : ℕ`, the statement assumes

```lean
HasJordanHolderMultiplicity
  (RelativeJacquetMultiplicity.innerJacquet T B S πt) τ m_in
HasJordanHolderMultiplicity
  (RelativeJacquetMultiplicity.ambientJacquet T B S πt) τ m_amb
m_in < m_amb
```

`innerJacquet T B S πt` is the normalized opposite Jacquet module of `πt`
inside the coarse Levi. `ambientJacquet T B S πt` is the normalized opposite
Jacquet module, on the same refined subgroup, of the actual outer upper
normalized induction `CuspidalJacquetMultiplicity.induced T B πt`. The outer
real twist is present on both sides. Each premise supplies an actual finite
composition series in which exactly the stated number of factors is
equivalent to the same actual `τ`. Independence of the composition series
is neither assumed nor needed.

These are not Hom dimensions, a count of Weyl labels, a coefficient of a
virtual class, or occurrence in a chosen irreducible outer quotient. No
outer quotient is a premise.

## The selected branch

Let `C = D.flatten R`, the original fine shape of `ω` and `v₀`. The
conclusion uses ordinary existential quantifiers to select one
`w : Equiv.Perm (Fin n)` and one proof
`hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C w`: the actual
permutation matrix of `w` conjugates the embedded `C`-Levi onto itself.
The following three clauses all concern this same `w`, which does not
depend on the varying parameter `u` of clause 3.

1. `w ∉ Geometric.blockWeyl B`: `w` does not preserve every coarse block.
2. On every full diagonal coordinate `a : Fin n`,

   ```lean
   v₀ (Geometric.blockIndex C (w.symm a)) -
       t (Geometric.blockIndex B (w.symm a)) =
     v₀ (Geometric.blockIndex C a) -
       t (Geometric.blockIndex B a)
   ```

   This is the fixed real stabilizer equation at the same `t` as the
   hypotheses. A determinant exponent on a block is the diagonal exponent
   on each coordinate of that block, so the equation compares the actual
   diagonal exponents of the fine real offset `v₀ - t`.
3. For almost every `u : Fin D.length → ℝ`,

   ```lean
   ComplexTwistFamilies.Occurs T D C C σ w hw ω
     (ComplexTwistFamilies.unitaryAmbient D)
     (ComplexTwistFamilies.refinedMixedAffine D R (-v₀)) u
   ```

The quantifier in clause 3 is Mathlib's `∀ᵐ u ∂volume` for
`MeasureTheory.volume : MeasureTheory.Measure (Fin D.length → ℝ)`. With
the imported `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, this is the
canonical finite product of Lebesgue measures on the real coordinates. It
means that the set of failing `u` is contained in a null set; measurability
of the occurrence set is not asserted. The import supplies only the
measure-space instance on `ℝ`; it adds no hypothesis.

The accepted definitions of
[`ComplexTwistFamilies`](ComplexTwistFamilies.md) are imported without
modification. They construct the actual twists, induced families,
transports and occurrence predicates, and prove no branch selection or
continuation. By these definitions, the occurrence in clause 3 is
`T.IsOppositeJacquetClassExponent C` applied to the following two actual
representations.

- The ambient representation is
  `ComplexTwistFamilies.induced T D σ (unitaryAmbient D u)`. This is the
  **entire** upper normalized induction from the middle Levi to `GL_n(F)`
  of `σ` twisted by the unitary determinant character with exponents
  `i u`. It is not the coarse representation `π`, a coarse unitary family,
  or an irreducible quotient.
- The candidate is
  `ComplexTwistFamilies.transported T D C C w hw ω
  (refinedMixedAffine D R (-v₀)) u`. It first twists the actual fine
  representation `ω` by the complex determinant exponents
  `-v₀(k) + i u(parent(k))`, where `parent(k)` is the middle block
  containing the fine block `k` under `D.flattenBlockEquiv R`. It then
  applies the inverse-conjugation transport
  `CuspidalSupport.transport C C w hw`. Writing
  `e = CuspidalSupport.leviConjugation C C w hw`, the action at a target
  Levi element `m` is the twisted action at `e.symm m`; both the character
  and the base representation are evaluated there.

Transport sends source coordinate `a` to target coordinate `w a`, so a
transported exponent at target `a` evaluates the source at `w.symm a`.
Hence both the negative real offset and the restricted middle-unitary
parameter are reindexed by `(CuspidalSupport.blockEquiv hw).symm`, the same
inverse used in clause 2. No second Weyl action is applied to an already
transported offset, and no coarse unitary parameter replaces the middle
parameter.

`T.IsOppositeJacquetClassExponent C` requires the candidate to be
irreducible and admissible, and to be an actual subquotient of the
normalized opposite Jacquet module of the ambient representation along the
`C`-Levi: an invariant subspace with an actual surjective intertwiner onto
the candidate. This is a representation-class occurrence, not an equality
of central exponents.

The equality `h` connects the direct fine shape `B.flatten S` and its
refined subgroup, used by the multiplicity premises, with the original fine
shape `C` used by the conclusion. All Levi identifications are the
constructed flattened Levi maps and the actual permutation conjugation. No
arbitrary group equivalence is supplied, and no equality of representations
is inferred from coordinate formulas alone.

## Original-source provenance

The original is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. **236** (1978), 95–104, retained as
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
Its registered source ID is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
SHA256 is
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The nested support data are on printed p.99, and Lemma 5.6 and its proof
are on printed p.101 (PDF page 7). Worker 253 inspected the p.101 page
image, which is needed because text extraction loses the imaginary unit
and the subscripts. The published
[continuation-parameter note](../../../notes/jacquet/silberger-continuation-parameters.md)
and [Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
are source-reading notes, not author errata or Lean theorems.

The source's p.96 convention is `χ_ν(m) = q^(i⟨ν,H(m)⟩)`. A real source
parameter `ν` therefore corresponds to the Library determinant exponent
`i ν`. The source's outer twist `σ''_{-i v''}` is `πt` with `t = v''`, and
its fine class `ω_{i(v₀ - v'')}` is `τ`, with determinant exponents
`-v₀ + t` on the fine blocks.

The proof of Lemma 5.6 must show

\[
[\omega_{i(v_0-v'')},\ \delta_P^{1/2} I(P'',\sigma''_{-iv''})(\bar P)]
=
[\omega_{i(v_0-v'')},\ \delta_{P\cap M''}^{1/2}\,
  \sigma''_{-iv''}(\bar P\cap M'')].
\]

These are the ambient and inner multiplicities `m_amb` and `m_in` of the
present hypotheses. The source records the inequality `≥` and equality for
generic `v''`. It labels the composition factors of the ambient Jacquet
module, counting multiplicities, by the classes
`ω^s_{i s(v₀ - v'')}` with `s` in a fixed subset `X` of `W(G/A)`, and
puts `Y = X ∩ W(ω_{i(v₀-v'')})`. For generic `v''` it has
`Y ⊂ W(M''/A)` and the multiplicity `[Y]` equals both sides. The remaining
paragraph, for an arbitrary regular `v''`, reads as follows, with the
printed `√-1` written `i`:

> Let `s ∈ X − Y` and suppose that `s(v₀ − v'') = v₀ − v''`. Then, by
> analytic continuation, `ω_{sν' + i s v₀} ∈ 𝔇_{C^G_{M'}(ω'_{ν'})}(P,A)`
> for almost all `ν' ∈ 𝔞'^*` and thus, since `C^G_{M'}(ω'_{ν'})` is a
> tempered class, `s v₀ ∈ +𝔞^*`.

It then concludes that `s ∈ W(M''/A)`, so that `Y ⊂ W(M''/A)` for all
regular `v''`. Here `ω'` is the middle discrete-series class of `σ`, and
`C^G_{M'}(ω'_{ν'})` is the induction from the middle Levi `M'` of its twist
by the middle parameter `ν'`.

The translation into the present statement is as follows. A strict excess
`m_in < m_amb` is the failure that the source proof excludes. Under the
source's counting, it requires an excess label outside the coarse Weyl group
`W(M''/A)`, which here is `Geometric.blockWeyl B`. Such a label is the
responsible noncoarse branch `w` of clause 1, and clause 2 is its printed
stabilizer condition `s(v₀ - v'') = v₀ - v''`. The source's candidate
`ω_{sν' + i s v₀}` is the `s`-transport of `ω_{ν' + i v₀}`. Its
untransported complex determinant coordinate is `-v₀ + i ν'`, with the
middle parameter `ν'` restricted to the fine blocks. This is exactly
`refinedMixedAffine D R (-v₀)` at `u = ν'`, followed by transport. The
ambient `C^G_{M'}(ω'_{ν'})` is `induced T D σ (unitaryAmbient D u)`. The
middle parameter space `𝔞'^*` is identified with `Fin D.length → ℝ` by a
linear isomorphism; the block-size scaling between scalar and determinant
coordinates preserves Lebesgue-null sets. So the source's "almost all
`ν'`" is the `∀ᵐ` of clause 3.

The statement does not depend on how the printed label sets `X` and `Y`
are read. It asks for one label outside the coarse Weyl group that is
selected by the actual strict excess. It does not assert that every label
persists: a fixed collection of labels with counted multiplicities, mere
pointwise finiteness of spectra, or a class collision at one parameter
does not by itself establish continuation of a given label. Such a
universal per-label claim is not made here.

The quantifier is almost everywhere, as printed on p.101. It is neither
strengthened to every parameter nor specialized at `u = 0`. An
almost-everywhere assertion cannot be evaluated at a prescribed point
without a further argument. This distinguishes the present boundary from
the all-parameter p.102 sentence used by the published
[`GLTemperedReflectionBranchObstructionStatement`](TemperedReflectionBranchObstructionStatement.md).

## Remaining proof obligations and scope

The unproved content isolated here is the implication from the supported
inputs and the strict multiplicity excess to one branch with all three
properties. A proof must derive the responsible branch from the actual
composition factors and geometric filtration of the ambient Jacquet module,
and must establish the almost-everywhere continuation of that selected
branch in the actual middle-unitary family. The statement assumes no
responsible-branch package, no geometric-filtration certificate containing
the desired branch, and no analytic-comparison datum.

Unrestricted Lemma 5.3 or Corollary 5.4 is not invoked. The statement is
distinct from the arbitrary-tempered reflection argument of
Proposition 5.8, which has no support maps on `π`. A proof may not use
`GLRelativeRegularComparisonStatement`, a regular head theorem relying on
it, the full reflection theorem, Langlands parameter or data uniqueness, or
downstream square-integrable classification: these are consumers of this
prerequisite.

After this implication, the source's contradiction still separately needs
unitary-twist preservation and temperedness of the middle-unitary
induction at a parameter chosen in the full-measure occurrence set, an
exponent-cone extraction with the correct block-size weights, and
numerical rigidity such as the published
`Langlands.Exponents.closedConeStabilizerRigidity`. The cone vector repeats
fine determinant exponents on all diagonal coordinates, so fine-block sums
carry block-size weights. These later implications are not premises or
conclusions of this statement.

Strict excess is narrower than failure of a common positive multiplicity.
The later multiplicity and head assembly must separately supply finite
composition series, positivity and the inner-to-ambient inequality in order
to reduce a failure of equality to this premise. The conclusion supplies no
occurrence in a prescribed irreducible quotient, no Jordan–Hölder equality,
no Hom-dimension comparison, and no head theorem. Existing statement
interfaces and their dependencies are unchanged. A proof successor must
target this exact declaration after its independent acceptance and
Library publication.
