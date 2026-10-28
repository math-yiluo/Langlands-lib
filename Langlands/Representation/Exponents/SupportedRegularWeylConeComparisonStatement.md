# Two-sided Weyl and cone comparison for supported regular data

Authors: Worker 125 and Worker 359.

`Langlands.GLSupportedRegularWeylConeComparisonStatement` is one closed
Prop-valued definition. It states an internal, derived `GL_n` comparison
boundary motivated by the parameter argument in Silberger 1978,
Proposition 6.1, printed pp.102–103. It supplies no proof. Its conclusion
precedes the numerical orthogonality and standard-chamber arguments, and
does not identify coarse inducing representations.

## Two independent supported data

The field prime, actual `F : PadicField.{uF} p`, compatible
`TopologicalData T`, and positive ambient rank `n` are shared. For each
`i = 1,2`, the definition independently repeats the complete supporting
telescope of
[`GLRelativeRegularComparisonStatement`](../Classification/RelativeRegularComparisonStatement.md)
through its real parameter `ti` and `StrictAnti ti`. It neither assumes
that proposition nor any of its multiplicity or head conclusions.

The coarse ordered shape `Bi` has a refinement `Qi`, giving
`Di = Bi.flatten Qi`. A refinement `Ri` of `Di` and a direct refinement
`Si` of `Bi` are related by the actual shape equality
`hi : Di.flatten Ri = Bi.flatten Si`. The fine representation `ωi` on
`(Di.flatten Ri).Levi F.Carrier` is irreducible, Levi-cuspidal, and
unitarizable. The exact existing predicate
`RelativeRegularComparison.IsPositiveRootParameter Di Ri vi` is required.
Lean transports these fine data literally along `hi`:

```lean
ωBi := hi ▸ ωi
vBi := hi ▸ vi
Ci := Bi.flatten Si
```

Thus the two presentations of each datum's fine shape agree as actual
ordered shapes. There is no equality or matching assumption between `C1`
and `C2`.

The middle representation `σi` on `Di.Levi` is irreducible and
`IsLeviSquareIntegrable T Di σi`. It receives an actual surjective
intertwiner from
`innerInduced T Di Ri (fineTwist T Di Ri ωi vi 0)`.
The coarse representation `πi` on `Bi.Levi` is irreducible and
`IsLeviTempered T Bi πi`. It receives both actual support maps from
`middleInduced T Bi Qi σi` and from
`innerInduced T Bi Si (fineTwist T Bi Si ωBi vBi 0)`.
These analytic predicates use the full product-Levi center and every
Borel Haar measure on its actual central quotient, as in the imported
support telescope.

The inductions use the constructed group equivalence

```lean
Geometric.flattenedLeviEquiv F.Carrier Bi Si :
  (Bi.flatten Si).Levi F.Carrier ≃*
    Geometric.refinedLevi F.Carrier Bi Si
```

Its forward map runs from the flattened product Levi to the refined
subgroup inside the coarser product Levi. Its inverse runs from that
subgroup to the flattened product Levi. Thus `fineTwist` and
`middleInduced` obtain actions on the refined subgroup by composing the
flattened-Levi actions with the inverse. The `hi` transports are equality
transports; they are distinct from these constructed group equivalences.

Finally, an actual irreducible
`J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier)` receives a surjective
intertwiner from each outer induction
`CuspidalJacquetMultiplicity.induced T Bi
  (Rep.of (T.leviRealPowerTwist Bi ti πi.ρ))`.
These are arbitrary weak quotient witnesses. No distinguished quotient,
unique head, association certificate, continuation, or cone is a premise.

The universes `uV1,uV2` of the fine carriers, `uM1,uM2` of the middle
carriers, `uW1,uW2` of the coarse carriers, `uJ` of the quotient, and `uF`
of the field are independent. Each actual induction retains carrier
universe `max uF uSource`; equality transports and twists keep their
source carriers. Surjective intertwiners and equivalences allow distinct
source and target universes.

In the final equivalence clause, the Lean applications explicitly pass the
additive and complex-module structures stored in `ωB1` and `ωB2`. This
resolves instance inference through the equality transports `hi ▸ ωi`;
it introduces no new hypothesis, carrier identification, or operation.

## One permutation and both cone conditions

Define full-diagonal vectors by repeating the corresponding determinant
exponent on every coordinate of its actual block:

```lean
V1 a := vB1 (Geometric.blockIndex C1 a)
V2 a := vB2 (Geometric.blockIndex C2 a)
A1 a := t1 (Geometric.blockIndex B1 a)
A2 a := t2 (Geometric.blockIndex B2 a)
```

The conclusion selects one `w : Equiv.Perm (Fin n)` and one proof
`hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C1 C2 w`.
That same pair witnesses all four clauses:

1. The transport from `C1` to `C2` of the actual representation
   `T.leviRealPowerTwist C1
     (RealTwistFamilies.nestedParameter B1 S1 vB1 t1) ωB1.ρ`
   is equivalent to
   `T.leviRealPowerTwist C2
     (RealTwistFamilies.nestedParameter B2 S2 vB2 t2) ωB2.ρ`.
2. For every diagonal coordinate `a`,
   `V1 (w.symm a) - A1 (w.symm a) = V2 a - A2 a`.
3. `Exponents.IsClosedPositiveRootCone (fun a => V1 (w.symm a))`.
4. `Exponents.IsClosedPositiveRootCone (fun a => V2 (w a))`.

The actual Levi conjugation sends source coordinate `a` to target `w a`.
`CuspidalSupport.transport` pulls back by its inverse, so a transported
parameter at target coordinate `a` is evaluated at `w.symm a`. The first
cone is the source vector transported to the target. The second is the
target vector transported back to the source; its argument is `w a`.
They are separate requirements on the same responsible Weyl comparison.
The fixed relation uses `V-A`, the total negation of the real twist
`-V+A`, so its sign agrees with the actual representation clause.

## Determinant weights and the full-diagonal cone

On a fine block of size `d_j`, a determinant exponent `r_j` restricts to
the scalar exponent `x_j = d_j r_j`, since
`|det(z I_(d_j))|^(r_j) = |z|^(d_j r_j)`.
The positive-root support predicate therefore uses the adjacent vectors
`e_j/d_j - e_(j+1)/d_(j+1)` in determinant coordinates. Its strictly
positive combination has size-weighted sum zero in each middle block.
This also gives same-side orthogonality of `Vi` with the coarse
block-constant vector `Ai`, but that orthogonality is not an extra premise
or an additional conclusion here.

The source's closed cone on a fine split center uses scalar coordinates
`x_j`, whose sum is zero and whose proper initial sums are nonnegative.
For the repeated full-diagonal vector `R`, the partial sum at the end of
fine block `j` equals `sum_(l ≤ j) d_l r_l`. If a cut is `m` coordinates
into that block, `0 ≤ m ≤ d_j`, its partial sum is

```text
P_(j-1) + m*r_j
  = (1 - m/d_j)*P_(j-1) + (m/d_j)*P_j,
where P_j = sum_(l ≤ j) d_l*r_l.
```

The positive block size makes this a convex combination of the two
endpoint sums. Thus the weighted split-center cone bounds give every
full-diagonal partial-sum bound, including cuts inside a block; the total
sums agree too. This applies to the target shape for `V1 ∘ w.symm` and
to the source shape for `V2 ∘ w`, since actual Levi conjugacy carries
whole fine blocks to whole fine blocks of equal size. These observations
explain the displayed full-diagonal cone convention; no unweighted
fine-index cone is applied directly to determinant exponents.

## Normalization and source correspondence

The source is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. **236** (1978), 95–104. The retained original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 125 read printed pp.96,99,102–103 as text and page images for this
statement. No source-specific author erratum was found in the supplied
note and literature roots.

Printed p.96 uses positive-half-modulus normalized induction and
`χ_ν(m) = q^(i⟨ν,H(m)⟩)`. The Library absolute value is
`|ϖ| = q^(-1)`, so the source fine twist `ν = i vi` gives determinant
exponent `-vi`, and the outer twist `ν = -i ti` gives `+ti`.
`RealTwistFamilies.nestedParameter Bi Si vBi ti` is exactly
`-vBi + restrictParameter Bi Si ti`. The actual upper inductions have
positive-half-modulus covariance and right translation. The opposite
Jacquet convention used in the source argument is the actual lower
radical coinvariant module normalized by the positive half of the upper
modulus, equivalently the inverse half of the opposite modulus.
Strict descent of `ti` is the upper regular positive chamber; individual
entries need not be positive and no central sum is set to zero.
Arbitrary real central shifts are retained. A one-block coarse shape has
vacuous strict descent and allows every real exponent. Unrefined middle
blocks have empty root expansions and zero internal parameter.

Printed p.99 supplies the nested cuspidal/discrete-series/tempered support
setup. The final paragraph of p.102 in the proof of Proposition 6.1 uses
associated cuspidal support to select a Weyl comparison and the relation
`s(v1-v1'') = v2-v2''`. It then discusses actual class exponents of
varying middle-unitary induced families. The first paragraph of p.103
uses temperedness to place `s⁻¹ v2` in the source fine root cone; the
symmetric comparison gives `s v1` in the target cone. These are the two
oriented cones above. The subsequent inner-product and chamber arguments,
and the later use of Propositions 5.8/5.7 for tempered-class recovery, are
outside this target.

This boundary is an explicit internal `GL_n` extraction, not the literal
wording of Proposition 6.1. It replaces the source's chosen quotient
classes by actual maps to one irreducible `J` and records the supporting
data rather than invoking a downstream classification to construct them.
Establishing the actual twisted fine-support equivalence and its real
parameter relation from support association remains a proof obligation.
Passing from arbitrary weak quotient witnesses to the distinguished
source quotients requires separately proved head uniqueness in that
future proof, without adding it as a premise here.

## Remaining proof boundary

The continuation and selection of a single responsible Weyl comparison
satisfying both cone bounds remain representation-theoretic proof
obligations. The published
[`ComplexTwistFamilies`](ComplexTwistFamilies.md) constructs actual
twists, unitary families, inverse-conjugation transports and
same-parameter opposite-Jacquet occurrence predicates; it asserts no
continuation or occurrence. Finite pointwise spectra and collision of
Weyl labels establish neither fixed-label persistence nor a universal
occurrence family. An almost-everywhere occurrence cannot simply be
specialized at zero. See the published
[continuation note](../../../notes/jacquet/silberger-continuation-parameters.md).

This supported scope differs from the arbitrary-tempered Proposition 5.8
selected-branch target. The
[Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
also remains in force: unrestricted Lemma 5.3 and Corollary 5.4 supply no
shortcut. The final regular parameter/data uniqueness statements,
downstream square-integrable block classification, and the full
conclusion of Proposition 6.1 must not be used to prove this prerequisite.

With `x1 = V1 ∘ w.symm`, `y1 = A1 ∘ w.symm`, `x2 = V2`, and `y2 = A2`,
the fixed relation has the form `x1-y1 = x2-y2`. The two transported cones
give the two distinct cross signs needed by
`Exponents.OrthogonalParameterComparisonStatement`, while the support
expansions give the same-side orthogonalities. Those numerical and
ordered-chamber steps belong to later work. This statement itself
asserts no equality of the transported `Vi`, no equality of the
transported `Ai`, no ordered block matching, and no equivalence of the
coarse inducing representations.
