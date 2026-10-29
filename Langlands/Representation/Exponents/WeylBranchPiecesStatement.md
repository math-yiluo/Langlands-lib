# Weyl-piece interfaces for the supported excess-multiplicity branch

Author: Worker 253. Coordinated with Worker 514, the first executor of the
proof task for
[`GLSupportedRegularMultiplicityBranchObstructionStatement`](SupportedRegularMultiplicityBranchObstructionStatement.md).

The module `Langlands.Representation.Exponents.WeylBranchPiecesStatement`
contains one predicate and four Prop-valued statement definitions. It proves
none of them. Each statement is an internal, derived consequence of two results
in Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977). The first is the normalized geometric lemma, section 2.12, printed
p.448. The second is section 2.4(d), printed p.447: cuspidal representations
are not subquotients of proper normalized induction. The statements are
specialized to the branch-selection step in the proof of Silberger 1978,
Lemma 5.6, printed p.101. Neither source states them as numbered results.
In BZ77 the geometric lemma concerns the upper Jacquet functor. The opposite
Jacquet versions used here follow by the block-reversal transfer already in
the Library. The product-Levi versions follow by applying the lemma block by
block inside the coarse Levi.

## Common conventions

Every statement quantifies over a prime `p`, an actual `PadicField p` `F` in
universe `uF`, compatible topological data `T` (activated by
`letI := T.topology`), and a positive rank `n` (`0 < n`). Block shapes are
ordered compositions of `n`. `B.flatten S` is the flattened shape of a
refinement `S` of `B`. `flattenedLeviEquiv F B S` is the constructed group
isomorphism from `(B.flatten S).Levi F` to the refined subgroup
`refinedLevi F B S` of `B.Levi F`.

- `RelativeJacquetMultiplicity.innerJacquet T B S V` is the normalized
  opposite Jacquet module of a representation `V` of `B.Levi F` along `S`,
  inside the coarse Levi. It is a representation of the refined subgroup.
  The statements pull it back along `flattenedLeviEquiv` to the flattened
  product Levi `(B.flatten S).Levi F`.
- `RelativeJacquetMultiplicity.ambientJacquet T B S V` is the composed
  normalized opposite Jacquet module of the outer normalized induction of `V`.
- `RelativeJacquetMultiplicity.innerInduced` and
  `RelativeRegularComparison.middleInduced` are the published normalized
  inductions to the coarse Levi.
- `CuspidalJacquetMultiplicity.induced T B V` is the normalized induction of
  `V` to `GL_n(F)`. `CuspidalJacquetMultiplicity.oppositeJacquet T C A` is the
  normalized opposite Jacquet module of `A` along the whole standard Levi of
  shape `C`.
- `CuspidalSupport.ConjugatesLevi D C w` says that conjugation by the actual
  permutation matrix of `w` maps the standard Levi of shape `D` onto the
  standard Levi of shape `C`. `CuspidalSupport.transport D C w hw` transports
  a representation of `D.Levi F` to `C.Levi F` along the inverse of this
  conjugation.
- `Geometric.IsMinimalRepresentative B C w` says that `w` is increasing on
  every block of `B` and `w⁻¹` is increasing on every block of `C`, the
  positive-root form of the minimal double-coset representative.
- `Geometric.blockWeyl B` is the subgroup of permutations preserving every
  block of `B`.
- `CuspidalSupport.IsLeviCuspidal` is admissibility together with actual
  quasicuspidality on every proper standard refinement.

The predicate

```lean
WeylBranchPieces.IsSubquotient A X :=
  ∃ U : Subrepresentation A, ∃ q : U.toRepresentation.IntertwiningMap X,
    Function.Surjective q
```

says that `X` is an actual quotient of an actual subrepresentation of `A`.
The representations may have different carrier universes. This is the same
shape as the subquotient clause of
`PadicField.TopologicalData.IsOppositeJacquetClassExponent`.

## `GLGeometricPieceLiftingStatement`

Universes `uF uV`. Let `B C` be shapes and `S` a refinement of `B`. Let `x` be
a permutation with `IsMinimalRepresentative B C x` and
`hx : ConjugatesLevi (B.flatten S) C x`. Then for every smooth representation
`V : Rep.{uV} ℂ (B.Levi F)`, the transport by `x` of the pulled-back inner
Jacquet module `innerJacquet T B S V` is a subquotient of
`oppositeJacquet T C (induced T B V)`.

In the geometric lemma the index `x` labels the piece
`Ind^C_{C ∩ xBx⁻¹} ∘ x ∘ r^B_{B ∩ x⁻¹Cx}`. Here `x⁻¹Cx` is the whole
flattened Levi `B.flatten S`, so that piece is the transported Jacquet module
itself. A graded piece of a finite filtration is a quotient of a
subrepresentation. No irreducibility is assumed.

## `GLGeometricExcessBranchStatement`

Universes `uF uV uW`. Let `S` refine `B`, let `V : Rep.{uW} ℂ (B.Levi F)` be
smooth, and let `ρ : Rep.{uV} ℂ ((B.flatten S).Levi F)` be irreducible and
Levi-cuspidal. Put

```lean
let τ := Rep.of (ρ.ρ.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)
```

on the refined subgroup. Assume actual Jordan–Hölder multiplicities `m_in` of
`τ` in `innerJacquet T B S V` and `m_amb` of `τ` in `ambientJacquet T B S V`,
with `m_in < m_amb`. The conclusion supplies a permutation `x` and a
refinement `S'` of `B`, with `hx : ConjugatesLevi (B.flatten S')
(B.flatten S) x`, such that

- `IsMinimalRepresentative B (B.flatten S) x`;
- `x ∉ blockWeyl B`;
- `ρ` is a subquotient of the transport by `x` of the pulled-back
  `innerJacquet T B S' V`.

This is the geometric-lemma count for the opposite Jacquet module of
`Ind_B^G V` along `B.flatten S`. The identity piece is the inner Jacquet
module. A strict excess therefore lies in some other piece. A cuspidal `ρ`
cannot occur in a properly induced piece, so that piece has the displayed
whole-Levi form. A minimal representative inside `blockWeyl B` is the
identity.

## `GLProductLeviCuspidalLocalizationStatement`

Universes `uF uV uM`. Let `Q` refine `B` and put `D = B.flatten Q`. Let
`σ : Rep.{uM} ℂ (D.Levi F)` be smooth. Let `S'` refine `B` and let
`ρ : Rep.{uV} ℂ ((B.flatten S').Levi F)` be irreducible and Levi-cuspidal.
Assume `ρ` is a subquotient of the pulled-back
`innerJacquet T B S' (middleInduced T B Q σ)`. The conclusion supplies a
permutation `g ∈ blockWeyl B` and a refinement `R'` of `D`, with
`hg : ConjugatesLevi (D.flatten R') (B.flatten S') g`, such that
`IsMinimalRepresentative D (B.flatten S') g` holds and `ρ` is a subquotient
of the transport by `g` of the pulled-back `innerJacquet T D R' σ`.

This is the geometric lemma inside the coarse Levi `B.Levi F`, a product of
general linear groups. Its Weyl group is `blockWeyl B`. An irreducible
subquotient of a finitely filtered representation is a subquotient of one
graded piece. Cuspidality of `ρ` excludes the properly induced pieces.

## `GLCuspidalInductionJacquetConstituentStatement`

Universes `uF uV uW`. Let `R R'` refine a shape `D`. Let
`ω : Rep.{uV} ℂ ((D.flatten R).Levi F)` be irreducible and Levi-cuspidal, and
let `ρ : Rep.{uW} ℂ ((D.flatten R').Levi F)` be irreducible and Levi-cuspidal.
Assume `ρ` is a subquotient of the pulled-back inner Jacquet module along
`R'` of the inner normalized induction, from `refinedLevi F D R`, of `ω`
pulled back along the inverse of `flattenedLeviEquiv F D R`. Then there are
`h ∈ blockWeyl D` and `hh : ConjugatesLevi (D.flatten R) (D.flatten R') h`
with an actual equivalence from `ρ.ρ` to
`CuspidalSupport.transport (D.flatten R) (D.flatten R') h hh ω.ρ`.

This is the product-Levi geometric lemma for cuspidal input. Cuspidality of
`ω` removes every piece in which `ω` is Jacquet-restricted to a proper Levi.
Cuspidality of `ρ` removes every properly induced piece. The remaining pieces
are irreducible transports of `ω`. The cuspidality hypothesis on `ρ` is
needed: without it, `ρ` could be a constituent of a properly induced piece.

## Intended use

Together with published twist compatibilities, unitary rigidity and the
exactness of Jacquet functors, these statements give the branch `s = x g h`.
Here `x` comes from the excess statement at twist `t`, `g` from the
localization statement for `σ |det|^t`, and `h` from the cuspidal-constituent
statement for the inner induction surjecting onto it. The lifting statement,
applied once with the minimal representative `x g`, gives the occurrence for
every middle unitary parameter. This module claims none of these consequences.
