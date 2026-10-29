# Exactness of the mirabolic minus functors

Author: Worker 749.

This module states that the four published mirabolic minus functors of
`Langlands.Representation.Derivative.MirabolicMinus` preserve short exact
sequences. These are unnormalized `Ψ⁻`, unnormalized `Φ⁻`, normalized `Ψ⁻`
and normalized `Φ⁻`. The module has two Prop-valued definitions: a small
helper and the principal proposition
`Langlands.Derivative.Mirabolic.MinusExactnessStatement.{uF, uV} F T`. It
proves nothing and constructs no functor. Exactness of these functors remains
a proof obligation.

## The helper `MapsShortExactIntertwiners`

`MapsShortExactIntertwiners.{uG, uH, uV} J` is defined for any groups `G`
and `H` with topologies and any functor

`J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H`.

It says: for all objects `A B C : SmoothRep.{0, uG, uV} ℂ G` and all
morphisms `i : A ⟶ B` and `q : B ⟶ C`, if

```
Function.Injective (SmoothRep.hom i)
Function.Surjective (SmoothRep.hom q)
LinearMap.range (SmoothRep.hom i).toLinearMap =
  LinearMap.ker (SmoothRep.hom q).toLinearMap
```

then

```
Function.Injective (SmoothRep.hom (J.map i)) ∧
LinearMap.range (SmoothRep.hom (J.map i)).toLinearMap =
  LinearMap.ker (SmoothRep.hom (J.map q)).toLinearMap ∧
Function.Surjective (SmoothRep.hom (J.map q))
```

`SmoothRep.hom` returns the actual intertwiner underlying a morphism of the
full smooth category. The hypotheses say that `0 → A → B → C → 0` is exact
on the underlying complex vector spaces. The conclusion says the same of
`0 → J A → J B → J C → 0`. Injectivity and surjectivity are statements about
the intertwiners as functions. The middle condition is an equality of
`ℂ`-submodules of the carrier of `B`, respectively of `J B`. The helper only
packages this condition so that it need not be written four times. It
assumes no functor, comparison or exactness certificate. It adds no
hypothesis to the objects beyond the smoothness bundled in `SmoothRep`.

## The principal proposition

The parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with level parameters in the order `uF, uV`. The
carrier universe `uV` is independent of `uF`. The body installs
`letI := T.topology`, so all groups carry the topology supplied by `T`. No
canonical topology is substituted. All categories are
`SmoothRep.{0, uF, uV} ℂ _`. Their carriers stay in `Type uV`, and `uV` is
not replaced by `max uF uV`.

`MinusExactnessStatement F T` is the conjunction of four clauses:

1. for every `n : ℕ`,
   `MapsShortExactIntertwiners (psiMinusUnnormalized.{uV} T n)`. This is
   unnormalized `Ψ⁻` from `GeneralLinear.mirabolic n F.Carrier = P_(n+1)` to
   `GeneralLinear n F.Carrier = GL_n`;
2. for every `n : ℕ` and every
   `ψ : UnitaryAdditiveCharacter F.Carrier` (with topology `T.topology`),
   `MapsShortExactIntertwiners (phiMinusUnnormalized.{uV} T ψ n)`. This is
   unnormalized `Φ⁻` from `GeneralLinear.mirabolic (n+1) F.Carrier =
   P_(n+2)` to `GeneralLinear.mirabolic n F.Carrier = P_(n+1)`;
3. for every `n : ℕ`,
   `MapsShortExactIntertwiners (psiMinus.{uV} T n)`. This is the
   determinant-normalized `Ψ⁻` with the source and target of clause 1;
4. for every `n : ℕ` and every such `ψ`,
   `MapsShortExactIntertwiners (phiMinus.{uV} T ψ n)`. This is the
   determinant-normalized `Φ⁻` with the source and target of clause 2.

All four functors are the published definitions in namespace
`Langlands.Derivative.Mirabolic`. They are referred to by name and are not
restated. During development the proposition was checked to be
definitionally equal (`Iff.rfl`) to the conjunction with the helper fully
unfolded in each clause.

### The maps in each clause

The published module fixes what `J.map` does on carriers.

- In clauses 1 and 3 the carrier of `J A` is
  `Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1`.
  This is the quotient of `A` by the span of the vectors `A(u)v - v` for `u`
  in the radical `V_(n+1)`. On a class `psiMinusQuotient T n A v` the map
  `SmoothRep.hom (J.map f)` gives `psiMinusQuotient T n B (SmoothRep.hom f v)`
  (`psiMinusUnnormalized_map_quotient`, `psiMinus_map_quotient`).
- In clauses 2 and 4 the carrier of `J A` is
  `Jacquet.Localization.Coinvariants A.representation
  (radical (n+1) F.Carrier) (T.mirabolicTheta ψ n)`. This is the quotient by
  the span of the vectors `A(u)v - θ_ψ(u)v` for `u` in `V_(n+2)`. Here
  `θ_ψ` is the published positive last-coordinate character. The map sends
  `phiMinusQuotient T ψ n A v` to `phiMinusQuotient T ψ n B (SmoothRep.hom f v)`
  (`phiMinusUnnormalized_map_quotient`, `phiMinus_map_quotient`).

In both cases the normalized and unnormalized functors have the same carriers
and the same linear maps. They differ only in the group action, by the factor
`|det|^(-1/2)` (`psiMinus_eq`, `phiMinus_eq`).

### Rank boundaries

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)`. Every
`n : ℕ` is included. At `n = 0`, clauses 1 and 3 concern `Ψ⁻ : P_1 → GL_0`,
and clauses 2 and 4 concern `Φ⁻ : P_2 → P_1`. The `Φ⁻` clauses use the
character `T.mirabolicTheta ψ n` on `V_(n+2)`, which always has a
coordinate. No character on a radical without coordinates is used.

### Additive characters

`UnitaryAdditiveCharacter` bundles continuity for `T.topology` and
nontriviality. The `Φ⁻` clauses therefore say nothing about the trivial
additive character.

## Source and provenance

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Page numbers below are printed numbers, with one-based PDF pages in
parentheses. Pages 445 and 451 were checked on the rendered images.

- §1.8(b), printed pp.444–445 (PDF pages 5–6). For `M` normalizing `U` and
  a character `θ` of `U` normalized by `M`, `E(U,θ)` is spanned by the
  vectors `π(u)ξ - θ(u)ξ`. The `θ`-localisation is `r_{U,θ}(E) = E/E(U,θ)`,
  with action `δ(m)(ξ + E(U,θ)) = mod_U^(-1/2)(m)·(π(m)ξ + E(U,θ))`.
- §1.9, printed p.445 (PDF page 6). `U` is a *limit of compact subgroups*
  if every compact subset of `U` lies in a compact subgroup of `U`.
  Proposition 1.9(a) states that `r_{U,θ}` is exact if `U` is a limit of
  compact subgroups. The print reads "a limit of by compact subgroups".
- §3.1, printed p.450 (PDF page 11). This section defines `P_n`, its
  radical `V_n`, the standard embeddings of `G_(n-1)` and `P_(n-1)`, and
  `θ((v_ij)) = ψ(v_(n-1,n))` for a fixed nontrivial additive character `ψ`.
- §3.2, printed pp.450–451 (PDF pages 11–12). `Ψ⁻ = r_{V,1}` and
  `Φ⁻ = r_{V,θ}`, normalized as in §1.8. Proposition 3.2(a), p.451: "All the
  functors `Ψ⁻, Ψ⁺, Φ⁻, Φ⁺, Φ̂⁺` are exact." The proof begins: "Parts (a),
  (c) and the first part of (b) follow from 1.9."

No applicable errata entry was found in the central library, the literature
index or the public notes. The published note
`notes/henniart/segment-head-independence.md` records the same.

### What the source asserts

Proposition 3.2(a) asserts exactness of five functors on the abelian
categories `Alg P_n` and `Alg G_(n-1)`. This module takes only the two minus
functors `Ψ⁻` and `Φ⁻`. Their source normalization multiplies the descended
action by `mod_V^(-1/2)`. "Exact" there means exact on the abelian category
of all smooth representations. The source does not separately state the four
Library clauses.

### Derived transfer to the four Library functors

The four clauses are derived, not quoted. The Library functors are not the
source functors verbatim in two ways.

- The unnormalized functors leave out the factor `mod_V^(-1/2)`. The
  normalized functors use the explicit character `|det|^(-1/2)` of the output
  group in its place. This module does not identify that character with a
  Haar modulus.
- The descended action of the Levi or successor subgroup is pulled back to
  `GL_n` or `P_(n+1)` along the published continuous group equivalences.

Neither change alters the underlying quotient spaces or the induced linear
maps. A fixed character twist and the pullback both keep carriers and linear
maps unchanged. Exactness on underlying linear maps is a property of these
maps alone. It therefore does not depend on which character normalizes the
action, so exactness of the four functors is expected from Proposition 3.2(a)
and Proposition 1.9(a). This module states that expectation; it does not
prove it. In particular, clauses 3 and 4 do not depend on the Haar-modulus
comparison.

### Internal packaging

The formulation by underlying linear maps follows the task contract. It uses
`SmoothRep.hom` and the literal injectivity, `range = ker` and surjectivity
conditions in place of a categorical exactness predicate. Short exact
sequences are the form of exactness stated. Grouping the four functors into
one conjunction with the helper `MapsShortExactIntertwiners` is also an
internal choice.

## Remaining proof obligation

A proof of `MinusExactnessStatement F T` must show all four clauses for the
actual radicals and characters, without added hypotheses. In particular it
must prove the following:

- every `radical n F.Carrier` is a limit of compact subgroups for the
  topology `T.topology`;
- the characters `1` and `T.mirabolicTheta ψ n` have the local constancy
  that a localization exactness argument needs;
- the twist and the continuous pullback keep the underlying linear maps.

The published
`Langlands.Jacquet.Localization.characterLocalizationExactness`
(`Langlands.Representation.Jacquet.LocalizationExactnessProof`) is a possible
lower input. Its compact-subgroup, local-constancy, normalizer and
smoothness hypotheses would have to be discharged inside the proof. This
statement adds no finite-length, admissibility, finite-dimensionality,
irreducibility, cuspidality, compact-exhaustion, local-constancy,
Haar-modulus or derivative hypothesis.

## Imports and independence

The module imports only `Langlands.Representation.Derivative.MirabolicMinus`.
Not counting this module, its `Langlands` import closure has 50 modules,
including `MirabolicMinus` itself. They cover groups, local fields, smooth representations, twists, localization and
Whittaker characters. The closure contains no classification, segment,
multisegment, square-integrable, tempered, socle or irreducibility module. It
does not contain `Representation/CompactCoefficient/GroupTransport`. Neither
the module nor its closure uses `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
or any result of the excluded exhaustion, existence, coverage, conversion,
uniqueness or segment-classification tasks. No plus functor, adjunction,
duality, iteration, filtration, pairing or classification result is used or
stated.
