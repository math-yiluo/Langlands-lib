# Statement: parabolic subgroups of reductive group schemes are self-normalizing

Worker 3483.

`Langlands.GroupScheme.RelativeParabolicSelfNormalizerStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Rational.TorusNormalizer`](Rational/TorusNormalizer.md) (for
`SubgroupFunctor.normalizer`) and [`Absolute.Borel`](Absolute/Borel.md) (for
`IsParabolicSubgroup`).

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`;
- every pair of group schemes `G P : GroupScheme (Spec (CommRingCat.of R))`;
- every group-scheme homomorphism `i : P ⟶ G`.

It has four hypotheses:

1. `IsReductive G`, the Library's predicate for reductive group schemes over a base scheme
   ([`Reductive.Basic`](Reductive/Basic.md)). It requires `G` to be smooth and affine over
   `Spec R`, and its geometric fibre at every point `s`, taken over the chosen algebraic
   closure of the residue field, must satisfy `IsPseudoReductive`. Over an algebraically
   closed field that means smooth, connected and affine with trivial unipotent radical, so
   the geometric fibres are connected reductive groups.
2. `Smooth P.X.hom`: the subgroup is smooth over `Spec R`.
3. `IsClosedSubgroup i`: the underlying scheme morphism `i.hom.hom.left` is a closed
   immersion.
4. For every field `k : Type u` and every ring homomorphism `R → k` (an instance
   `Algebra R k`), the base change of `i` along `Spec.algebraMap R k` satisfies
   `IsParabolicSubgroup` ([`Absolute.Borel`](Absolute/Borel.md)): a smooth closed subgroup
   that contains a Borel subgroup after base change to `AlgebraicClosure k`, through an
   actual factorization.

These are exactly the hypotheses of the published
`RelativeParabolicQuotient.ExistenceStatement`
([`RelativeParabolicQuotientStatement`](RelativeParabolicQuotientStatement.md)), with the
closed-immersion hypothesis written as `IsClosedSubgroup i`, which is by definition
`IsClosedImmersion i.hom.hom.left`.

The conclusion is the equality of subgroup functors

```lean
(SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i
```

- `SubgroupFunctor.range i` assigns to each test `U : Over (Spec (CommRingCat.of R))` the
  subgroup of points `U ⟶ G.X` that factor through `i`, namely the points `y ≫ i.hom.hom`
  with `y : U ⟶ P.X`.
- `SubgroupFunctor.normalizer F`
  ([`Rational.TorusNormalizer`](Rational/TorusNormalizer.md)) assigns to `U` the points
  `g : U ⟶ G.X` such that, for every test `V`, every morphism `a : V ⟶ U` and every
  `x ∈ F(V)`, both `(a ≫ g) * x * (a ≫ g)⁻¹` and `(a ≫ g)⁻¹ * x * (a ≫ g)` belong to `F(V)`.

So a point of `G` over any `R`-scheme `U` normalizes `P_U` exactly when it is a point of
`P`. The tests are arbitrary schemes over `Spec R`, including non-affine and nonreduced
ones; the equality is the scheme-theoretic statement `N_G(P) = P`, not only an equality of
field-valued points.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Corollary 5.2.8, p.155, first assertion: "For any parabolic subgroup P in a reductive
  group scheme G, the normalizer functor N_G(P) is represented by P." (The second
  assertion, on the quotient `G/P`, continues on p.156.)
- Definition 5.2.1, p.151: "A parabolic subgroup of a reductive group scheme G → S is a
  smooth S-affine S-group P equipped with a monic homomorphism P → G such that P_s is
  parabolic in G_s (i.e., G_s/P_s is proper) for all s ∈ S."
- Proposition 5.2.3, p.152: for such `Q`, "Q → G is a closed immersion".
- Definition 3.1.1, p.81: a reductive `S`-group is a smooth `S`-affine group scheme whose
  geometric fibres are connected reductive groups.

## Derivation from the source

The Lean proposition is the first assertion of Corollary 5.2.8 for an affine base
`S = Spec R`, under hypotheses that imply the source's.

- Hypothesis 1 is Definition 3.1.1.
- Hypotheses 2 and 3 make `P` smooth, `S`-affine (closed in the affine `G`) and monic in
  `G`.
- For a point `s` with residue field `κ(s)`, hypothesis 4 at `k = κ(s)` says that `P_s`
  contains a Borel subgroup after base change to an algebraic closure. Over a field this is
  equivalent to properness of `G_s/P_s`: properness can be checked after the faithfully
  flat extension to the algebraic closure, where parabolic subgroups are the closed
  subgroups containing a Borel subgroup (Conrad's discussion after Theorem 1.1.8, p.9).
  The published Markdown of `ParabolicSelfNormalizerStatement`
  ([`Rational.ParabolicNormalizerStatement`](Rational/ParabolicNormalizerStatement.md))
  and of `RelativeParabolicQuotient.ExistenceStatement` explain the same comparison.

So `i` is a parabolic subgroup in the sense of Definition 5.2.1, and Corollary 5.2.8 gives
that the normalizer functor `N_G(P)` is represented by `P`. Since `P → G` is a closed
immersion, this says that `N_G(P)(U) = P(U)` inside `G(U)` for every `S`-scheme `U`, which
is the Lean equality. Hypothesis 4 tests every field-valued point, not only residue fields,
and hypothesis 3 is a conclusion of Proposition 5.2.3 in the source; so the Lean hypotheses
are at least as strong as the source's, and the proposition is no stronger than the
source result.

## Scope

All objects are in universe `u`; the field tests are in `Type u`. The ring `R` is
arbitrary: it need not be Noetherian, local, a domain or of positive dimension, and the
case `P = G` is included. No maximal torus, Borel subgroup over `R`, cocharacter or
splitting is assumed. Conrad's base `S` may be any scheme; the Lean statement covers affine
bases. The second assertion of Corollary 5.2.8 (representability and properness of `G/P`)
is the published `RelativeParabolicQuotient.ExistenceStatement` and is not part of this
proposition.

## Relation to the Library

- `ParabolicSelfNormalizerStatement`
  ([`Rational.ParabolicNormalizerStatement`](Rational/ParabolicNormalizerStatement.md)) is
  the case of a field.
- `RelativeSelfNormalizerStatement`
  ([`RelativeSelfNormalizerStatement`](RelativeSelfNormalizerStatement.md)) detects
  self-normalization of a smooth closed subgroup with geometrically connected fibres by
  testing all field-valued base changes.
- The published theorem `RelativeParabolicNormalizerReduction.normalizer_eq_of_statements`
  ([`RelativeParabolicNormalizerReduction`](RelativeParabolicNormalizerReduction.md))
  derives this conclusion from `RelativeSelfNormalizerStatement`,
  `ParabolicSelfNormalizerStatement` and `ParabolicDynamicStatement` taken as hypotheses.
  It is a theorem with hypotheses, not a named closed proposition; the family 8 ledger
  records the closed proposition as missing.

This module proves none of these relations.
