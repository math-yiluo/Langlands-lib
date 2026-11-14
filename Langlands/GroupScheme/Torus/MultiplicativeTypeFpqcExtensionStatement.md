# Statement: fpqc descent and extensions for groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeFpqcExtensionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), for the fibre
  `RelativeIdentityComponent.residueFiber H s` over the residue field of a point;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `i : H' ⟶ H` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `i.hom.hom : H'.X ⟶ H.X`,
and `H.X.hom : H.X.left ⟶ S` is the structure morphism of `H`.

## Predicates used

- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms `S_i ⟶ S` locally of finite presentation)
  such that each base change `H_{S_i}` is isomorphic, as a group scheme over `S_i`, to the
  diagonalizable group `D_{S_i}(Λ_i)` of some finitely generated abelian group `Λ_i`. This
  is Conrad's Definition B.1.1, not the field-level `IsMultiplicativeType` of
  [`Torus.MultiplicativeType`](MultiplicativeType.md).
- `GroupScheme.baseChange b`: base change of group schemes along `b : S' ⟶ S`.
- `RelativeIdentityComponent.residueFiber H s`: the base change of `H` along
  `Spec κ(s) ⟶ S`, a group scheme over the residue field `κ(s)` of `s : S`.
- `SubgroupFunctor.range i`: the subgroup functor of `H` whose `T`-points are the
  `T`-points of `H` that factor through `i`.
- `RelativeRoot.IsFppfQuotient N q` for `q : H ⟶ H''`: the morphism `q.hom.hom.left` is
  flat, surjective and locally of finite presentation, and the subgroup functor of points
  of the scheme-theoretic kernel `kernel q` is exactly `N`.

## Statement and quantifiers

The proposition quantifies over every scheme `S` and is the conjunction of two parts.

1. For every `H : GroupScheme S` with `Flat H.X.hom`, `LocallyOfFinitePresentation H.X.hom`
   and `IsAffineHom H.X.hom`, every scheme `S'` and every morphism `b : S' ⟶ S` that is
   flat, surjective and quasi-compact: if the base change of `H` along `b` is of
   multiplicative type, then `H` is of multiplicative type.
2. For all `H' H H'' : GroupScheme S`, each flat, locally of finite presentation and affine
   over `S`, and homomorphisms `i : H' ⟶ H` and `q : H ⟶ H''` such that
   - `i.hom.hom` is a monomorphism,
   - `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` holds,
   - `H'` and `H''` are of multiplicative type, and
   - for every `s : S`, the underlying scheme of `residueFiber H s` is connected or
     `residueFiber H s` is commutative (`IsCommMonObj`),

   the group `H` is of multiplicative type.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Corollary B.4.2, p.299: "Let S be a scheme, H → S an S-affine fppf group scheme.
  1. If H becomes multiplicative type fpqc-locally on S then it is of multiplicative type.
  2. Consider a short exact sequence 1 → H′ → H → H′′ → 1 of fppf S-affine S-groups with H′
     and H′′ of multiplicative type. If each H_s is either connected or commutative then H
     is of multiplicative type."
- Definition B.1.1, p.280, defines `S`-groups of multiplicative type.

The source remarks after the corollary that (1) shows that SGA 3's notion of multiplicative
type (fpqc-local triviality) agrees with Conrad's (fppf-local triviality) in the finite type
case, and that some fibral hypothesis is needed in (2): a finite constant group over a field
of characteristic `0` built from a non-commutative group of order `p³` is an extension of
one multiplicative type group by another.

Conrad's proof (pp.300–301) derives (1) from the fibral criterion (Theorem B.4.1, p.297). For (2) it
reduces to a complete strictly henselian local noetherian base, lifts the special fibre
with Theorem B.3.2(2), and treats the case of an algebraically closed field directly. This
is explanation only.

## Derivation from the source

- **`S`-affine fppf groups.** "S-affine fppf" for an `S`-group `H` is `IsAffineHom H.X.hom`
  (the structure morphism is affine), `Flat H.X.hom` and
  `LocallyOfFinitePresentation H.X.hom`. In part (2) the source applies this phrase to all
  three groups, and the statement assumes it for `H'`, `H` and `H''`.
- **fpqc-locally.** Part (1) uses one flat, surjective, quasi-compact morphism `b : S' ⟶ S`,
  as the Library does elsewhere for fpqc descent (for example `fieldExtension_fpqc` in
  [`BaseChangeReflection`](../BaseChangeReflection.md)). An fpqc covering family of `S`
  gives such a morphism over each affine open `V` of `S`: finitely many affine opens of
  the members whose images cover `V`, and their disjoint union. Being of multiplicative
  type is local on `S` for the Zariski topology (fppf covers of the members of an open
  cover combine into an fppf cover of `S`). So the single-morphism form of part (1) implies
  the form with fpqc covering families.
- **Short exact sequence.** Exactness of `1 → H' → H → H'' → 1` for fppf groups means that
  `H' → H` is a monomorphism identifying `H'` with the kernel of `H → H''`, and that
  `H → H''` is an fppf surjection. The statement encodes this as `Mono i.hom.hom` together
  with `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`. The second condition says
  that `q` is flat, surjective and locally of finite presentation, and that the points of
  the kernel of `q` are exactly the points that factor through `i`.
- **Fibres.** `H_s` is the fibre of `H` over the residue field `κ(s)`, which is
  `residueFiber H s`. "Connected" is `ConnectedSpace` of its underlying scheme, and
  "commutative" is `IsCommMonObj` of its underlying monoid object. The condition is
  imposed separately at each point, so different points may satisfy different
  alternatives, as in the source.

## Scope

All schemes are in universe `u`, including the fpqc source `S'` in part (1). The base `S`
is arbitrary, as in the source. The statement does not include the source's remark on
SGA 3's definition or its counterexample.
