# Statement: reductive fibral identity components are open, closed and of étale index

Worker 75.

`Langlands.GroupScheme.IdentityComponentClopenStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Reductive.Basic`](Basic.md), which provides `IsReductive` and `IsConnectedReductive`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), which provides
  `IsRelativeIdentityComponent` and the residue-field fibre
  `RelativeIdentityComponent.residueFiber`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  which provides `RelativeRoot.IsFppfQuotient`;
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, for `Etale` and `IsSeparated`.

`GroupScheme S` is `Grp (Over S)` (from `Langlands.AbelianScheme.GroupScheme`), and
`SubgroupFunctor.range i` is the subgroup functor of points of `G` that factor through `i`.

It states Conrad's Proposition 3.1.3: for a smooth separated finitely presented group
scheme whose fibral identity components are reductive, the relative identity component
is a reductive group scheme, it is open and closed, and the component group is a
separated étale group scheme of finite presentation.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with the instances `Smooth G.X.hom`,
  `IsSeparated G.X.hom` and `QuasiCompact G.X.hom`. In Mathlib a smooth morphism is
  locally of finite presentation and a separated morphism is quasi-separated, so these
  say that `G → S` is smooth, separated and of finite presentation, as in Conrad;
- a group scheme `H : GroupScheme S` and a homomorphism `i : H ⟶ G` with
  `IsRelativeIdentityComponent G i`. This says that the underlying morphism of `i` is an
  open immersion and that, on every test scheme `T` over `S`, a point `x : T ⟶ G` factors
  through `i` exactly when for every `s ∈ S` the image of its fibre `x_s` lies in the
  connected component of the identity of the residue-field fibre `G_s`. So `H` is Conrad's
  open subgroup `G⁰`. For smooth `G` such an `H` exists
  (`RelativeIdentityComponent.SmoothExistenceStatement` in
  [`RelativeIdentityComponentStatements`](../RelativeIdentityComponentStatements.md)), so
  the quantification over `H` and `i` is not vacuous once that statement is proved;
- a proof that for every point `s : S` the residue-field fibre
  `RelativeIdentityComponent.residueFiber H s` is connected reductive
  (`IsConnectedReductive`). This fibre is the base change of `H` along
  `Spec κ(s) ⟶ S`, which is Conrad's `G⁰_s`. For a group `K` over a field `k`,
  `IsConnectedReductive K` asks that `K` be smooth, affine and connected over `k`, and that
  the unipotent radical of `K` base-changed to the algebraic closure of `k` be trivial.

## Conclusion

The conclusion is the conjunction of three assertions.

1. `IsReductive H`: `H` is smooth and affine over `S`, and each geometric fibre is a
   smooth connected affine group with trivial unipotent radical. This is Conrad's "`G⁰`
   is a reductive `S`-group".
2. `IsClosedImmersion i.hom.hom.left`: the open immersion `G⁰ ⟶ G` is also a closed
   immersion, so `G⁰` is open and closed in `G`.
3. There are a group scheme `E : GroupScheme S` and a homomorphism `q : G ⟶ E` with
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, and `E → S` is étale
   (`Etale`), separated (`IsSeparated`) and quasi-compact (`QuasiCompact`).
   `IsFppfQuotient N q` asks that the underlying morphism of `q` be flat, surjective and
   locally of finite presentation, and that the subgroup functor of points of the kernel
   of `q` be `N`. So `E` represents the fppf quotient sheaf `G/G⁰`. An étale morphism is
   locally of finite presentation, so `E` is a separated étale `S`-group of finite
   presentation.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 3.1.3, p.82: "Let G → S be a smooth separated group scheme of finite
  presentation such that G⁰_s is reductive for all s ∈ S. Then G⁰ is a reductive S-group
  that is open and closed in G, and G/G⁰ exists as a separated étale S-group of finite
  presentation." The proof is on pp.82–83.
- p.81: "for any smooth group scheme G → S of finite presentation there exists a unique
  open subgroup scheme G⁰ ⊂ G such that (G⁰)_s is the identity component of G_s for all
  s ∈ S [EGA, IV₃, 15.6.5]."
- Definition 3.1.1, p.81: "A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s̄ are connected reductive groups."

## Derivation from the source

- **`G⁰`.** Conrad uses the open subgroup `G⁰` of p.81 without constructing it in this
  proposition. The proposition takes any open subgroup `H`
  satisfying the Library's all-test criterion `IsRelativeIdentityComponent G i` as `G⁰`.
- **Hypothesis.** "`G⁰_s` is reductive" refers to the fibre of `G⁰` over `k(s)`, which is
  the identity component of `G_s`. A reductive group over a field is a smooth connected
  affine group whose geometric fibre has trivial unipotent radical (Definition 3.1.1 over
  `Spec k`); this is `IsConnectedReductive` of the residue-field fibre of `H`.
- **Open and closed.** Openness is part of `IsRelativeIdentityComponent`, so only
  closedness is stated.
- **Quotient.** Conrad's "`G/G⁰` exists as a separated étale `S`-group of finite
  presentation" is read as representability of the fppf quotient sheaf by such a group
  scheme, with the quotient map. `RelativeRoot.IsFppfQuotient` is the Library's encoding of
  a represented fppf quotient, used for example in
  `RelativeParabolicReductiveQuotientStatement` in
  [`RelativeLevi.ReductiveQuotientStatement`](../RelativeLevi/ReductiveQuotientStatement.md).
  The conditions "finite presentation" on `E` are `QuasiCompact`, quasi-separatedness
  (implied by `IsSeparated`) and local finite presentation (implied by `Etale`).

## Scope

All objects are in universe `u`. The proposition does not state:

- the existence of `G⁰` (that is `RelativeIdentityComponent.SmoothExistenceStatement`);
- the ingredients of Conrad's proof: SGA 3, XVI, 5.2(i) (finite presentation may replace
  affineness in the definition of a reductive group scheme), Theorem 5.3.5 (a monic
  homomorphism from a reductive group scheme to a finitely presented separated group
  scheme is a closed immersion), and Knutson's criterion for the algebraic space `G/G⁰`
  to be a scheme;
- Example 3.1.4 (`G/G⁰` need not be finite over `S`) or Proposition 3.1.12 (closedness of
  the locus of connected fibres when `G` is affine).

## Relation to the Library

- `RelativeIdentityComponent.SmoothExistenceStatement`,
  `RelativeIdentityComponent.SmoothNormalityStatement` and
  `RelativeIdentityComponent.SmoothBaseChangeStatement` in
  [`RelativeIdentityComponentStatements`](../RelativeIdentityComponentStatements.md)
  give existence, normality and base change of `G⁰` for smooth `G`.
- `RelativeIdentityComponent.SmoothDvrAffinenessStatement` in
  [`RelativeIdentityComponentDvrAffinenessStatement`](../RelativeIdentityComponentDvrAffinenessStatement.md)
  states that `G⁰` is affine for a smooth affine group over a discrete valuation ring.

This module proves none of these relations.
