# Statement: a maximal torus of a connected reductive group is its own centralizer

Worker 303. This module states one proposition and proves nothing:
`Langlands.GroupScheme.MaximalTorusCentralizerStatement`.

Let `k` be a field and `G` a group scheme over `Spec k` with
`IsConnectedReductive G`. That is, `G` is smooth, affine and connected, and the
base change of `G` to an algebraic closure of `k` has trivial unipotent
radical. Let `T` be a commutative group scheme over `Spec k` and
`j : T ⟶ G` a homomorphism with `IsMaximalTorus j`: `T` is a torus (it splits
over some field extension), `j` is a closed subgroup, and `j` factors through
no strictly larger closed torus of `G`. The statement asserts the equality of
subgroup functors of `G`

`torusCentralizer j = SubgroupFunctor.range j`.

The subgroup functors are compared as actual subgroup functors, on every test
scheme `U` over `Spec k`, nonaffine and nonreduced ones included. The two
sides are:

- `torusCentralizer j` (published in `Rational/TorusCentralizer`). Over `U`
  it consists of the points `g` of `G` such that, for every `U`-scheme
  `a : V ⟶ U` and every point `t` of `T` over `V`, the points `a ≫ g` and
  `t ≫ j` of `G` commute. This is the functor of points of the
  scheme-theoretic centralizer `C_G(T)`.
- `SubgroupFunctor.range j` (published in `SubgroupFunctor`). Over `U` it
  consists of the points of `G` that factor through `j`.

So the statement says that the centralizer of `T` is exactly `T`, as a
subgroup functor and therefore as a closed subgroup scheme.

## Source

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
Corollary 17.84, printed p.379 (PDF p.395): "A torus `T` in a reductive group
`G` is maximal if and only if `C_G(T) = T`". The Lean statement is the
"only if" direction. The converse, which Milne calls obvious, is not stated
here.

The conventions match the Library definitions as follows.

- Milne's reductive groups are connected (Definition 6.46, printed p.135,
  PDF p.151): a connected group variety whose geometric unipotent radical is
  trivial. This is the published `IsConnectedReductive`.
- Milne's tori in `G` are algebraic subgroups that are tori, and maximality is
  maximality among them. This is the published `IsMaximalTorus`, which ranges
  over closed tori.
- No splitness of `T` is assumed. Milne's statement holds for every maximal
  torus. In the intended application, `RegularCocharacterBorelStatement`,
  `T` is split.

Milne's proof combines two results:

- Theorem 17.82: a torus is maximal if and only if it stays maximal after
  extending the base field. This rests on Grothendieck's theorem (17.81).
- Proposition 17.61(a): over an algebraically closed field, `C_G(T) = T` for a
  maximal torus. This uses Borel subgroups (17.39, 17.38, 17.56).

The formation of centralizers commutes with base change. The Milne errata
snapshot of 2026-11-02 (`milne-2017-algebraic-groups-errata-2026-11-02`) has
no entry for these items.

## Use

This is the missing centralizer input for clause 1 of
`Langlands.GroupScheme.RegularCocharacterBorelStatement`, proof task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`. That task also needs a second input,
`GenericCentralizerStatement` (`Rational/Statement`). That statement is
published but not yet proved. Its proof is the open target of task
`07f71149-a274-48a4-9fc8-e29fd7e04cb9`. For a split maximal torus and a regular
cocharacter `ν`, it identifies `Dynamic.centralizer (ν ≫ j)` with
`torusCentralizer j`. Once both statements are proved, they will combine to
identify the dynamic Levi subgroup `Z(ν)` with `T`. Until then, neither
prerequisite is available as a proved result.
