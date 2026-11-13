# Statement: the derived group of a reductive group scheme over a base

Worker 75.

`Langlands.GroupScheme.RelativeDerivedGroupStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Reductive.Semisimple`](Semisimple.md), for the field predicate `IsSemisimple`;
  `IsReductive`, `geometricFiber` and `IsClosedSubgroup` come transitively from
  [`Reductive.Basic`](Basic.md);
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`Torus.Relative`](../Torus/Relative.md), for `RelativeTorus.IsTorus`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Flat`, for `Flat`.

`SubgroupFunctor.range` and `SubgroupFunctor.IsNormal` come from
[`SubgroupFunctor`](../SubgroupFunctor.md).

## The local predicate `Admissible`

The statement begins with a local `let`. For a scheme `S'`, group schemes
`G' D' : GroupScheme S'` and a homomorphism `d : D' ⟶ G'`, `Admissible d` is the
conjunction of:

1. `IsClosedSubgroup d`: the underlying morphism of schemes of `d` is a closed immersion.
2. `(SubgroupFunctor.range d).IsNormal`: for every `T : Over S'`, the subgroup of
   `T`-points of `G'` that factor through `d` is normal in the group of all `T`-points.
3. `IsReductive D'`: `D'` is smooth and affine over `S'`, and every geometric fibre
   `geometricFiber D' s` satisfies `IsPseudoReductive`. Over an algebraically closed
   field this means smooth, connected and affine with trivial unipotent radical.
4. `∀ s : S', IsSemisimple (geometricFiber D' s)`: every geometric fibre of `D'`, over
   the chosen algebraic closure of the residue field `κ(s)`, is connected reductive with
   finite scheme-theoretic centre.
5. There are a group scheme `Q` over `S'` and a homomorphism `q : G' ⟶ Q` with
   `RelativeTorus.IsTorus Q` and `RelativeRoot.IsFppfQuotient (range d) q`. The first
   says that `Q` becomes a finite split torus on some étale cover of `S'`. The second
   says that the underlying morphism of `q` is flat, surjective and locally of finite
   presentation, and that the range of the scheme kernel of `q` is the range of `d`.

Conditions 3 and 4 say that `D'` is a semisimple `S'`-group. Condition 5 says that
`G'/D'` exists as a represented fppf quotient and is an `S'`-torus.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S` with `IsReductive G`. It asserts that there are a group scheme
`D : GroupScheme S` and a homomorphism `d : D ⟶ G` with `Admissible d` and the following
four properties.

1. **Uniqueness.** For every `D' : GroupScheme S` and `d' : D' ⟶ G` with
   `Admissible d'`, `SubgroupFunctor.range d' = SubgroupFunctor.range d`.
2. **Commutator sheaf.** For every `T : Over S` and every `T`-point `x : T ⟶ G.X`, `x`
   factors through `d` if and only if there is a cover `𝒰` of the scheme `T.left` in the
   precoverage `Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)` such that,
   for every index `i`, the restriction of `x` along `𝒰.f i` lies in the commutator
   subgroup `_root_.commutator` of the group of points of `G` over
   `Over.mk (𝒰.f i ≫ T.hom)`. A cover in this precoverage is a jointly surjective family
   of flat morphisms locally of finite presentation, indexed by a type in universe `u`,
   that is, an fppf covering family.
3. **Base change.** For every scheme `S'` and morphism `b : S' ⟶ S`,
   `Admissible ((GroupScheme.baseChange b).map d)`.
4. **Universal property.** For every group scheme `Q` over `S` and every
   `q : G ⟶ Q` with `RelativeRoot.IsFppfQuotient (range d) q`, and every group scheme
   `A` over `S` whose group object is commutative (`IsCommMonObj A.X`), every
   homomorphism `φ : G ⟶ A` factors as `q ≫ ψ` for exactly one homomorphism
   `ψ : Q ⟶ A`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Theorem 5.3.1, p.160: "Let G → S be a reductive group scheme. There is a unique
  semisimple closed normal S-subgroup D(G) ⊂ G such that G/D(G) is a torus. Moreover,
  D(G) represents the fppf-sheafification of the 'commutator subfunctor'
  S′ ↝ [G(S′), G(S′)] on the category of S-schemes. In particular, the quotient map
  G → G/D(G) is initial among all homomorphisms from G to an abelian sheaf, and the
  formation of D(G) commutes with any base change on S."
- Proof of Theorem 5.3.1, pp.160–163: `D(G)` is constructed étale-locally as the kernel
  of a smooth surjection `G → T/T'`, and it is shown that every semisimple `S`-group is
  its own commutator subsheaf for the fppf topology, which gives the uniqueness.
- Definition 3.1.1, p.81: "An S-torus is an S-group T → S of multiplicative type with
  smooth connected fibers. A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s are connected reductive groups. A semisimple
  S-group is a reductive S-group whose geometric fibers are semisimple." The text after
  the definition notes that any `S`-torus becomes a power of `G_m` étale-locally on `S`
  (Proposition B.3.4).

## Derivation from the source

- "Semisimple S-subgroup" is conditions 3 and 4 of `Admissible`, following
  Definition 3.1.1. One geometric point over each `s` suffices, as the source remarks
  after Definition 3.1.1, so the chosen algebraic closure of `κ(s)` is used.
- "Closed normal S-subgroup" is conditions 1 and 2. The subgroup is given as a closed
  immersion `d`, and normality is normality of its functor of points.
- "G/D(G) is a torus" is condition 5. The quotient is an fppf quotient of group
  schemes, represented by a flat surjective morphism locally of finite presentation
  whose kernel is `D(G)`. The target is an `S`-torus in the étale-local sense
  `RelativeTorus.IsTorus`, which is equivalent to Definition 3.1.1 by Proposition B.3.4.
- "Unique" is property 1. Subgroups given by monomorphisms are compared through their
  ranges.
- "D(G) represents the fppf-sheafification of the commutator subfunctor" is property 2.
  The commutator subfunctor is a subpresheaf of the fppf sheaf `G`. Its sheafification
  is the subsheaf of `G` whose `T`-points are the points that lie in the subpresheaf
  after restriction to the members of some fppf covering family of `T`. Property 2 says
  that `D(G)` has exactly these points.
- "The formation of D(G) commutes with any base change on S" is property 3: the base
  change of `D(G) ⊂ G` along `S' ⟶ S` again satisfies the defining properties over `S'`.
  With property 1 applied over `S'`, this identifies it with `D(G_{S'})`.
- "The quotient map G → G/D(G) is initial among all homomorphisms from G to an abelian
  sheaf" is property 4, restricted to abelian sheaves represented by commutative
  `S`-group schemes. It is stated for every represented fppf quotient `q` of `G` by
  `D(G)`, not only for one with torus target.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus or splitting of `G` is assumed. The Library's
[`Derived.StructureStatement`](../Derived/StructureStatement.md) concerns the
scheme-theoretic derived subgroup of an affine group over a field. The present
statement concerns reductive groups over a general base. Neither contains the other.

## Not stated

Property 4 covers only abelian sheaves represented by commutative group schemes over
`S`, not arbitrary abelian fppf sheaves, because the Library has no category of fppf
sheaves over a general base. The construction of `D(G)` in the proof (the open cell
`U⁻ × T' × U⁺` and the subtorus `T'` generated by the coroots) is not stated.
