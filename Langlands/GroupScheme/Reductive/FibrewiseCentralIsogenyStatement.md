# Statement: central isogenies of reductive group schemes are detected on fibres

Worker 75.

`Langlands.GroupScheme.ReductiveFibrewiseCentralIsogenyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md), for `IsCentralIsogeny`; it brings
  `IsIsogeny` ([`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md)), the kernel
  `kernel f` with its inclusion `kernelι f`
  ([`AbelianScheme.Kernel`](../../AbelianScheme/Kernel.md)) and `IsCentral`
  ([`Rational.Characters`](../Rational/Characters.md)) transitively;
- [`Reductive.Basic`](Basic.md), for `IsReductive`; the base-change functor
  `GroupScheme.baseChange` of [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)
  comes transitively;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `IsFinite`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ G` in it is a homomorphism of group
schemes over `S`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field. This is
  Conrad's reductive group scheme (Definition 3.1.1).
- `kernel f` and `kernelι f : kernel f ⟶ G'`, for `f : G' ⟶ G`: the scheme-theoretic kernel,
  the pullback of `f` along the unit section of `G`, with its inclusion into `G'`. Its points
  on a test scheme are exactly the points of `G'` killed by `f`.
- `IsCentral i`, for `i : H ⟶ G'`: every point of `H` on every test scheme maps into
  `center G'`, the all-test centre of `G'`. Applied to `kernelι f`, this says that
  `ker f` is central in `G'` as a subgroup scheme.
- `IsCentralIsogeny f`: `IsIsogeny f` (the underlying morphism of schemes is finite, flat
  and surjective), the underlying morphism is locally of finite presentation, and
  `IsCentral (kernelι f)`. This is Conrad's Definition 3.3.9 of a central isogeny, "a finite
  flat surjection" whose kernel is central. Local finite presentation is part of the Library
  predicate; for a homomorphism of reductive groups it is automatic, since both groups are
  locally of finite presentation over `S`.
- `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism from the
  spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre `f_s : G'_s ⟶ G_s` of
  `f` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map f`, the pullback of
  `f` to `Spec κ(s)` with the induced group laws.

## Statement and quantifiers

The proposition quantifies over every scheme `S`, every pair of group schemes
`G' G : GroupScheme S` with `IsReductive G'` and `IsReductive G`, and every homomorphism
`f : G' ⟶ G` whose underlying morphism of schemes is surjective
(`Surjective f.hom.hom.left`). It asserts

```
IsCentralIsogeny f ↔
  ∀ s : S, IsFinite (kernel f_s).X.hom ∧ IsCentral (kernelι f_s)
```

that is, `f` is a central isogeny if and only if, for every point `s ∈ S`, the kernel of the
fibre `f_s` is finite over `κ(s)` and central in `G'_s`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers.

- Definition 3.3.9, p.103: "A homomorphism f : G′ → G between smooth S-affine S-groups is
  an isogeny if it is a finite flat surjection, and is a central isogeny if also ker f is
  central in G′."
- Proposition 3.3.10, p.103: "A surjective homomorphism f : G′ → G between reductive groups
  over a scheme S is a central isogeny if and only if f_s has finite central kernel for all
  s ∈ S."

Conrad's proof (p.103) obtains flatness of `f` from the fibral flatness criterion, proves
centrality of `K = ker f` over artin local bases by lifting the special fibre of `K` into the
multiplicative type centre `Z_{G'}`, and then deduces finiteness of `K` from its being a
quasi-finite closed subgroup of the multiplicative type group `Z_{G'}`. This is explanation
only.

## Derivation from the source

- **Reductive group schemes.** Conrad's "reductive groups over a scheme S" are
  `IsReductive` (Definition 3.1.1). Both `G'` and `G` are reductive over the same base `S`.
- **Surjective homomorphism.** The hypothesis "surjective" is surjectivity of the
  underlying morphism of schemes, `Surjective f.hom.hom.left`.
- **Central isogeny.** The left side of the equivalence is Definition 3.3.9, encoded by the
  Library predicate `IsCentralIsogeny` (see above for the local finite presentation field).
- **`f_s` has finite central kernel.** `f_s` is the fibre of `f` over the point `s`, its base
  change to `Spec κ(s)`. Its kernel is the scheme-theoretic kernel `kernel f_s`; "finite" is
  `IsFinite` of its structure morphism to `Spec κ(s)`, and "central" is `IsCentral` of its
  inclusion into `G'_s`, i.e. centrality as a subgroup scheme, matching the centrality
  condition of Definition 3.3.9 over the base `Spec κ(s)`.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary; no noetherian or connectedness
hypothesis is imposed, as in the source. Both directions of the equivalence are stated; the
source calls the forward direction obvious.

## Related Library statements

- `ReductiveFibrewiseIsogenyStatement`
  ([`FibrewiseIsogenyStatement`](FibrewiseIsogenyStatement.md)) is Conrad's Proposition
  6.1.10, which detects isogenies (without centrality) on fibres; its Markdown records that
  Proposition 3.3.10 was not stated there.
