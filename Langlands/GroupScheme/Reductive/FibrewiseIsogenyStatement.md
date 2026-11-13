# Statement: fibrewise isogenies of reductive group schemes are isogenies

Worker 75.

`Langlands.GroupScheme.ReductiveFibrewiseIsogenyStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md), for `IsIsogeny`;
- [`Reductive.Basic`](Basic.md), for `IsReductive`; the base-change functor
  `GroupScheme.baseChange` of [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)
  comes transitively.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ G` in it is a homomorphism of group
schemes over `S`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field. This is
  Conrad's reductive group scheme (Definition 3.1.1).
- `IsIsogeny f`, for a homomorphism `f : H ⟶ G` of group schemes over a scheme `S`: the
  underlying morphism of schemes `f.hom.hom.left` is finite, flat and surjective (Mathlib's
  `IsFinite`, `Flat` and `Surjective`). This is exactly Conrad's Definition 3.3.9 of an
  isogeny between smooth `S`-affine `S`-groups, "a finite flat surjection". The Library
  predicate is defined for all group-scheme homomorphisms; here it is applied only to
  homomorphisms of reductive groups and their fibres, which are smooth and affine.
- `S.fromSpecResidueField s : Spec κ(s) ⟶ S` is Mathlib's canonical morphism from the
  spectrum of the residue field `κ(s)` at a point `s ∈ S`. The fibre `f_s : G'_s ⟶ G_s` of
  `f` at `s` is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map f`, the pullback of
  `f` to `Spec κ(s)` with the induced group laws.

## Statement and quantifiers

The proposition quantifies over every scheme `S`, every pair of group schemes
`G' G : GroupScheme S` with `IsReductive G'` and `IsReductive G`, and every homomorphism
`f : G' ⟶ G`. It asserts:

```
(∀ s : S, IsIsogeny f_s) → IsIsogeny f
```

that is, if the fibre of `f` over the residue field of every point of `S` is a finite flat
surjection, then `f` itself is a finite flat surjection.

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
- Discussion after Definition 3.3.9, p.103: if `f_s` is an isogeny for all `s ∈ S` then `f`
  is surjective and flat (fibral flatness criterion), and the question is whether `f` is
  finite; "We shall give affirmative answers in the reductive case. ... the general case lies
  a bit deeper (see Proposition 6.1.10)."
- Proposition 6.1.10, p.192: "Let f : G′ → G be a homomorphism between reductive group
  schemes. If f_s is an isogeny for all s ∈ S then f is an isogeny."

## Derivation from the source

- **Reductive group schemes.** Conrad's "reductive group schemes" over `S` are `IsReductive`
  (Definition 3.1.1). Both `G'` and `G` are reductive over the same base `S`.
- **`f_s`.** In Conrad, `f_s` is the fibre of `f` over the point `s ∈ S`, that is its base
  change to `Spec κ(s)`. This is `(GroupScheme.baseChange (S.fromSpecResidueField s)).map f`.
  The fibres `G'_s` and `G_s` are smooth affine `κ(s)`-groups, so Definition 3.3.9 applies to
  `f_s` over the base `Spec κ(s)`.
- **Isogeny.** Both the hypothesis on `f_s` and the conclusion on `f` use Definition 3.3.9,
  which is `IsIsogeny`: finite, flat and surjective underlying morphism.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary; no noetherian, locally
noetherian or connectedness hypothesis is imposed, as in the source. No centrality of the
kernel is assumed or concluded.

The Library's [`FiberwiseIsogenyStatement`](../../AbelianScheme/FiberwiseIsogenyStatement.md)
has the same shape for smooth proper group schemes, and its fibres are formed by the same
pullback (`GroupScheme.baseChange f` is the abbreviation `(Over.pullback f).mapGrp`). The
present statement is the smooth affine reductive case, which is a separate result.

## Not stated

The statement does not assert Conrad's Proposition 3.3.10 (central isogenies are detected
on fibres), the existence or finiteness of the scheme-theoretic kernel `ker f`, that `G` is
the fppf quotient `G'/ker f`, or the quasi-finiteness and flatness of `f` that the proof
derives first. It says nothing about homomorphisms between non-reductive smooth affine
groups; Conrad's discussion on p.103 raises that question and answers it only in the
reductive case.
