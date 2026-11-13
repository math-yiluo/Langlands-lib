# Statement: monomorphisms out of reductive group schemes are closed immersions

Worker 75.

`Langlands.GroupScheme.ReductiveMonomorphismClosedImmersionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`Reductive.Basic`](Basic.md), for
`IsReductive`, and Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, for
`LocallyOfFinitePresentation`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every pair of group schemes `G G' : GroupScheme S`;
- every group-scheme homomorphism `f : G ⟶ G'`.

It has five hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](Basic.md)): `G` is smooth and affine over `S`,
   and its geometric fibre at every point `s`, over the chosen algebraic closure of the
   residue field `κ(s)`, satisfies `IsPseudoReductive`. Over an algebraically closed
   field this means smooth, connected and affine with trivial unipotent radical, so the
   geometric fibres are connected reductive groups.
2. `IsSeparated G'.X.hom`: the structure morphism `G' → S` is separated.
3. `LocallyOfFinitePresentation G'.X.hom`: it is locally of finite presentation.
4. `QuasiCompact G'.X.hom`: it is quasi-compact.
5. `Mono f.hom.hom.left`: the underlying morphism of schemes of `f` is a monomorphism
   in the category of schemes.

The conclusion is `IsClosedImmersion f.hom.hom.left`: the underlying morphism of schemes
of `f` is a closed immersion.

Hypotheses 2–4 together say that `G'` is a separated `S`-group of finite presentation.
A morphism of finite presentation is locally of finite presentation, quasi-compact and
quasi-separated, and the last condition follows from separatedness. No flatness,
smoothness, affineness or fibre condition is imposed on `G'`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Theorem 5.3.5, p.165: "For a reductive group G → S, any monic homomorphism
  f : G → G′ to a separated S-group of finite presentation is a closed immersion. In
  particular, if G is an adjoint semisimple S-group then Ad_G : G → GL(g) is a closed
  immersion."
- Remarks after Theorem 5.3.5, p.165: the result is also [SGA3, XVI, 1.5(a)]. The
  conclusion fails if `G'` is only locally of finite presentation (Néron lft models of
  split tori), and it fails if reductivity of `G` is weakened to "smooth affine with
  connected fibres" (Example 3.1.2).
- Proof of Theorem 5.3.5, p.166: "monicity means that the diagonal Δ_f : G → G ×_{G′} G
  is an isomorphism".
- Definition 3.1.1, p.81 (reductive group schemes).

## Derivation from the source

The proposition is the first sentence of Theorem 5.3.5.

- "Reductive group G → S" is `IsReductive G` over an arbitrary scheme `S`.
- "Monic homomorphism" is a homomorphism of `S`-groups that is a monomorphism of
  `S`-schemes, as the proof's reformulation through the diagonal `Δ_f` shows. A morphism
  of `S`-schemes is a monomorphism over `S` exactly when it is a monomorphism of
  schemes, since monomorphisms are detected by the diagonal and fibre products over `G'`
  are the same in both categories. The Lean hypothesis is the scheme-level
  `Mono f.hom.hom.left`, as in the Library's field-level
  [`FiniteTypeMonomorphismStatement`](../FiniteTypeMonomorphismStatement.md).
- "Separated S-group of finite presentation" is hypotheses 2–4 on the structure morphism
  of `G'`, as explained above.
- "Closed immersion" is Mathlib's `IsClosedImmersion` of the underlying morphism of
  schemes.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus or splitting of `G` is assumed. The Library's field-level
`FiniteTypeMonomorphismStatement` concerns an arbitrary separated finite-type group
over a field instead of a reductive group over a base; neither statement contains the
other.

## Not stated

The second sentence of Theorem 5.3.5, that the adjoint representation
`Ad_G : G → GL(g)` of an adjoint semisimple `S`-group is a closed immersion, is not
stated. The Library has no relative adjoint semisimple predicate and no quasi-coherent
Lie algebra `g` with its group `GL(g)` over a general base. The source deduces that
sentence from the first one and Proposition 3.3.8.
