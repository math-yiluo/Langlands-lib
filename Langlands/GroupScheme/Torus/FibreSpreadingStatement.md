# Statement: a torus fibre spreads to a Zariski neighbourhood

Worker 75.

`Langlands.GroupScheme.TorusFibreSpreadingStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Torus.Lattice`](Lattice.md), which provides the field-level predicate `IsTorus`;
- [`Torus.Relative`](Relative.md), which provides the relative predicate
  `RelativeTorus.IsTorus`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), which provides the
  residue-field fibre `RelativeIdentityComponent.residueFiber`;
- Mathlib's `Flat` and `LocallyOfFinitePresentation` morphism properties
  (`Mathlib.AlgebraicGeometry.Morphisms.Flat` and
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`).

Through these imports it also uses `GroupScheme` and the base-change functor
`GroupScheme.baseChange` from `Langlands.AbelianScheme.GroupScheme`. `GroupScheme S` is
`Grp (Over S)`, and the underlying morphism of `(GroupScheme.baseChange f).obj H` is
`pullback.snd H.X.hom f`.

It states Conrad's Corollary 3.1.8 (SGA 3, X, 4.9): if an fppf affine group scheme with
connected fibres has a torus fibre at a point `s`, then it is a torus over some open
neighbourhood of `s`.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with the instances `Flat G.X.hom`,
  `LocallyOfFinitePresentation G.X.hom` and `IsAffineHom G.X.hom`. This is Conrad's
  fppf `S`-affine group scheme `G → S`; see the derivation below;
- a proof that for every `s : S` the underlying topological space of the scheme
  `(RelativeIdentityComponent.residueFiber G s).X.left` is connected (`ConnectedSpace`).
  This scheme is the pullback of `G.X.hom` along the canonical morphism
  `S.fromSpecResidueField s : Spec κ(s) ⟶ S`, that is, Conrad's fibre `G_s` over the
  residue field `k(s)`. This is Conrad's hypothesis "with connected fibers";
- a point `s : S` and a proof of `IsTorus (RelativeIdentityComponent.residueFiber G s)`.
  For a group scheme `T` over `Spec k` with `k` a field, `IsTorus T` says that there is a
  field extension `K` of `k` such that the base change of `T` to `Spec K` is a split
  torus, that is, isomorphic as a group scheme over `Spec K` to `splitTorus (Spec K) I`
  for some finite type `I` (`IsSplitTorus`).

## Conclusion

There is an open subset `U : S.Opens` with `s ∈ U` such that
`RelativeTorus.IsTorus ((GroupScheme.baseChange U.ι).obj G)`. Here `U.ι` is the open
immersion of `U` into `S`, so `(GroupScheme.baseChange U.ι).obj G` is Conrad's `G_U`.
`RelativeTorus.IsTorus H`, for a group scheme `H` over a scheme `X`, says that there is
a jointly surjective étale cover of `X`, indexed in universe `u`, on each member of which
the base change of `H` is a split torus (`IsSplitTorus`); the rank may vary between
members.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Corollary 3.1.8, p.84: "Let G → S be an fppf S-affine group scheme with connected
  fibers, and assume that G_s is a torus for some s ∈ S. Then G_U is a torus for some
  open neighborhood U of s in S. This result is [SGA3, X, 4.9]."
- The proof, p.85, first treats smooth `G`: since being a torus is étale-local on the
  base, Proposition 3.1.6 gives, on an étale neighbourhood of `(S, s)`, a subgroup `H` of
  multiplicative type with `H_s = G_s`; a further étale neighbourhood makes `H` split,
  `H` is a torus because `H_s` is, and the fibral isomorphism criterion (Lemma B.3.1)
  shows `H = G`. It then reduces the fppf case to the smooth case by showing that `G` is
  smooth over an open neighbourhood of `s`.

## Derivation from the source

- **fppf.** Conrad's "fppf" means faithfully flat and locally of finite presentation.
  The proposition assumes `Flat` and `LocallyOfFinitePresentation`. Surjectivity is
  automatic for a group scheme, since the identity section is a section of `G → S`, so
  no surjectivity hypothesis is included. "`S`-affine" is `IsAffineHom G.X.hom`.
- **Connected fibres.** Conrad's fibres `G_s` are taken over the residue fields `k(s)`,
  and connectedness of a scheme is connectedness of its underlying topological space.
  The proposition uses the residue-field fibres of
  [`RelativeIdentityComponent`](../RelativeIdentityComponent.md).
- **Torus over a field.** Over a field, a torus is a group scheme that becomes
  isomorphic to a power of `𝔾_m` over some field extension. This is the field predicate
  `IsTorus` of [`Torus.Lattice`](Lattice.md) (Milne, *Algebraic Groups*, 12.14).
- **Torus over `U`.** Conrad's tori over a general base are groups that are, locally for
  the fpqc topology, isomorphic to powers of `𝔾_m`; for tori this is equivalent to being
  split étale-locally (SGA 3, X, 4.5). The proposition uses the étale form
  `RelativeTorus.IsTorus`. Its splitting covers are étale covers of `U`, not of `S`, and
  the rank may vary between their members. The equivalence with the fpqc form is not
  stated here.
- **Open neighbourhood.** Conrad's `U` is a Zariski open neighbourhood of `s`, encoded as
  `U : S.Opens` with `s ∈ U`, and `G_U` is the base change along `U.ι`.

## Scope

All objects are in universe `u`. The proposition does not state:

- the smooth case of the proof, the reduction from fppf to smooth, or the smoothness of
  `G` over a neighbourhood of `s`;
- the étale-locality of the torus property, or the equivalence of the étale and fpqc
  forms of the relative torus predicate;
- the fibral isomorphism criterion (Lemma B.3.1).

## Relation to the Library

- `RelativeSplitTorusLiftingStatement` in
  [`Torus.RelativeLiftingStatement`](RelativeLiftingStatement.md) is a split-torus
  specialization, with a pointed refinement, of Conrad's Proposition 3.1.6, which is the
  main input of the smooth case of the proof.

This module proves none of these relations.
