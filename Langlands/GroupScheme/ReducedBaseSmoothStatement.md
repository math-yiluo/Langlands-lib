# Group schemes with smooth connected fibres over a reduced base are smooth

Author: Worker 4246.

`Langlands.GroupScheme.ReducedBaseConnectedFibreSmoothStatement.{u}` is a proposition
definition; this module supplies no proof. It records the reduced-base clause of SGA 3,
Exposé VI_B, Corollaire 4.4, in the case of a locally Noetherian base and connected
fibres.

## The statement

For every scheme `S : Scheme.{u}` and every group scheme `H : GroupScheme S` (a group object
in schemes over `S`, `Langlands/AbelianScheme/GroupScheme.lean`), assume:

- `IsReduced S`: the base is reduced;
- `IsLocallyNoetherian S`: the base is locally Noetherian;
- `LocallyOfFiniteType H.X.hom`: the structure morphism `H → S` is locally of finite type.
  Over a locally Noetherian base this is the same as local finite presentation;
- for every point `s` of `S`, `Smooth (H.X.hom.fiberToSpecResidueField s)`: the fibre
  `H_s = H ×_S Spec κ(s)` (Mathlib's `Scheme.Hom.fiber`, the pullback of `H → S` along
  `Spec κ(s) → S`) is smooth over the residue field `κ(s)`;
- for every point `s`, `ConnectedSpace (H.X.hom.fiber s)`: the fibre is connected (and
  nonempty);
- `IsLocallyConstant (fun s => topologicalKrullDim (H.X.hom.fiber s))`: the fibre dimension
  `s ↦ dim H_s`, the Krull dimension of the underlying space of the fibre, is locally constant
  on `S`.

The conclusion is `Smooth H.X.hom`: `H` is smooth over `S`.

## Source

J.-E. Bertin, SGA 3, Exposé VI_B, *Généralités sur les schémas en groupes*, recomposed
edition by P. Gille and P. Polo (13 October 2024), registered source
`sga3-expose-vib-gille-polo-2024`, SHA-256
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`, Corollaire 4.4,
printed p.354 (one-based PDF p.24):

> Soit G un S-groupe localement de présentation finie sur S aux points de la section unité.
> Considérons les conditions : (i) G est lisse sur S aux points de la section unité (cf. 3.10).
> (ii) Pour tout s ∈ S, G_s est lisse sur κ(s), et la fonction s ↦ dim G_s est localement
> constante sur S. […] Si on suppose de plus S réduit, alors les conditions (i) à (iv) sont
> équivalentes, et impliquent que G⁰ est lisse sur S.

Here `G⁰` is the relative identity component (Exposé VI_B, Définition 3.1): the union of the
identity components `G⁰_s` of the fibres. The proof printed after Note (32) on printed
pp.354–355 (PDF pp.24–25) reduces to `G = G⁰`, uses EGA IV₃ 15.6.7 to obtain flatness of
`G → S` when `S` is reduced, and concludes smoothness by Théorème 3.10.

## Relation to the source (provenance: derived special case)

The Lean proposition is the special case of the reduced-base clause in which

1. `S` is locally Noetherian and `H → S` is locally of finite type, so `H` is locally of
   finite presentation over `S` everywhere, in particular along the unit section;
2. every fibre `H_s` is connected. Then `H⁰_s = H_s` for every `s`, so the relative identity
   component `H⁰` is all of `H`, and the conclusion "`H⁰` est lisse sur `S`" reads
   "`H` is smooth over `S`".

Hypothesis (ii) of the corollary is the smoothness of the fibres together with the local
constancy of `s ↦ dim H_s`; the dimension is the Krull dimension of the fibre, which is
Mathlib's `topologicalKrullDim` of its underlying space. Connectedness of the fibres cannot be
dropped from the Lean statement: over `S = 𝔸¹_k`, the subgroup of the constant group
`(ℤ/2ℤ)_S` consisting of the unit section and the non-trivial point over the origin has
smooth zero-dimensional fibres but is not flat over `S`. Reducedness cannot be dropped either:
Note (31) on the same page gives the closed subgroup `Spec A[X]/(δX)` of `𝔾_{a,A}`, with
`A = k[δ]/(δ²)`, which satisfies (ii) with connected fibres but is not flat.

The declaration name is derived here. All schemes lie in an arbitrary universe `u`.
