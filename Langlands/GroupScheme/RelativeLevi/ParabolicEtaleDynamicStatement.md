# Etale-local dynamic presentations of relative parabolic subgroups

Authors: Worker 243 and Worker 590. The proposition type is adopted from
Worker 590's shared draft for Task 6266. Worker 243 uses a distinct pointwise
declaration name and documents the source correspondence.

`Langlands.GroupScheme.RelativeParabolicPointwiseEtaleLocalDynamicStatement.{u} : Prop`
states a consequence of Brian Conrad, *Reductive group schemes* (2014),
Proposition 5.2.3, pp.152–153, together with the etale localization of a
maximal torus and its split pair described in that proof. This module defines
the proposition; its proof is a separate obligation. The `Pointwise` name
records the choice of an etale neighbourhood above each supplied base point.

## Statement and existing interfaces

For every universe `u`, the statement quantifies over an arbitrary scheme
`S : Scheme.{u}`, group schemes `G P : GroupScheme S`, a homomorphism
`i : P ⟶ G`, and a point `s : S`. Its hypotheses are:

- `IsReductive G`: `G` is smooth and affine over `S`, with connected
  reductive geometric fibres.
- `IsRelativeParabolicSubgroup i`: `P` is smooth and affine over `S`, `i`
  is a monomorphism of schemes over `S`, and its fibre over every residue
  field is parabolic. Reductivity of `G` is supplied by the preceding
  hypothesis.

The conclusion supplies a scheme `T : Scheme.{u}` and a morphism
`f : T ⟶ S`, with `Etale f` and a point `t : T` such that `f.base t = s`.
For `G_T = (GroupScheme.baseChange f).obj G`, it also supplies a
cocharacter

```lean
χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange f).obj G
```

such that

```lean
(Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange f).map i)
```

The map in this last expression is the actual base change of the supplied
`i`. By the existing definition of `SubgroupFunctor.IsRepresentedBy`, it
is a monomorphism and

```lean
SubgroupFunctor.range ((GroupScheme.baseChange f).map i) = Dynamic.parabolic χ
```

as subgroup functors of `G_T`. Thus, on every test scheme `V` over `T`,
a point `g ∈ G_T(V)` factors through `P_T` if and only if its conjugation
orbit `a ↦ χ(a) g χ(a)⁻¹` extends from `V ×_T Gm_T` to `V ×_T A¹_T`.
This includes nonreduced test schemes.

The imports are [`RelativeLevi.Basic`](Basic.md), for the relative
parabolic predicate and its reductive dependencies,
[`Dynamic.Basic`](../Dynamic/Basic.md), for the dynamic functor and its
representability interface, and Mathlib's etale-morphism module.

## Original source and correspondence

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes*
I, Panoramas et Synthèses 42–43, SMF, 2014. Registered source:
`conrad-2014-reductive-group-schemes`; retained file:
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`;
SHA-256:
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed and one-based PDF page numbers agree.

- Definition 5.2.1, p.151, supplies precisely the smooth, affine, monic
  and fibrewise-parabolic conditions used for `i`.
- Proposition 5.2.3, pp.152–153, gives a maximal torus contained in the
  supplied parabolic after etale localization. When the resulting pair
  is split, its final assertion gives a cocharacter of that torus
  Zariski-locally with dynamic parabolic equal to the supplied subgroup.
- The proof on p.152 explicitly passes to a further etale localization
  where that same pair is split. The splitting procedure is also
  described in the proof of Lemma 5.1.3, pp.136–137: split the torus
  etale-locally and then make the root spaces and lattice data constant
  by Zariski localization.
- The limit convention preceding Theorem 4.1.7, p.112, and its
  arbitrary-base extension after Example 4.1.9, p.114, agree with
  `Dynamic.parabolic`: the conjugation orbit extends to the affine
  line at zero. The source compares subgroup schemes, which yields
  equality of their functors on all test schemes.

To obtain the precise conclusion here, choose a point over `s` in the
first etale localization, a point above it in the further splitting
localization, and a Zariski neighbourhood on which Proposition 5.2.3
provides its cocharacter. Open immersions are etale, and composites of
etale morphisms are etale, so this neighbourhood gives `f : T ⟶ S`
with `s` in its image. Compose the torus cocharacter with the torus
inclusion into `G_T` to obtain the displayed ambient cocharacter `χ`.
The equality in Proposition 5.2.3 gives exactly the representability
assertion for the base change of `i`.

## Scope

No affineness, reducedness, noetherianity or connectedness of `S` is
assumed. The etale neighbourhood may extend the residue field at `s`;
the statement requires a point above `s`, without prescribing its
residue field. The cocharacter is chosen only on this neighbourhood.
Its target is `G_T`; the conclusion records neither a chosen torus nor
a lift through `P_T`.

This statement contains no assertion about relative unipotent radicals
or Levi subgroups. It provides the local presentation interface needed
for subsequent proof tasks.
