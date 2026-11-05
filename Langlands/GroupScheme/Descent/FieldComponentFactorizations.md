# Compatibility of cover factorizations on field components

Authors: Workers 1347, 416 and 1366. Worker 1347 supplied the proof
prototype; Worker 416 supplied the component restriction and base-isomorphism
interfaces used in its design. Worker 1366 prepared this pair for review.

`Langlands.GroupScheme.Descent.Compatible.of_factorization_onFieldComponents`
proves compatibility of an actual factorization with supplied descent data.
The base is any scheme `B` in universe `u`, the covering scheme is `Spec K`
for a field `K : Type u`, and `p : Spec K → B` is arbitrary. The group
schemes `C`, `G` and `H` are over `Spec K`. The inputs are descent data
`D`, `E` and `F` on those objects, actual homomorphisms `π : C → G`,
`q : H → G` and `a : C → H`, compatibility of `π` and `q` with the
respective data, the explicit central-cover universal property of `π`,
semisimplicity of `H`, centrality and the isogeny properties of `q`, and
`a ≫ q = π`.

The additional geometric inputs are a finite type `I : Type`, fields
`L i : Type u`, and actual maps `r i : Spec (L i) → Overlap p`. The
coproduct map `Sigma.desc r` must be an isomorphism. Each composite with
`fst p` and with `snd p` must also be an isomorphism. The conclusion is
`Compatible D F a`. No flatness, surjectivity or effectivity assumption
on `p` is needed for this compatibility result.

## Implemented proof

Finite-component equality detection reduces the compatibility equation to
each `Spec (L i)`. Put `f = r i ≫ fst p`, `g = r i ≫ snd p`, and let
`e` be the restriction of the target datum's overlap isomorphism. Restricting
the given compatibility equations produces

```text
f*π ≫ e.hom = D_i.hom ≫ g*π,
f*q ≫ e.hom = F_i.hom ≫ g*q.
```

Actual pullback preserves the given factorization equation along both
`f` and `g`. Transport the universal property along the base isomorphism
`f` and then postcompose its target with `e`. The source of `g*q` is
semisimple by base-isomorphism transport along `g`, and `g*q` is a
central isogeny by actual base change. The transported property supplies
a unique homomorphism factoring `f*π ≫ e.hom` through `g*q`.

Both `(f*a) ≫ F_i.hom` and `D_i.hom ≫ (g*a)` have that factorization
equation, using the two restricted compatibility equations and the two
pullbacks of `a ≫ q = π`. Uniqueness identifies them. The theorem
`FiniteComponents.pullHom_ext` then gives compatibility on the full
double overlap.

## Provenance and scope

This is an internal deduction from the published actual pullback,
finite-component equality and base-isomorphism transport interfaces. The
proof imports `Descent.ComponentCoverLifts` and
`SimplyConnected.BaseIsoTransport` by Lean name. No external literature
assertion is used as an additional premise.

The universal property is applied only over a field component. Centres,
kernels and central isogenies retain their full scheme-theoretic meanings
on all test schemes, including nonreduced tests. The supplied data include
the universal property and factorization; this lemma constructs neither a
covering group nor a tensor decomposition nor a descended homomorphism.
