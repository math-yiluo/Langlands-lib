# Reduced translation spaces in a central-isogeny square

Author: Worker 1631.

This is a derived comparison for supplied actual group schemes over an arbitrary
field `k`, in arbitrary universe `u`. Let `q : C → G` be a central isogeny,
and let `i : S.toGrp → C` and `j : T.toGrp → G` be maps from split tori.
Both ambient group schemes are affine and locally of finite type. Supply an
actual torus map `t : S → T` which is an isogeny and a commuting square
`i ≫ q = groupHom t ≫ j`. These data are hypotheses throughout the comparison;
neither inclusion is required to be maximal or a monomorphism.

`centralIsogenyRootPullbackEquiv` is a bijection from the actual relative
roots for `j` to those for `i`. Its value on a root `a` is precisely `t ≫ a`.
It packages the existing
`IsCentralIsogeny.roots_bijOn_of_torusRestriction`, rather than reproving
the root-support comparison.

`eval_cocharacterMapReal` is the pairing identity
`eval T a (cocharacterMapReal t v) = eval S (t ≫ a) v`.
It follows from the existing real pairing naturality theorem.
Every source root is the pullback of a target root, and every target root
pulls back to a source root. Consequently the actual cocharacter map preserves
and reflects simultaneous annihilation by all the relative roots.
The proved real bijectivity of the cocharacter map of a split-torus isogeny
then identifies the image of the entire source root-annihilator submodule
with the target root-annihilator submodule.

`centralIsogenyTranslationEquiv` is the resulting linear equivalence of the
published reduced spaces `TranslationSpace i` and `TranslationSpace j`.
It is induced by the original actual map: on quotient representatives it sends
`[v]` to `[cocharacterMapReal t v]`, and on pure tensors that cocharacter map is
`r ⊗ ν ↦ r ⊗ (ν ≫ t)`. The root-form comparison is

```text
rootForm j a (centralIsogenyTranslationEquiv ... v)
  = rootForm i (centralIsogenyRootPullbackEquiv ... a) v.
```

Quotient induction reduces this identity to the evaluation identity.

The provenance is internal: the actual root-support bijection and the
split-torus isogeny theorem on real cocharacters are already proved Library
results. The new construction descends these maps through the published common
root kernels and proves the induced root-form identity. It supplies no cover
tori, map of normalizer points, valuations, apartment points or apartment axioms.
Those remain necessary for the simply connected cover transfer and the final
normalizer-image theorem.
