# Normalized root-function pullback through a central isogeny

Author: Worker 1631.

Let `k` be a field in arbitrary universe `u`. Supply affine, locally finite type
`k`-group schemes `C` and `G`, a central isogeny `q : C → G`, split commutative
tori `S` and `T`, maps `i : S → C`, `j : T → G`, and a torus isogeny `t : S → T`
with `i ≫ q = groupHom t ≫ j`. No maximality or monomorphism assumption is needed
for the family constructions. The valuation-normalization adapter alone uses
the target monomorphism required by the existing valuation predicate.

`centralIsogenyRootGroupPointsEquiv` packages the existing rational root-point
transport as a multiplicative equivalence between `U_{t*a}(k)` and `U_a(k)` for
each actual target relative root `a`. Its forward point is literally composition
with `q`. This wrapper needs only affine ambient groups, splitness of `S`, and
the supplied square and torus isogeny; target splitness and local finite type
are used by the subsequent actual root-support bijection.

`RootFunctionFamily.IsNormalized` packages the two existing normalization
conventions: values are infinity at nonroots and off the actual root subgroup.
The normalized pullback chooses the unique target root corresponding to a source
root using `centralIsogenyRootPullbackEquiv.symm`, uses the ambient point map on
that source root subgroup, and takes infinity elsewhere. This restriction matters
because central-kernel points need not belong to a root subgroup even when their
image is the identity. On corresponding actual root points, evaluation is
unchanged. Every pulled-back family is normalized. The published full valuation
predicate implies `IsNormalized` by its first two fields.

Naturality of evaluation and the actual root bijection show that pullback
intertwines the original real-cocharacter translations along `cocharacterMapReal t`.
Translations preserve normalization. Surjectivity of the root-point equivalences
then shows that normalized target families are determined by their pullbacks:
compare their values on roots and root points using these equivalences, and use
normalization on all other inputs. Together with real cocharacter surjectivity
of the torus isogeny, this proves preservation and reflection of equipollence
for normalized target families.

For each corresponding root and each real level, source filtration membership
is equivalent to membership in the actual source root group together with target
filtration membership of its image. The target filtration is exactly the image
of that source filtration. The proof uses only surjectivity on the corresponding
root subgroup, without asserting surjectivity on ambient or torus rational points.

All assertions here are internal consequences of the existing central-isogeny
root bijection, rational root-point equivalences, pairing naturality, and real
cocharacter bijectivity. No new assertion from external literature is introduced.
This unit constructs neither the supplied tori nor full valuation or apartment
data, and proves no apartment-axiom or affine Weyl image assertion.
