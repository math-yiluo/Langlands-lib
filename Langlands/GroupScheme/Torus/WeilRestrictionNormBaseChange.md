# Arbitrary base change of the finite-free norm and its norm-one kernel

For commutative rings `A`, `A'` and a commutative `A`-algebra `B` that is finite
free as an `A`-module, this module constructs the actual group-scheme
isomorphism

\[
 (\operatorname{Res}_{B/A}\mathbf G_m)^{N=1}\times_{\operatorname{Spec}A}
 \operatorname{Spec}A'
 \;\simeq\;
 (\operatorname{Res}_{(A'\otimes_A B)/A'}\mathbf G_m)^{N=1}.
\]

Here the norm-one group is the published actual scheme-theoretic kernel
`WeilGm.normOne`, and `N` is the published determinant norm. The comparison is
an isomorphism in `Grp (Over (Spec A'))`. The module also proves the norm square,
the inclusion square and the formula for this particular isomorphism on every
test scheme.

## Hypotheses and provenance

The scheme constructions assume `[Module.Finite A B] [Module.Free A B]` and an
arbitrary ring homomorphism `f : A ⟶ A'` in `CommRingCat`. The `A`-algebra
structure of `A'` is induced by `f.hom.toAlgebra`. The algebra-structure version
instead takes `[Algebra A A']` and uses `baseMap A A'`.
All rings and the test schemes use the displayed universe `u`. There are no
field, separability, reducedness, injectivity or flatness assumptions on the
base map. No nontriviality or positive-rank assumption is added.

This is an internal derived construction. It uses the published objects and
formulas in [TensorNorm](../../Algebra/TensorNorm.md),
[WeilRestrictionNorm](WeilRestrictionNorm.md),
[WeilRestrictionBaseChange](WeilRestrictionBaseChange.md) and
[WeilRestrictionNormOne](WeilRestrictionNormOne.md), together with
[Split](Split.md)'s natural-point-model construction of actual group-scheme
isomorphisms. The algebraic proof uses Mathlib's
`Algebra.TensorProduct.cancelBaseChange` and
`Algebra.norm_eq_of_algEquiv`. No new external-source assertion or unproved
structural result is assumed. The results concern compatibility of the existing
norm and kernel constructions; they do not assert rational descent or
anisotropy.

## Algebraic comparison

For commutative-ring algebras and a scalar tower `A → A' → R`, the published
`baseChangeTensorEquiv A A' B R` is the ring equivalence

\[
 e_R:B\otimes_A R\simeq(A'\otimes_A B)\otimes_{A'}R,
 \qquad b\otimes r\longmapsto(1\otimes b)\otimes r.
\]

`tensorNorm_baseChange` proves

\[
 \operatorname{tensorNorm}_{A',A'\otimes_A B,R}(e_R(x))
 =\operatorname{tensorNorm}_{A,B,R}(x).
\]

The proof unfolds the two tensor norms and cancels the two opposite tensor
swaps. What remains is invariance of `Algebra.norm R` under the `R`-algebra
equivalence `(cancelBaseChange A A' R R B).symm`. This algebraic identity uses
only the displayed algebra structures and scalar tower, without finiteness or
freeness; here `Algebra.norm` has its Mathlib definition. The scheme part applies
it in the finite-free situation, where this is the determinant norm of a finite
free algebra.

`tensorNormUnits_baseChange` proves the corresponding equality on units by
`Units.ext`. `normOneTensorEquiv` restricts the unit equivalence induced by `e_R`
to the kernels of the two unit norms. Its inverse restricts the inverse unit
equivalence; the norm equality proves both membership conditions.
`normOneTensorEquiv_val` identifies its underlying unit as `Units.map e_R`.

## Actual norm square

Write `b = baseMap A A'`, `E = algebraBaseChangeIso A A' B`, and
`g = Gm.baseChangeIso b`. Then `norm_baseChange` is the equality of actual group
homomorphisms

\[
 \operatorname{baseChange}(b)(N_{B/A})\,;\,g
 = E\,;\,N_{(A'\otimes_A B)/A'}.
\]

Its proof uses `hom_ext_points` on every `T : Over (Spec A')`, followed by the
injectivity of the multiplicative-group point equivalence. The published
pullback, norm and Weil-restriction point formulas reduce the square to
`tensorNormUnits_baseChange` for `R = restrictedSections A A' T`.
`norm_baseChange_specMap` exposes the same square directly for every ring map
`f`, with `E = baseChangeIso f B` and `b = Spec.map f`.

## Norm-one isomorphism and its all-test formula

`baseNormOnePointsEquiv` composes the pullback point equivalence,
`normOnePointsEquiv` on the restricted test over `A`, and `normOneTensorEquiv`.
Thus its target is the kernel of the tensor unit norm for
`(A' ⊗[A] B)/A'` over the global sections of `T`.
`baseNormOnePointsEquiv_val` identifies its underlying unit with
`basePointsEquiv` of the image under the actual base-changed inclusion.
Consequently `baseNormOnePointsEquiv_naturality` follows from naturality of that
Weil-unit model, after taking subtype values.

`normOneAlgebraBaseChangeIso` applies `isoOfPointModels` to this natural model
and the existing `normOnePointsEquiv A' (A' ⊗[A] B)`. The theorem
`normOneAlgebraBaseChangeIso_hom_points` gives the resulting formula: for any
`T : Over (Spec A')` and any point `x` of the base-changed actual kernel,

\[
 \mathrm{normOnePointsEquiv}_{A',A'\otimes_A B,T}(x;E_1)
 =\mathrm{normOneTensorEquiv}_{A,A',B,R}
   \bigl(\mathrm{normOnePointsEquiv}_{A,B,T|_A}
       (\mathrm{baseChangePointsEquiv}(x))\bigr).
\]

Here `R = restrictedSections A A' T`, `T|_A` means composition with the base
map, and `E₁` is the hom of `normOneAlgebraBaseChangeIso`. In particular the
underlying tensor unit is sent by `Units.map e_R`.
The quantifier includes nonaffine and nonreduced test schemes and all morphisms
between them.

`normOneAlgebraBaseChangeIso_hom_ι` proves, as an equality of actual
morphisms,

\[
 E_1\,;\,\iota_{A',A'\otimes_A B}
 =\operatorname{baseChange}(b)(\iota_{A,B})\,;\,E.
\]

The proof again uses all-test point extensionality: the isomorphism's point
formula, the two inclusion formulas and the existing Weil base-change formula
have the same underlying tensor unit.

Finally `normOneBaseChangeIso f B` and the theorems
`normOneBaseChangeIso_hom_points` and `normOneBaseChangeIso_hom_ι` provide the
isomorphism, all-test formula and inclusion square along `Spec.map f` for an
arbitrary ring homomorphism, using exactly its induced algebra structure.
