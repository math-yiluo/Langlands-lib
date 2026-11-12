# Norm characters on the actual affine Weil restriction

For a finite free commutative ring extension `S/R` in an arbitrary common
universe, `Langlands.GroupScheme.AffineWeil.multiplicativeNorm` constructs
the determinant norm morphism

`AffineWeil.groupScheme R S (Gm (Spec S)).toGrp → (Gm (Spec R)).toGrp`.

This uses the exact affine restriction carrier used by the canonical
adelic Weil comparison. On every actual relative test scheme `T`, its unit
formula is the determinant norm from
`(S ⊗[R] Γ_R(T))ˣ` to `Γ_R(T)ˣ`, with the tensor factors swapped to regard
the algebra as finite free over the coefficient ring. No field,
separability, reducedness or nonzero-ring assumption is needed.

Restricting any character of an upper-base affine finite-type group and
composing with this norm gives `AffineWeil.normCharacter`. Its exact
affine-test formula evaluates the original character after the existing
Weil point comparison, then applies the determinant tensor norm.
The original group is arbitrary affine and locally of finite type over
`Spec S`; it need not be commutative or reductive.

The provenance is internal, using the actual group-point representations,
the published determinant tensor norm and its naturality, and relative
global-section normalization. The existing `WeilGm.norm` is a related
determinant-norm construction on the separately presented
`WeilGm.groupScheme`. This module constructs the map directly on
`AffineWeil.groupScheme`, retaining that fixed carrier and its exact
`pointsEquiv`; it does not supply or assume an identification of the two
presentations.

`multiplicativeUnitsEquiv` composes the affine restriction's all-test
corepresented point equivalence with the original multiplicative group's
affine unit equivalence. Both equivalences are natural, so their composite
is natural in all test schemes. Composing with the determinant tensor norm
and the inverse original `Gm.pointsEquiv` gives a natural homomorphism of
point groups. The published group-valued Yoneda construction produces
`multiplicativeNorm`, and `multiplicativeNorm_units` proves its exact
all-test formula.

On an affine test algebra `A`, relative global sections are normalized by
`Corepresented.affineSectionsIso A`. Its published compatibility with
`Corepresented.affinePointsEquiv` proves
`multiplicativeUnitsEquiv_affine_normalized`. The determinant norm commutes
with this normalization, by `tensorNormUnits_naturality`; the forward
section isomorphism has exactly the original `Scheme.ΓSpecIso` ring map.
This gives `multiplicativeNorm_affineUnits`, expressed on the original
algebra `A`. Finally, `normCharacter` is `AffineWeil.map` of the original
character followed by `multiplicativeNorm`. Functoriality of the fixed
Weil point comparison proves `normCharacter_affineUnits`.

The determinant norm's compatibility with the actual adelic norm and its
normalized absolute value remains separate, as does a classification of
all characters of the affine restriction. This module does not prove a
norm-one subgroup comparison or rational quotient compactness.
