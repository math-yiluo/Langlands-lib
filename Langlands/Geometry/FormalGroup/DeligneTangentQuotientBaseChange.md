# Actual tangent Pi quotient and residue-fibre comparisons

This module compares the actual total tangent quotient and its residue fibre
for the existing preliminary Deligne datum and its constructed scheme pullback.
It supplies the target comparison needed for condition (b) in Drinfeld,
*Coverings of p-adic Symmetric Regions* (1976), §2 A, printed p.110
(PDF p.4, opening paragraph). That condition maps the total integral quotient
`eta_s / Pi eta_s` to `(T_s / Pi T_s) ⊗ κ(s)`. This module concerns the latter
object. The source file is registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA-256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

The provenance is derived. The implementation combines the published natural
comparison of ordinary module pullback stalks with actual scalar-extension
functors, their preservation of cokernels, and the scheme morphism's residue
square. These are comparisons of objects already defined in
`DeligneAdmissibility` and `DelignePreDatumBaseChange`; no representing object,
universal object, or separately supplied comparison is assumed.

## Scalar extension and a range quotient

For any commutative rings `R R' : Type u`, ring homomorphism `ρ : R →+* R'`,
and morphism `p : M ⟶ N` in `ModuleCat.{u} R`,
`extendScalarsRangeQuotientIso ρ p` identifies scalar extension of
`N / range(p)` with the quotient of the extended `N` by the range of the
extended `p`. No flatness assumption is needed: this is right exactness.

The isomorphism first identifies the range quotient with the categorical
cokernel, applies preservation of cokernels by scalar extension, and identifies
the resulting cokernel with its actual range quotient.
`extendScalarsRangeQuotientIso_mkQ` proves that the extended quotient projection
followed by this isomorphism is the actual quotient projection for the extended
morphism. The proof uses the defining projection squares for the three factors.

## Actual tangent stalks and quotients

Fix a positive integer `d`, a commutative coefficient ring `O : Type u`, an
element `π : O`, an `O`-algebra field `F : Type u`, schemes `S S' : Scheme.{u}`,
a coefficient map `φ : O →+* Γ(S, ⊤)`, a preliminary datum
`D : SheafPreDatum d π F φ`, and a morphism `f : S' ⟶ S`. No nilpotence,
admissibility, flatness of `f`, or quasi-coherence assumption is added here.
The structural and lattice hypotheses belonging to the supplied preliminary
datum remain in force.

For `x : S'`, `tangentStalkPullbackIso` specializes the existing natural
`StalkPullback.pullbackStalkIso` to the actual total tangent module sheaf. It is
an isomorphism from the actual tangent stalk of `D.pullback f` at `x` to the
extension of the original tangent stalk at `f x` along `(f.stalkMap x).hom`.
The module stalk is the actual additive stalk with its canonical local-ring
action, as in `DeligneAdmissibility`.

`tangentStalkPullbackIso_pi` is the naturality square for the actual tangent
Pi morphism. `tangentStalkPullbackIso_range` uses that square and surjectivity of
the stalk isomorphism to identify its transported Pi range with the range of
the extended Pi morphism. Thus `tangentPiQuotientPullbackIso` identifies the
actual quotient `T'_x / Pi T'_x` with extension of `T_(f x) / Pi T_(f x)` along
the actual local-ring map. It first uses the induced quotient equivalence,
then the inverse scalar-extension range-quotient comparison.

`tangentPiQuotientPullbackIso_inv_mkQ` proves the corresponding projection
square for the inverse quotient comparison: extending the original quotient
projection and then applying the inverse comparison equals applying the
inverse stalk comparison and then the pulled quotient projection. The proof
uses the generic projection square and the defining action of the induced
quotient equivalence on representatives.

## Actual residue fibres

`tangentPiQuotientFibrePullbackIso` is an isomorphism over the residue field
`κ(x)` from the actual `tangentPiQuotientFibre` of `D.pullback f` at `x` to
extension of the actual original `tangentPiQuotientFibre` at `f x` along
`(f.residueFieldMap x).hom`.

The four factors are: extend the actual tangent quotient comparison along
`S'.residue x`; replace the two successive local-ring and residue extensions
by extension along their composite; use the equality of ring maps supplied
by `Scheme.residue_residueFieldMap f x`; and decompose the other composite as
original residue extension followed by residue-field extension. In particular,
the original and pulled quotient fibres are the existing objects, rather than
new fibre presentations taken as input.

This unit does not prove compatibility of the comparison with the actual map
`u`, nor preservation of condition (b)'s injectivity. Full admissibility,
the moduli functor, projective-linear actions and representability also remain
separate obligations.
