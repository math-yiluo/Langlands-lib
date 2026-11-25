# Coefficient pullback of arbitrary rational formal Hom sheaf sections

This is internal construction infrastructure. It extends the existing actual
coefficient and tensor Hom maps to the genuinely sheafified rational Hom.
No original-literature theorem is attributed to this module.

Let `O` be a commutative ring, let `R` and `S` be commutative `O`-algebras,
and let `F` be an `O`-algebra field. The rings `R`, `S` and `F` occupy the same
universe; `O` can occupy a different one. Let `φ : R →ₐ[O] S`. The formal
modules over `R` have finite, possibly different coordinate types.

`coefficientSpectrumMap φ` is the actual continuous map `Spec S → Spec R`.
`coefficientOpenMap φ` takes inverse images of opens. On each open `U`,
`coefficientSectionMap φ U` is the actual map from the structure sheaf of
`R` on `U` to the structure sheaf of `S` on the inverse image of `U`,
equipped with its compatible `O`-algebra structure. The structural and
restriction equalities follow from the actual structure-sheaf morphism.

`Hom.openBaseChange` applies `Hom.mapSquareLinear` to this commutative
coefficient square. Its coordinate series are exactly those of the input map
with coefficients mapped by `coefficientSectionMap φ U`. This formula proves
compatibility with restriction. Tensor extension gives
`RationalHom.openBaseChange`, whose restriction compatibility is proved by
tensor induction.

`rationalHomPresheafBaseChange` assembles these actual tensor maps into a
morphism of presheaves. Its target is the rational Hom presheaf for the
coefficient-extended formal modules, evaluated on inverse images of opens.
Compose with the actual target sheafification unit. The pushforward of the
target rational Hom sheaf is a genuine sheaf on `Spec R`, so the universal
property `sheafifyLift` extends this map uniquely from the source rational
Hom presheaf. This defines `rationalHomSheafBaseChange`.

`RationalSection.baseChange φ U` is the component of that sheaf morphism.
It is `F`-linear and is defined on every actual sheaf section, without an
assumption of a global tensor representative. Naturality proves compatibility
with open restriction. The sheafification unit identity gives the formula
on `ofRational`. The coefficient-square law on extended global tensors
then gives the formulas on `ofGlobalOn` and global integral `ofHom`.

No nilpotence, domain, fraction-field or isogeny hypothesis is required.
This module asserts no invertibility of the sheaf morphism, no comparison
isomorphism, and no preservation of the local scalar-isogeny condition.
