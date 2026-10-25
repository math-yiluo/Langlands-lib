# Sheafified tensor presentations of ideal-adic coefficient systems

## Scope and provenance

Let `C : Type uC` have hom universe `vC`, let `J` be a Grothendieck topology
on `C`, and let `R : Type u` be a commutative ring with ideal `I`. Module
carriers have universe `u`. The reduction-system constructions assume
`HasSheafify J (ModuleCat R)`. Changing to coefficients in `R/I` additionally
uses sheafification for modules over that ring.

This is an internal categorical construction from
`Langlands.Coefficients.AdicSystem.tensorReduction`, `tensorPowerIso`,
`tensorPowersIso` and the existing sheaf reduction construction in
`Langlands/Sheaf/AdicSystem.lean`. The module comparison is the natural
quotient-ring-linear isomorphism `(R/I) tensor_R M ≅ M/IM`. Here `IM` denotes
`I • ⊤` in the module. Mathlib's sheafification adjunction and
`sheafComposeNatIso` provide the sheafification comparisons. This file does
not claim to transcribe a separate result from Harris.

## Quotient coefficients and tensor systems

Write `a_R` for sheafification of `R`-module presheaves and `i_R` for the
inclusion of sheaves into presheaves. If `T` is a module endofunctor, the
existing `sheafifyEndofunctor J` sends it to

`F ↦ a_R(i_R(F) ⋙ T)`.

It also maps every natural transformation by applying it sectionwise and
sheafifying. `tensorReduction` applies this construction, with target
coefficients `R/I`, to the module comparison. It is a natural isomorphism
from `Sheaf.composeAndSheafify J (ModuleCat.extendScalars (Ideal.Quotient.mk I))`
to the existing `quotientCoefficients J I`. Thus tensoring the section
modules and sheafifying agrees with quotienting those modules and
sheafifying. It does not assert that the quotient presheaf is already a sheaf.

For each natural number `n`, let `T_n` be extension to `R/I^n` followed by
restriction to `R`. The declarations are:

- `tensorPower J I n`: apply `sheafifyEndofunctor J` to `T_n`.
- `tensorPowerIso J I n`: its natural isomorphism to the existing reduction
  endofunctor `(powers J I).obj (op n)`.
- `tensorPowers J I`: the `ℕᵒᵖ` diagram obtained by applying
  `sheafifyEndofunctor J` to the module-level tensor diagram, including its
  canonical higher-power-to-lower-power transitions.
- `tensorPowersIso J I`: a natural isomorphism of that diagram to `powers J I`.
- `tensorFunctor J I` and `tensorFunctorIso J I`: the flipped diagram,
  functorial in the original sheaf, and its natural isomorphism to the
  existing `functor J I`.

The level comparisons are mapped module comparisons. The diagram
comparison is obtained by whiskering the module diagram comparison. In the
flipped comparison, naturality in the index is the component of that diagram
identity, and naturality in the sheaf is the level comparison's naturality.
All powers, including zero, are included.

## Units and scalar extension

Let `η_n : Id → T_n` be the module extension/restriction adjunction unit,
which sends `m` to `1 tensor m`. `tensorUnit J I n` is the composite of the
inverse sheafification counit with the image of `η_n` under
`sheafifyEndofunctor J`.

`tensorPowerIso_unit` proves that this unit followed by `tensorPowerIso.hom`
is the existing `quotientMap J I n`. The proof maps the module-level unit
identity through the functor. `tensorUnit_transition` similarly maps the
module-level compatibility equation and proves compatibility with every
transition `n → m` for `m ≤ n`.

`tensorUnit_hom` identifies the underlying presheaf morphism as

`whiskerLeft F.obj η_n ≫ toSheafify J (F.obj ⋙ T_n)`.

The proof uses the fact that the inclusion maps the inverse sheafification
counit to `toSheafify`, then uses naturality of `toSheafify`.

For `extensionPowerIso` and `extensionPowerIso_unit`, also assume
sheafification for `R/I^n`-module presheaves and
`J.HasSheafCompose (ModuleCat.restrictScalars (Ideal.Quotient.mk (I^n)))`.
The latter explicitly says that scalar restriction takes sheaves to sheaves
on this arbitrary site. Preservation of sheafification is supplied by
Mathlib: scalar restriction is left adjoint to coextension of scalars, and
`Sheaf.preservesSheafification_of_adjunction` applies.

`extensionPowerIso` is a natural isomorphism

`Sheaf.composeAndSheafify J (extendScalars q_n) ⋙ sheafCompose J (restrictScalars q_n)`

`≅ tensorPower J I n`,

where `q_n : R → R/I^n` is the quotient map. Its forward component is the
inverse of the canonical comparison between sheafifying after scalar
restriction and restricting an already sheafified presheaf, applied to the
tensor presheaf. This is constructed from `sheafComposeNatIso` and does not
assume the desired tensor/quotient comparison.

`extensionPowerIso_unit` proves that the sheaf extension/restriction
adjunction unit followed by this comparison is `tensorUnit`. After forgetting
to presheaves, the proof uses Mathlib's formula for the induced adjunction
unit and `sheafComposeIso_inv_fac`, then the formula for `tensorUnit_hom`.

## Boundaries

No flatness, exactness, topological completeness, derived inverse limit,
cohomological coefficient-change comparison, or geometric equivariance is
asserted. These are actual ordinary module sheaves and ordinary inverse
systems. The small-etale specialization is supplied by
`Langlands/Geometry/EtaleAdicTensorComparison.lean`; identification with the
specific Harris coefficient sheaves remains a separate obligation.
