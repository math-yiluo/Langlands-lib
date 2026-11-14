# Actual residue-fibre compatibility and condition (b) under base change

This module proves compatibility of the actual Deligne residue-fibre map with
the constructed scheme pullback, and preservation of condition (b) under an
arbitrary scheme morphism.

## Source and scope

The source condition is V. G. Drinfeld, *Coverings of p-adic Symmetric Regions*
(1976), Section 2 A, printed p.110 (PDF p.4, opening paragraph). It requires
injectivity of the actual map from the total integral stalk quotient
`eta_s / Pi eta_s` into the residue fibre of the total tangent quotient
`T_s / Pi T_s`. The preliminary sheaf data are at the end of printed p.109
(PDF p.3). Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
No source-specific errata file was present in the pinned Library at preparation.

The provenance is derived: these compatibility formulas and the preservation
result follow from the existing actual stalk, quotient and residue-fibre
constructions and their canonical comparisons. They are implementation lemmas
for condition (b). The module does not assert Proposition 2.4, whose inputs
arise from a special formal module, or Drinfeld's representability theorem.
Preservation of the determinant condition, full admissibility, a moduli functor
and representability remain separate obligations.

## Parameters and actual objects

Let `O : Type u` be a commutative ring, `d` a nonzero natural number,
`π : O`, and `F : Type u` a field with an `O`-algebra structure. Let
`S S' : Scheme.{u}`, `φ : O →+* Γ(S, ⊤)`,
`D : SheafPreDatum d π F φ`, and `f : S' ⟶ S`. All hypotheses belonging to
the existing preliminary datum remain in force. No nilpotence, flatness of `f`,
or admissibility of `D` is added to the comparison results. The final transport
theorem assumes precisely `D.ResidueFibreInjective`.

For `x : S'`, put `y = f x`. The existing eta quotient equivalence has direction
`eta_y/Pi ≃ₗ[O] eta'_x/Pi`, and the existing tangent quotient fibre comparison
has direction

```
(T'_x/Pi) ⊗ κ(x) ≅ Eβ ((T_y/Pi) ⊗ κ(y)),
```

where `β : κ(y) → κ(x)` is the actual `f.residueFieldMap x`, and `Eβ` is
`ModuleCat.extendScalars β`. The fibres and all maps are the actual objects
defined in `DeligneAdmissibility` and the preceding base-change modules.
No comparison isomorphism, representing object or universal object is an
additional input. Quotients are by the actual linear ranges of the Pi operators.

## The field-extension unit

`fieldExtension_unit_injective` applies to any field homomorphism
`β : K →+* K'` and any `M : ModuleCat.{u} K`, with both fields in the same
displayed universe. It proves injectivity of the actual extension/restriction
adjunction unit `M → Restrictβ(Eβ(M))`.

The proof installs the algebra structure induced by `β`. The coefficient map
`K → K'` is injective, and tensoring it with the vector space `M` preserves
injectivity because `M` is flat. Composing with the inverse tensor left-unitor
gives the map `m ↦ 1 ⊗ m`, which is the actual adjunction unit. No finite
dimension, separability or algebraicity is required.

## Compatibility of the actual maps

`uResidueFibrePullback_square` proves, on the original total eta stalk,

```
fibreIso.hom (uResidue'_x (etaIso.hom e)) = unitβ (uResidue_y e).
```

The proof follows the four factors defining the existing
`tangentPiQuotientFibrePullbackIso`. Write `ρ` for the actual local-ring map,
`σ` for the pulled residue map, and `α` for the original residue map.
Naturality of the extension unit handles extension of the actual tangent
quotient comparison along `σ`. The previously proved
`uPiQuotientPullback_square` identifies its inner value with `unitρ` applied
to the original quotient of `u`. The inverse composition comparison combines
`unitσ` and `unitρ`. Transport along the actual residue square
`σ.comp ρ = β.comp α` changes this unit to the other composite unit.
The forward composition comparison decomposes it as `unitβ` after `unitα`.
These are formulas for the previously constructed comparison itself.

`piQuotientResiduePullbackMap` packages the additive composite from the original
eta/Pi quotient through the actual eta quotient equivalence, the pulled
`piQuotientResidueMap`, and the actual fibre comparison. Its target is `Eβ`
of the original tangent quotient fibre.

`piQuotientResiduePullback_square` states the corresponding equality explicitly
for every original quotient element `q`:

```
fibreIso.hom (piQuotientResidue'_x (etaQuotientEquiv q)) =
  unitβ (piQuotientResidue_y q).
```

The proof chooses a representative using surjectivity of the actual quotient
projection. The eta quotient comparison and both descended maps have their
existing representative formulas; these reduce the result to the preceding
unquotiented residue-fibre square.

## Preservation of condition (b)

`residueFibreInjective_pullback` proves
`D.ResidueFibreInjective → (D.pullback f).ResidueFibreInjective`.
For two pulled eta quotient elements with equal images, surjectivity of the
actual eta quotient equivalence supplies original quotient elements. Applying
the actual fibre comparison and its square gives equality of the extension
units of their original residue-fibre images. The field-extension unit is
injective, and condition (b) for `D` makes the original quotient elements
equal. Applying the eta quotient equivalence yields the desired equality.
