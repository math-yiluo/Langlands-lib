# Exact integral transporters and their generic conjugacy equation

This internal construction connects the published exact Henselian transporter
lifting theorem to the actual integral-point map of a supplied integral model.
All rings, fields and schemes lie in an arbitrary common universe `u`.
Let `R` be a commutative domain, let `K` be its fraction field, and let
`M : IntegralModel R K G`. The model includes an affine, flat, finite-type
group scheme over `Spec R` and a specified identification of its generic fibre
with `G`. Let `H` be any group scheme over `Spec R`.

For a field `k` with an `R`-algebra structure, two homomorphisms
`j₁ j₂ : H ⟶ M.group`, and a specified point
`g₀ : Spec k → M.group` over `Spec R`, `M.TransporterData j₁ j₂ g₀`
consists of:

- An actual section `section_ : M.integralSections`.
- The all-test equation `PointwiseSchemeAction.IsTransporter j₁ j₂ section_`.
- The equality saying that restriction of this same section along `Spec k →
  Spec R` is exactly `g₀`.

Here the transporter equation tests every scheme refinement and every source
point. In point notation it says `j₁(x) * g = g * j₂(x)`. It is stronger than
an assertion solely about rational points over one field.

`TransporterData.genericPoint` applies the model's actual
`integralPointMap` to the recorded section. Thus it uses both base change of
the section and `M.genericIso`. The theorem
`TransporterData.genericPoint_mem_integralPoints` proves membership in the
model's integral-point subgroup by the section itself.

For any integral section `g` satisfying the transporter equation,
`genericHom_comp_innerIso_of_isTransporter` proves the equality of actual
generic group-scheme homomorphisms

```text
M.genericHom j₂ ≫ (G.innerIso (M.integralPointMap g)).hom =
  M.genericHom j₁.
```

`TransporterData.generic_comm` specializes this equality to the recorded data.
No Henselian, smoothness, splitting, or residue-surjectivity assumption is
needed for these constructions and equations.

The proof first applies `IsTransporter.baseChange` along `R → K`.
`baseChangePointsEquiv_baseChangeSectionHom` identifies the transported
section with the actual base-changed integral section. The proof then applies
`IsTransporter.map` along `M.genericIso.hom`. Testing the resulting equation
on every scheme and point, multiplying by the inverse of the constant
generic point, and applying `hom_ext_points` gives the displayed equality.
This retains the specified generic-fibre identification.

For `henselianTransporter`, additionally assume that `R` is Henselian local,
`H` is a split torus, `M.IsSmooth`, and `R → k` is surjective. A prescribed
`g₀` satisfying `IsTransporter j₁ j₂ g₀` then produces actual
`TransporterData` by classical choice from the published
`PointwiseSchemeAction.exists_henselian_transporter_of_split`. Affineness of
the model's total scheme follows from its affine structural morphism and
affineness of `Spec R`, via `isAffine_of_isAffineHom`. The chosen section
recovers the prescribed residue point exactly; uniqueness is not asserted.

The provenance is internal. The inputs are the published integral-model,
transporter-functoriality, exact Henselian lifting, base-change point, and
inner-automorphism interfaces described above. This module does not construct
the residue transporter, a common residue torus, a smooth integral model,
or a special apartment. No characteristic restriction is imposed.
