# Openness of the fibre-contraction locus

Authors: Worker 1028 and Worker 139. Worker 1028 supplied the statement draft;
Worker 139 checked the interfaces and source passage and prepared this pair.

`Langlands.AbelianScheme.FibreContractionOpenStatement.{u}` is a
`Prop`-valued definition. This module states the proposition and does not
prove it.

For arbitrary schemes `Y Z : Scheme.{u}`, an actual abelian scheme
`B : AbelianScheme Y`, a scheme morphism `Ψ : B.X.left ⟶ Z`, and a point
`z₀ : Z`, suppose
`∀ y : Y, Ψ (unitSection B y) = z₀`. The conclusion is that

```text
{y : Y | ∀ x : B.X.left, B.X.hom x = y → Ψ x = z₀}
```

is open in the underlying topological space of `Y`. The binders occur in
the order `Y Z B Ψ z₀`, followed by the unit-section hypothesis.

Here `B.X.left` is the total scheme and `B.X.hom` its structure morphism.
The imported `Langlands.AbelianScheme.unitSection B` is the actual unit
section; `unitSection_comp` identifies its composition with `B.X.hom`
with the identity of `Y`. All quantified points and displayed equalities
are in underlying topological spaces. Thus the fibre condition quantifies
over every point of the topological fibre, not just rational or closed
points. The hypothesis is pointwise on the unit section and does not
specify an equality of scheme morphisms.

The morphism `Ψ` need not be over `Y` or any other specified base and
need not preserve a group structure. The definition of `AbelianScheme`
already supplies smoothness, properness and geometrically connected
fibres of `B.X.hom`. There are no additional Noetherian, separatedness,
reducedness, finiteness, connectedness, flatness, field-base,
rational-point or affineness assumptions on `Y`, `Z` or `Ψ`. The
conclusion asserts no closedness of the displayed set, no factorization
of `Ψ` through `B.X.hom`, and no constancy of `Ψ` on fibres outside
that set.

## Derived provenance

The registered original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft), source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The relevant passage is (1.12), the Rigidity Lemma and its proof, printed
pp.12–13, PDF pp.16–17, in the retained file
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
No source-specific errata note was present in the checked workspace,
Library or project `notes/errata/` locations.

This proposition is derived from the openness step of that proof,
isolated in scheme-theoretic form. It is not a quotation of the source's
lemma, which concerns varieties over a field, a product with a complete
variety, and a stronger factorization conclusion.

The rationale for the derived form is as follows. Choose an affine open
neighbourhood `U` of `z₀` in `Z`. Properness of `B.X.hom` makes it a
closed map, so the complement of the image of `Ψ⁻¹(Z ∖ U)` is open
in `Y`. Over a point of this complement, the map from the residue-field
fibre takes values in `U`. That fibre is smooth, proper and
geometrically connected over the residue field, so its global functions
are the residue field. The Library theorem
`Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`
in `Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof`
expresses this by invertibility of the canonical map on global sections.
A map from the fibre to an affine scheme therefore factors through the
spectrum of its residue field and has a one-point topological image.
The unit-section hypothesis identifies that image with `z₀`.
Conversely, a fibre mapped entirely to `z₀` avoids `Z ∖ U`.
This identifies the displayed locus with the indicated open complement.
This paragraph explains the mathematical derivation; this module
contains no formal proof of it.

The module imports only the existing `RelativePicardZero` interface.
It assumes no Picard-zero openness or component-constancy statement.
