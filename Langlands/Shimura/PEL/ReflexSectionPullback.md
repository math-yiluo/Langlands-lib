# Pullback of reflex determinant sections

This internal result is derived from the existing actual reflex determinant
and structure-section maps in `LieDeterminantCondition`. It adds the scheme
pullback compatibility needed for that construction; it does not translate an
additional theorem from the literature.

For any commutative ring object `R`, structure map `s : S ⟶ Spec R`,
morphism `f : T ⟶ S`, source open `U` and target open `W ≤ f ⁻¹ᵁ U`,
`secHom_comp_appLE` proves the equality of actual ring maps

```text
secHom s U ≫ f.appLE U W e = secHom (f ≫ s) W.
```

Unfolding `secHom` reduces this to composition of the scheme morphisms' actual
section maps `appLE`. The full inverse-image form uses `f.app U`.

The Harris specialization retains exactly the central-simple unitary datum,
Harris signature charts, CM-section witness and reflex field used by
`harrisReflexSectionDeterminant`. Mapping that polynomial's coefficients
along `f.appLE U W e` gives the actual reflex determinant polynomial for the
composite structure map `f ≫ s` on `W`. The proof composes polynomial maps
and uses the preceding equality of structure ring maps. Taking every monomial
coefficient gives the corresponding equality of structure-sheaf sections.
The full inverse-image polynomial identity is also provided.

The general ring-map lemma permits any scheme universe; the Harris
specialization uses universe zero, as the imported datum does. The source and
target schemes are otherwise arbitrary, including nonreduced schemes; there is
no flatness hypothesis. These statements only transport the reflex side of the
determinant equality. They do not assert equality with a Lie determinant or
prove Lie-action naturality under base change.
