# Actual finite etale cover over a nonreduced irreducible affine base

This is a derived scheme construction for the prescribed-extension step in
Stacks Project, Lemma 37.24.8, tag 0551, proof. The registered source is
`stacks-generic-geometric-irreducibility-2026-11-04`, file `0551.html`,
especially the paragraph starting with a nonempty affine open and ending
with the finite etale shrinking. The algebraic construction and its
specified generic extension are supplied by
`FiniteSeparableNilradicalEtaleModel`; the actual residue-field comparison
before localization is supplied by `FiniteSeparableNilradicalGenericPoint`.

All rings and schemes in this module lie in one universe. Let `R` be a
commutative ring with irreducible prime spectrum. Its nilradical is prime,
and `K` is a specified fraction field of the literal domain
`R / nilradical R`. Let `L` be a field algebraic over `K`, with the compatible
quotient and original-base algebra structures specified in Lean. Given an
actual `FiniteSeparableNilradicalEtaleModel R K L`, write `A` for its
unlocalized monic quotient, `r` for its denominator, `B = R[1/r]`, and
`C = B tensor_R A`. These are the literal types used in the definitions,
not abstract scheme presentations assumed to have the desired properties.
The predecessor's proved constructor supplies such a model whenever
`L/K` is finite dimensional and separable.

The construction proceeds as follows.

- `baseScheme`, `modelScheme`, and `liftedModelScheme` are respectively
  `Spec B`, `Spec C`, and `Spec A`. The tensor product's right algebra
  structure makes `C` a localization of `A` away from the image of `r`.
  `toLiftedModel` is the corresponding actual open immersion on spectra.
- `extensionAlgebra` is obtained from the proved generic tensor
  equivalence with the original `L`. This gives a ring map `C -> L` and
  proves `C` is nontrivial. Thus `Spec C` is nonempty. The earlier
  nilradical computation makes `Spec A` irreducible, and its nonempty open
  subscheme `Spec C` is irreducible as well.
- `toBase` is the spectrum map induced by `B -> C`. The predecessor's
  finite, free, and etale algebra instances give a finite etale scheme
  morphism. A nontrivial free algebra is faithful; integrality then gives
  surjectivity of the actual spectrum map.
- `baseOpen` is the principal open `D(r)` in `Spec R`. The denominator
  avoids the base nilradical, so the base generic prime belongs to this
  open. `localizationIso` identifies `Spec B` with this actual open
  subscheme, using the equality of the localization map's range with
  `D(r)`. The composite `coverMap : Spec C -> D(r)` is therefore finite,
  etale, and surjective, with an affine irreducible source.

The generic residue-field comparison uses the actual stalk residue fields
of these schemes. The lemma `toLiftedModel_genericPoint` shows that the
generic point of `Spec C` maps to the previously computed generic prime
of `A`. An open immersion induces an isomorphism on residue fields.
`modelGenericResidueFieldIso` composes the earlier comparison for `A`,
the residue-field congruence for that equality of points, and the inverse
of the induced spectrum isomorphism. Its type is precisely

```text
Spec L ≅ Spec ((Spec C).residueField (genericPoint (Spec C))).
```

`modelGenericResidueFieldIso_hom_toLiftedModel` proves compatibility with
the residue-point morphism to `Spec A`. Its proof applies naturality of
the residue-point morphism, cancels the residue-field isomorphism, and
uses the residue-field congruence identity.

The lemma `coverMap_ι` proves that the two coefficient factorizations from
`Spec C` to `Spec R` agree: one goes through `Spec B` and the open
inclusion, and the other through `Spec A`. The proof reduces equality of
spectrum maps to equality of the original coefficient ring maps and
uses the two scalar towers. Consequently
`modelGenericResidueFieldIso_hom_coverMap_ι` proves

```text
e.hom >> (Spec C).fromSpecResidueField η' >> coverMap >> D(r).ι
  = Spec.map (K -> L) >> Spec.map (R -> R/nilradical R -> K),
```

where `e` is the constructed isomorphism and `η'` is the actual generic
point of `Spec C`. The earlier unlocalized coefficient triangle and the
open-immersion compatibility prove this identity. Thus the construction
preserves the specified extension and its map to the original,
potentially nonreduced affine base.

This unit establishes the affine scheme cover and its actual generic
residue-field triangle. It imposes no reducedness, domain, or
Noetherianity condition on `R`. Transport to an arbitrary irreducible
scheme, geometric splitting of components, the complete assertion of
Stacks 0551, and the geometric-fibre results used in Conrad remain
separate obligations.
