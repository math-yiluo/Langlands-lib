# Actual finite etale scheme models of separable generic extensions

This derived construction interprets the domain-case finite etale model from
Stacks Project, Lemma 37.24.8 (0551), as actual schemes and morphisms.
The registered source is
`stacks-generic-geometric-irreducibility-2026-11-04`, `0551.html`, especially
the monic-model and shrinking argument in its proof. The source treats arbitrary
irreducible scheme bases; this unit treats the domain case only.

Let `R`, `K`, and `L` be in one arbitrary universe, with `R` a commutative domain,
`K` its specified fraction field, and compatible `R`- and `K`-algebra structures
on the field `L`. Let `d : FiniteSeparableEtaleModel R K L`.
For a finite separable extension `L/K`, the imported constructor
`finiteSeparableEtaleModel` supplies such a `d` without any additional
existence hypothesis. No Noetherianity, integral closedness, or characteristic
restriction is imposed on `R`.

Write `r = d.denominator`, `B = R[1/r] = d.Base`, and
`A = B ⊗[R] R[b] = d.Carrier`, where `b` is the constructed integral primitive
element. The imported algebra model proves that `r` is nonzero and that `A`
is a finite free etale domain algebra over `B`.

The definitions `baseScheme`, `modelScheme`, and `toBase` are literally
`Spec B`, `Spec A`, and the spectrum map of the structural algebra map.
The corresponding instances prove that `toBase` is finite, etale, and
surjective, and that `Spec A` is affine, integral, and irreducible.
Surjectivity uses lying over for the integral algebra map; freeness and
nontriviality supply faithfulness.

`baseOpen` is the actual principal open `D(r)` of `Spec R`.
`localizationMap` is the spectrum map of `R → B`. Localization makes this an
open immersion with range `D(r)`. The resulting `localizationIso` identifies
`Spec B` with the actual open subscheme, and `localizationIso_hom_ι` identifies
its map back to `Spec R`. Thus `coverMap` is an actual finite etale surjection
`Spec A → D(r)`. The principal open is nonempty: the generic point of the
domain `B` gives a point in the range of the localization map.

The supplied field `K` is also a fraction field of `B`. `genericBaseMap` is
the spectrum map of the compatible localized-base map `B → K`.
Assuming `L/K` algebraic, `genericIso` identifies the actual pullback
`Spec K ×[Spec B] Spec A` with `Spec L`. It composes the spectrum/tensor-product
pullback comparison with the imported `K`-algebra equivalence of the generic
model with `L`. `genericIso_inv_fst` proves that the projection to `Spec K`
is exactly the spectrum map of the original `K → L`.

`genericResidueFieldIso` uses the published fraction-field/generic-point
comparison to identify `Spec K` with the spectrum of the actual residue field
at the generic point of `Spec B`, over `Spec B`.
`genericPullbackToFiberIso` transports the pullback along that isomorphism and
swaps its factors. Consequently `genericFiberIso` identifies the actual
scheme-theoretic fibre of `toBase` at that generic point with `Spec L`.
`genericFiberIso_inv_toSpecResidueField` proves the structural-map equation:
the inverse comparison followed by the fibre's residue-field projection equals
`Spec L → Spec K` followed by `genericResidueFieldIso.hom`. This retains the
specified field extension rather than asserting only an abstract scheme
isomorphism.

This unit supplies the actual domain scheme cover and its generic comparison.
It does not construct the finite extension that splits geometric components,
prove the splitting conclusion, handle a nonreduced irreducible base, or prove
full Stacks 0551. Those remain separate obligations in the Conrad program.
