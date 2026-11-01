# Spreading out a fibre degree-zero restriction isomorphism: proof

Authors: Worker 1119 wrote the algebraic proof that this module reuses, in the
helper modules under `Langlands/Cohomology/ModuleComplex/FibreH0RestrictionSpread/`.
Its row-minor lemma in `Split` is adapted from Worker 606. Worker 950 designed the
published statement. Worker 1098 wrote this exact-target wrapper.

Module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadProof` proves
the published proposition
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement.{u}`, for an
arbitrary universe `u`, as the theorem

```lean
theorem Langlands.Cohomology.ModuleComplex.fibreH0RestrictionSpread :
    FibreH0RestrictionSpreadStatement.{u}
```

The theorem has exactly the statement as its type, with no further hypotheses or
data. It imports the statement module unchanged. It assumes no unproved Library
proposition, and in particular neither `LocalMinimalPerfectStatement` nor
`PrimeMinimalPerfectStatement`. It uses no `sorry` and no new axioms.

## Proof

The proof is the term `FibreH0Spread.fibreH0RestrictionSpread`, imported from
module `Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Main`. That
theorem already has type `FibreH0RestrictionSpreadStatement.{u}`. This module only
restates it under the name and module expected by the proof task, so that
consumers can import the exact-target theorem directly.

The argument itself is documented in `FibreH0RestrictionSpread/Main.md` and the
Markdown of its helper modules `Model`, `Core`, `Homology` and `Split`. In
outline, for `p = ker φ₀`:

1. The published theorems `primeMinimalPerfect` and `primeFreeHomotopyDescent`
   give finite free models of `K`, `K₁` and `K₂`, homotopy equivalent to their
   scalar extensions, over one localization `A = R[1/r]` with `φ₀ r ≠ 0`. The
   term ranks are the homology dimensions over the residue field `κ(p)`.
2. Hence the models have zero differentials after scalar extension to `κ(p)`,
   and so also after extension to `k` along the map `κ(p) →+* k` induced by
   `φ₀`. The negative-homology hypotheses make the degree `-1` terms zero. The
   universal rank-one degree-zero homology of `K₁` and `K₂`, together with the
   fibre bijectivity, makes the three degree-zero terms free of rank one.
3. The chain maps are transported to the models as
   `e.hom ≫ (baseChange α).map ψⱼ ≫ eⱼ.inv`, and natural homology comparisons
   carry the fibre hypotheses to these transported maps.
4. The `Core` theorem `exists_bijective_of_finiteFree` gives `a = a₀ * a₁ : A`,
   nonzero at the fibre, such that the degree-zero homology map of the first
   transported map is bijective after every ring map `β` inverting `a`. Universal
   rank-one degree-zero homology forces the target degree-zero differentials to
   vanish after `β`. A row minor and its adjugate (`Split`) split the jointly
   injective degree-one components up to the scalar `a₁`, which kills the source
   degree-zero differential after `β`. The degree-zero component is split up to
   `a₀` in the same way; as its source and target are free of rank one, it is
   bijective after `β`.
5. Clearing the denominator of `a` gives an element `r * s` of `R` with
   `φ₀ (r * s) ≠ 0`. Any ring map `R →+* T` inverting it factors through `A` and
   inverts `a`, so the degree-zero map of `ψ₁` is bijective after it.

## Provenance

The statement Markdown records the derivation from Stacks Project tag 0BF2
(`more-morphisms.tex`, proof lines 9543–9619, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). `Main.md` explains how the reused
proof follows that route and where it differs: the field `k` is reached through
the residue field of `ker φ₀`, so no faithful flatness argument is needed, and
the splittings are explicit up to a scalar, so the conclusion holds after every
ring map inverting one element.
