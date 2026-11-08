# Multiplicity spaces of the cohomology of the actual CM tower as Galois representations

This internal construction applies the generic module
`Langlands.Shimura.MultiplicityGaloisRepresentation` to the published Galois
actions on the cohomology of the actual geometric CM tower. It assumes the
Library statement `HarrisCMLevelGaloisSmoothStatement`, which says that
`Gal(F̄/F)` acts smoothly on the shrinking-level cohomology. Under this
statement the restricted Galois action on each isotypic part is smooth. If
moreover a representation `ξ` of `GG(A_f)ᵐᵒᵖ` is finitely generated over the
group algebra, the Galois action on the multiplicity space `Hom(ξ, H^d)` is
smooth too. Over a topological field `R`, a finite-dimensional multiplicity
space is then a continuous Galois representation of `F`, an object of
`Langlands.GaloisRepresentation.Objects F R`. Its Euler polynomial at a
finite place `w` where the cohomology is unramified is the Frobenius Euler
polynomial of the multiplicity space. The same holds for the prime-to-`m`
cohomology and representations of `GG(A_f^{(m)})ᵐᵒᵖ`, where the smoothness
of the Galois action is an explicit hypothesis. All declarations are in
namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, describes the Galois representations
that occur in `H^{n-1}(S_K(N), W)[π]`. Part (ii) characterizes them by their
Frobenius characteristic polynomials at almost all unramified places,
through formula (5.6). Formulas (5.2), (5.3) and (5.5) on printed
pp. 312-313 use spaces of intertwining maps of representations. This module
makes the multiplicity spaces of the published CM cohomology modules into
continuous Galois representations with Euler polynomials, so that they can be
compared through `HasEulerPolynomialAt`.

The coefficients are module sheaves on `Spec F`, pulled back to every level.
The module does not construct Harris's coefficient systems `W`, the
representation `JL(π_f)`, or compactly supported or adic cohomology. It does
not prove `HarrisCMLevelGaloisSmoothStatement`, the smoothness of the Galois
action on the prime-to-`m` cohomology, the finite dimension of any
multiplicity space, or unramifiedness at any place. These are hypotheses of
the results. `ξ` is an arbitrary representation, finitely generated over the
group algebra where stated. No statement of Harris is formalized.

## Inputs

The CM data `E`, `F`, `L`, `D`, `C`, the named propositions `preservation`
through `htor`, `q : CMRepresentabilityStatement ...` and the inputs
`existence`, `geometry`, `hRigid` and `criterion` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. Below `...`
abbreviates them. Write `base` for `Spec (CommRingCat.of F)`. Let
`U : Type uU` be an `R`-module.

- The published `cmSmallLevelGaloisCohomologyFunctor ... R d`, written `H d`,
  and, for `m : ℕ`, `hm : m ≠ 0` and a level `K₀` of
  `(D.rationalInvolution.DividingPoints m)ᵐᵒᵖ`, the published
  `cmPrimeToGaloisCohomologyFunctor ... m hm K₀ ... R d`, written `H' d`.
  Both send `ModuleSheaf base R` to actions of `F̄ ≃ₐ[F] F̄`, which is
  definitionally `Field.absoluteGaloisGroup F`.
- The published
  `Langlands.Cohomology.HarrisCMLevelGaloisSmooth.HarrisCMLevelGaloisSmoothStatement ... R`
  (Worker 3): for every `d`, `M` and class `x` of `(H d).obj M`, some open
  subgroup of `F̄ ≃ₐ[F] F̄`, with its Krull topology, fixes `x`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMIsotypicCohomology` (candidate
  `06482d9c-709f-449e-bd42-538102e24d51`, accepted and awaiting
  publication): `cmSmallLevelIsotypicCohomologyFunctor`,
  `cmSmallLevelMultiplicityFunctor`, `cmPrimeToIsotypicCohomologyFunctor`
  and `cmPrimeToMultiplicityFunctor`.
- From `Langlands.Shimura.MultiplicityGaloisRepresentation`, submitted
  together with this module: `isSmooth_isotypicGaloisRepresentation`,
  `isSmooth_multiplicityRepresentation`, `multiplicityObjects` and its
  Euler-polynomial results. It uses `multiplicityActionFunctor` and
  `galoisRepresentation` of `Langlands.Shimura.IsotypicGaloisAction`.
- `FrobeniusPolynomial.frobeniusEulerPolynomial` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication), and `IsUnramifiedAt`, `IsUnramifiedAlong` and
  `geometricFrobenius` of the published
  `Langlands.Shimura.DecompositionGroupAction`.

## Smoothness

Let `R : Type` be a commutative ring and `hsmooth` a proof of
`HarrisCMLevelGaloisSmoothStatement ... R`.

- `cmSmallLevelGaloisCohomology_isSmooth ... R hsmooth d M`: the
  representation `galoisRepresentation ((H d).obj M)` is smooth
  (`Langlands.IsSmooth`).
- `cmSmallLevelIsotypicCohomology_isSmooth ... R ξ hsmooth d M`: for
  `ξ : Representation R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ U`, the
  Galois action on `(cmSmallLevelIsotypicCohomologyFunctor ... R ξ d).obj M`
  is smooth.
- `cmSmallLevelMultiplicity_isSmooth`: if moreover
  `[Module.Finite (MonoidAlgebra R D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) ξ.asModule]`,
  the representation `((cmSmallLevelMultiplicityFunctor ... R ξ d).obj M).ρ`
  is smooth.
- `cmPrimeToIsotypicCohomology_isSmooth ... d M hM` and
  `cmPrimeToMultiplicity_isSmooth ... d M hM`: the analogues for
  `ξ : Representation R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ U`, with
  `cmPrimeToIsotypicCohomologyFunctor` and `cmPrimeToMultiplicityFunctor`,
  given a proof `hM` that `galoisRepresentation ((H' d).obj M)` is smooth.

## Continuous Galois representations

Let now `R : Type` be a field with a topology, and let `ξ` be finitely
generated over the group algebra as above. Let `w : Global.FinitePlace F`,
and let `j` be in `ClosureEmbedding (NumberField.FinitePlace.embedding w)`.

- `cmSmallLevelMultiplicityGaloisRepresentation ... R ξ hsmooth d M`: if
  `[Module.Finite R (ξ.IntertwiningMap ((H d).obj M).V.representation)]`,
  this is `multiplicityObjects` of `ξ` and `(H d).obj M`, an object of
  `Objects F R`.
- `cmSmallLevelMultiplicityGaloisRepresentation_apply`: `σ` sends an
  intertwining map `φ` to `(SmoothRep.hom (((H d).obj M).ρ σ)).comp φ`.
- `cmSmallLevelMultiplicityGaloisRepresentation_rank`: the rank is the
  dimension of the multiplicity space over `R`.
- `cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_iff`:
  the representation has Euler polynomial `P` at `w` if and only if the
  multiplicity action
  `(multiplicityActionFunctor ξ (Field.absoluteGaloisGroup F)).obj ((H d).obj M)`
  is unramified at `w` (`IsUnramifiedAt (ModuleCat R) w`) and its
  `FrobeniusPolynomial.frobeniusEulerPolynomial w` is `P`.
- `cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAlong hu`:
  if `(H d).obj M` is `IsUnramifiedAlong` at `w` and `j`, the Euler
  polynomial at `w` is the reverse of the characteristic polynomial of the
  geometric Frobenius endomorphism of the multiplicity action along `j`.
- `cmSmallLevelMultiplicityGaloisRepresentation_hasEulerPolynomialAt_of_isUnramifiedAt hu`:
  if `(H d).obj M` is unramified at `w`, the Euler polynomial at `w` is the
  Frobenius Euler polynomial of the multiplicity action.
- `cmPrimeToMultiplicityGaloisRepresentation ... R m hm K₀ ξ d M hM`, with
  `_apply`, `_rank`, `_hasEulerPolynomialAt_iff`,
  `_hasEulerPolynomialAt_of_isUnramifiedAlong` and
  `_hasEulerPolynomialAt_of_isUnramifiedAt`: the analogues for `H' d`, with
  the smoothness proof `hM` in place of `hsmooth`.

## Proof outline

`cmSmallLevelGaloisCohomology_isSmooth` repackages the open subgroup given
by `hsmooth` as membership in the fixed vectors, through
`Representation.mem_invariants`. All other results apply the corresponding
results of `Langlands.Shimura.MultiplicityGaloisRepresentation` to
`(H d).obj M` or `(H' d).obj M`; the descriptions of the action and the rank
hold by `rfl`.

## Provenance

This is an internal specialization of
`Langlands.Shimura.MultiplicityGaloisRepresentation` to the Galois actions on
the cohomology of the actual geometric CM tower. The smoothness input is the
published Library statement `HarrisCMLevelGaloisSmoothStatement`, used as a
hypothesis. No action, multiplicity space or Galois representation is
supplied as input. Harris (1999), Theorem 5.7 and formulas (5.2)-(5.6) on
printed pp. 312-313, is motivation only.
