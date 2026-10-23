# The principal-idele coefficient sequence

This module constructs the actual sequence

`0 → Eˣ → J_E → C_E → 0`

as a short exact sequence of representations of `Gal(E/F)`, and constructs
its two induced maps on ordinary group cohomology in every degree. It uses
the published `relativeIdeleRepresentation` and `relativeIdeleCohomology`
from `IdeleCohomology`, the published `unitsRepresentation` for `Eˣ`, and
`relativeIdeleClassRepresentation` for `C_E`. All exported declarations are
in `Langlands.ClassField.Global`.

Here `J_E = NumberField.IdeleGroup (𝓞 E) E` is the group of units of the
full adele ring. The principal map is Mathlib's
`IdeleGroup.unitEmbedding (𝓞 E) E`, obtained from the field's diagonal
embedding in the adeles. The subgroup `IdeleGroup.principalSubgroup` is its
range, and `C_E = NumberField.IdeleClassGroup (𝓞 E) E` is the quotient by
that subgroup. In this module, “principal” refers to principal ideles from
all of `Eˣ`; it does not refer to a higher local unit filtration.

## Parameters and coefficient conventions

The main construction takes `F E : Type u`, `[Field F]`, `[Field E]`,
`[NumberField E]`, and `[Algebra F E]`. The universe `u` is arbitrary.
No normality or Galois hypothesis is required for this coefficient sequence;
it is equivariant under the group of `F`-automorphisms of `E`.

All three multiplicative groups are represented through `Additive`, with
scalar ring `NormalizedTwoCocycle.CoefficientScalars.{u} = ULift.{u} ℤ`.
Addition denotes multiplication in the original group, zero denotes its
identity, and scalar multiplication by `r` denotes raising to `r.down`.
The actions on `J_E` and `C_E` are the published arithmetic actions induced
by `ideleEquiv σ.toRingEquiv` and its quotient action. Cohomology is
Mathlib's ordinary `groupCohomology` of these representations. No continuous
cochain condition or topological exactness assertion is introduced here.

## The maps and exactness

`relativeIdeleAut_unitEmbedding` proves that applying an automorphism to
a principal idele agrees with first applying the automorphism to its field
unit. It reuses `ideleEquiv_diagonal`.
`relativeIdeleClassAut_quotient` gives the matching formula for the quotient
projection; it follows by unfolding the published quotient action.

`principalIdeleLinear F E` is the principal map on the additive coefficient
modules. `principalIdeleCoefficients F E` equips it with its equivariance,
so it is a morphism `unitsRepresentation F E ⟶ relativeIdeleRepresentation F E`.
`ideleQuotientLinear F E` and `ideleQuotientCoefficients F E` are the actual
quotient projection in the same two forms. Linearity follows from the
multiplication and integer-power laws of the underlying group homomorphisms.
The two `_apply` lemmas on the representation morphisms give exactly the
principal-embedding and quotient values.

The basic correctness lemmas are:

- `principalIdeleCoefficients_injective`: equality of principal ideles
  implies equality of their field units, by `Units.ext` and
  `AdeleRing.algebraMap_injective`.
- `ideleQuotientCoefficients_surjective`: every quotient class has an idele
  representative, by `QuotientGroup.mk_surjective`.
- `principalIdeleCoefficients_range_eq_ker`: the range of the first linear
  map equals the kernel of the second. Both directions use
  `QuotientGroup.eq_one_iff`, together with the definition of the principal
  subgroup as the range of `unitEmbedding`.
- `principalIdeleCoefficients_comp_ideleQuotientCoefficients`: the composite
  is the zero morphism, since each principal idele belongs to the principal
  subgroup.

`ideleCoefficientSequence F E` packages these maps and their zero composite
as a `ShortComplex`. `ideleCoefficientSequence_shortExact` proves its
`ShortExact` property. A private helper reflects exactness through the
faithful forgetful functor from representations to modules and applies
`ShortComplex.moduleCat_exact_iff_range_eq_ker`. The injectivity and
surjectivity lemmas give the categorical monomorphism and epimorphism via
`Rep.mono_iff_injective` and `Rep.epi_iff_surjective`.

## Ordinary cohomology and degree two

For every `n : ℕ`, `principalIdeleCohomologyMap F E n` and
`ideleQuotientCohomologyMap F E n` are `groupCohomology.map` along the identity
group homomorphism with the two coefficient morphisms above. Their source
and target are respectively

`Hⁿ(Gal(E/F), Eˣ) → Hⁿ(Gal(E/F), J_E) → Hⁿ(Gal(E/F), C_E)`.

`principalIdeleCohomologyMap_comp_ideleQuotientCohomologyMap` proves that
these consecutive maps compose to zero, also for `n = 0`. The proof uses
`groupCohomology.map_id_comp`, the coefficient-level zero composite, and
preservation of zero morphisms by the cohomology functor. The module does
not claim that these three cohomology groups form a short exact sequence,
or prove image-kernel equality on cohomology.

`principalIdeleCocycles₂` and `ideleQuotientCocycles₂` are Mathlib's
`mapCocycles₂` for the same maps. Their `_apply` lemmas state that the value
at `(σ, τ)` is respectively the principal idele or quotient class of the
original cocycle's value there. The `_H2π` lemmas state that applying the
cohomology map to `H2π z` gives `H2π` of the mapped cocycle; both specialize
`groupCohomology.H2π_comp_map_apply`. These are actual Mathlib cocycles and
classes, without any choice of representatives in the map definitions.

## Finite-place compatibility

For this section, `F` is also a number field, `E/F` is normal, and `w` is a
finite place of `E` above a finite place `v` of `F`.
`principalIdeleCoefficients_comp_ideleLocalProjection` states that the
principal map restricted along `FundamentalClass.decompositionHom v w`,
followed by `ideleLocalProjection v w`, equals `unitsLocalization v w`.
The proof is pointwise: the finite coordinate of a principal idele is the
image of its field element in the completion, using the published
`ideleCoordinate_unitEmbedding` and `Units.ext`.

`principalIdeleCohomologyMap_comp_ideleLocalMap` consequently proves, for
every degree `n`,

`principalIdeleCohomologyMap F E n ≫ ideleLocalMap v w n = unitsLocalMap v w n`.

This is `groupCohomology.map_comp` applied to the coefficient equality.
No semilocal Shapiro theorem, archimedean compatibility, reciprocity law,
cohomological vanishing, connecting map, or invariant existence theorem
is asserted in this module.

## Sources and provenance

The original arithmetic objects and actions are those of Artin and Tate,
*Class Field Theory* (AMS Chelsea, 2009), Preliminaries §1, printed pp. 1–2
(PDF pp. 10–11). Chapter VII §3, printed pp. 42–43 (PDF pp. 51–52), supplies
the cohomological context for ideles and their local components. The
registered source is `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
These passages motivate the coefficient sequence and local compatibility;
the module asserts no arithmetic consequence from that chapter beyond its
explicit constructions and identities.

The Lean implementation is an internal construction from Mathlib's actual
principal embedding, quotient, short-complex API, and ordinary cohomology
functor, together with the published project actions and coordinate maps.
The correctness proofs follow the quotient and functoriality arguments
described above. The new Lean and Markdown pair was authored by Worker 54;
Worker 269's published `IdeleCohomology` is reused by import.
