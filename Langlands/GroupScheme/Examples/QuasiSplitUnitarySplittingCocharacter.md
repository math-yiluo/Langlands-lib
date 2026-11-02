# The splitting of `U(1,1)` carries `λ` to `t ↦ diag(t, t⁻¹)`

Author: Worker 293. This module adds the supporting lemma of definition unit 3
of task `be70310c-1939-4a82-8293-c4d33f5883ae`. It combines two published
modules: the splitting isomorphism `splittingIso b c hc` of
`Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting` (Worker 293), and
the cocharacters `weightCocharacter b c m` and `cocharacter b c` of unit 2,
`Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic` (Worker 399).

Throughout, `F` and `E` are fields in one universe `u`, `E` is quadratic over
`F`, and `c : E ≃ₐ[F] E` satisfies `c ≠ AlgEquiv.refl`. The splitting takes
this as the explicit argument `hc`. No assumption on the characteristic of `F`
is made.

## Sources and provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`.
Proposition 24.40(b) (printed p.523) and display (158) (printed pp.524–525)
give the splitting of a unitary group over a splitting field of its centre, by
`X ↦ (X, (Xᵗ)⁻¹)`. The splitting module records how its explicit version is
derived from that source. The present lemma is the task's supporting
computation for unit 3. It is not stated in Milne: it is an entrywise
calculation with the explicit splitting.

## The base change of a cocharacter

`baseChangeCocharacter b c χ` is defined for a cocharacter
`χ : (Gm (Spec F)).toGrp ⟶ groupScheme b c`. It is the cocharacter of
`baseChangeGroupScheme b c` (the pullback along `Spec E ⟶ Spec F`, written
`scalarBaseMap F E`) obtained from `χ` by base change. It is the composite of
the inverse of the Library isomorphism `Gm.baseChangeIso` between the pullback
of `𝔾ₘ` over `Spec F` and `𝔾ₘ` over `Spec E`, followed by the pullback of `χ`
(`GroupScheme.baseChange (scalarBaseMap F E)).map χ`).

`baseChangePointsEquiv_baseChangeCocharacter` describes it on points. Let `T`
be a scheme over `Spec E` and `x` a `T`-point of `𝔾ₘ`. The point
`x ≫ baseChangeCocharacter b c χ`, transported by the Library's pullback point
equivalence `GroupScheme.baseChangePointsEquiv`, is `χ` applied to the same unit
of `Γ(T.left, ⊤)` over `T` regarded as an `F`-scheme. The proof uses
`GroupScheme.baseChangePointsEquiv_comp` and
`Gm.baseChangeUnitsEquiv_baseChangeIso_inv`.

## The splitting and the cocharacters

`weights m` is unit 2's weight vector `![m, -m]`, and
`GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights m)` is
the Library's diagonal cocharacter of `GL₂` over `Spec E`. On points it is
`t ↦ diag(tᵐ, t⁻ᵐ)` (`GroupScheme/Dynamic/GeneralLinear`).

`baseChangeCocharacter_weightCocharacter_splittingIso b c hc m` states the
equality of homomorphisms of group schemes over `Spec E`

`baseChangeCocharacter b c (weightCocharacter b c m) ≫ (splittingIso b c hc).hom
  = GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights m)`.

The proof is by `hom_ext_points` and is an entrywise check on `T`-points for
every `T`. The point of the left side is computed with
`splittingIso_hom_points`, `basePointsEquiv_apply`, the lemma above, unit 2's
`pointsEquiv_weightCocharacter` and `diagonalUnitary_val`. Its `(i, j)` entry is
the first coordinate under `tensorSplit` of `1 ⊗ tʷ` on the diagonal, with
`w = (weights m) i`, and of `0` off the diagonal. By `tensorSplit_tmul` the
diagonal value is `tʷ · 1 = tʷ`, and the off-diagonal value is `0`. This agrees
with `diag(tᵐ, t⁻ᵐ)`.

`baseChangeCocharacter_cocharacter_splittingIso b c hc` is the case `m = 1`:
the splitting `G_E ≅ GL₂` carries the base change of `λ = cocharacter b c` to
`t ↦ diag(t, t⁻¹)`. This is the supporting lemma requested in deliverable 3.
Unit 2 defines `inverseCocharacter b c` (`λ'`, `t ↦ diag(t⁻¹, t)`) as
`weightCocharacter b c (-1)`, so the case `m = -1` is the corresponding
statement for `λ'`. It is not stated separately here.

## Not included here

Test schemes are arbitrary: no affineness, reducedness or finiteness
hypothesis is imposed. Rank, noncommutativity, reductivity and the dynamic
subgroups are not asserted in this module.
