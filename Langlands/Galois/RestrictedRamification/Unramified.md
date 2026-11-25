# Extensions unramified outside a set of finite places

`Langlands/Galois/RestrictedRamification/Unramified.lean`, namespace `Langlands.Galois`.

Let `K` be a number field, `Ω` a field over `K` and `S` a set of finite places of `K`
(`HeightOneSpectrum (𝓞 K)`). An intermediate field `E` of `Ω / K` is *unramified outside `S`* if
every finite place of `K` outside `S` is unramified in `𝓞 E`. The infinite places play no role:
in the language of Neukirch–Schmidt–Wingberg, `S` together with all archimedean places is the set
of places at which ramification is allowed. The notion is meant for finite `E` (then `𝓞 E` is the
ring of integers of a number field); for infinite `E` the condition is about Mathlib's `𝓞 E` and
is not used.

```lean
def finitePlacesAbove (L : Type*) [Field L] [Algebra K L] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Set (HeightOneSpectrum (𝓞 L))           -- {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}
def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal
theorem isUnramifiedAt_under_iff_inertia [IsGalois F M] (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x
theorem IsUnramifiedOutside.sup [IsGalois F Ω] [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (h₁ : IsUnramifiedOutside S E₁) (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂)
theorem IsUnramifiedOutside.map [IsGalois F Ω] [FiniteDimensional F E] (hE : IsUnramifiedOutside S E)
    (τ : Gal(Ω/F)) : IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω))
theorem isUnramifiedOutside_restrictScalars_iff (S) (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal)
    (M : IntermediateField L Ω) [FiniteDimensional L M] :
    IsUnramifiedOutside S (M.restrictScalars F) ↔ IsUnramifiedOutside (finitePlacesAbove L S) M
```

## Outline of the proofs

- *Tower.* For number fields `F ⊆ L ⊆ M` the ramification index is multiplicative
  (`Ideal.ramificationIdx_tower`), and a prime is unramified exactly when its ramification index is
  `1` (`Ideal.ramificationIdx_eq_one_iff`); hence `isUnramifiedAt_tower_iff`.
- *Inertia.* In a finite Galois extension `M / F` the inertia group of `Q` has order
  `e(Q | F)`, and the inertia group of `Q` in `Gal(M / E)` is the intersection of that of `Gal(M / F)`
  with `Gal(M / E)`. Comparing orders through the tower formula, `Q ∩ E` is unramified over `F` if
  and only if the inertia group of `Q` lies in `Gal(M / E)`, i.e. fixes `E`
  (`isUnramifiedAt_under_iff_inertia`); for intermediate fields of `Ω` this becomes
  `isUnramifiedIn_iff_inertia` and `isUnramifiedIn_iff_le_fixedField`.
- *Compositum, `⊥`, conjugates.* Put `E₁ ⊔ E₂` (or `E`) into a finite Galois subextension `M`
  (`exists_finiteGaloisIntermediateField_le`, the normal closure); the criterion says that both
  fields lie in the fixed field of every inertia group above `v`, hence so does `E₁ ⊔ E₂`. For a
  conjugate `τ(E)`, the inertia group of `Q` is conjugate to that of `ρ⁻¹ Q`, `ρ` the restriction
  of `τ` to `M`.
- *Restriction of scalars.* A place of `L` outside `finitePlacesAbove L S` lies over a place of
  `F` outside `S`, and conversely; the tower formula moves unramifiedness between `M / F` and
  `M / L` when `L / F` is unramified outside `S`.
- *Finitely many ramified primes.* A prime with ramification index `e ≥ 2` divides the different
  ideal (`pow_sub_one_dvd_differentIdeal_aux`: `P^{e-1}` divides it), which is nonzero.
- *Valuations.* An element `σ` of a group acting on a Dedekind domain moves height one primes
  (`smulPlace`) and transports valuations: `v_{σw}(σx) = v_w(x)`; in an extension unramified at
  `W | w` the valuation of `W` restricts to that of `w`.

## Declarations

- `finitePlacesAbove L S`, `mem_finitePlacesAbove`, `liesOver_iff_eq_under`,
  `mem_finitePlacesAbove_iff_under` (`w` lies above `S` iff `w.under (𝓞 K) ∈ S`),
  `finitePlacesAbove_mono`, `finite_finitePlacesAbove` (finite above a finite `S`),
  `mem_finitePlacesAbove_of_natCast_mem` (if `S` contains the places above `n`, so does
  `finitePlacesAbove L S`).
- `isUnramifiedAt_tower_iff`.
- `dvd_differentIdeal_of_ramificationIdx_ne_one`, `finite_setOf_ramificationIdx_ne_one` (a ramified
  prime divides the different, so only finitely many primes ramify), `finite_setOf_natCast_mem`.
- `restrictScalars_mem_inertia_iff`, `mem_range_restrictScalarsHom_iff`,
  `isUnramifiedAt_under_iff_inertia`.
- `IsUnramifiedOutside`, `IsUnramifiedOutside.ramificationIdx_eq_one`,
  `isUnramifiedOutside_of_ramificationIdx_eq_one`, `finiteDimensional_of_le`, `isUnramifiedIn_of_le`,
  `IsUnramifiedOutside.of_le`, `IsUnramifiedOutside.mono`, `isUnramifiedIn_iff_inertia`,
  `mem_map_fixedField_iff`, `isUnramifiedIn_iff_le_fixedField`.
- With `[IsGalois F Ω]`: `exists_finiteGaloisIntermediateField_le`, `isUnramifiedIn_sup`,
  `IsUnramifiedOutside.sup`, `isUnramifiedIn_bot`, `isUnramifiedOutside_bot`, `isUnramifiedIn_map`,
  `IsUnramifiedOutside.map`.
- `isUnramifiedOutside_restrictScalars_iff`.
- Valuations: `eq_of_forall_le_exp_iff`, `smulPlace σ w` with `smulPlace_asIdeal`,
  `intValuation_smulPlace`, `valuation_smulPlace`, `valuation_smulPlace_apply`,
  `valuation_algebraMap_of_isUnramifiedAt`.

- The action of `Gal(L/K)` on the places of `L` (namespace `Langlands.Galois`, `K L : Type u`):
  instance `finitePlaceAction : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L))`, `σ • w` the place with
  valuation `x ↦ w(σ⁻¹ x)` (through `finitePlaceEquiv` of `Langlands.Global.AdelicFunctoriality.Finite`;
  `smul_finitePlace_def`, `valuation_smul_finitePlace`), with `under_smul_finitePlace`
  (`(σ • w) ∩ 𝒪_K = w ∩ 𝒪_K`), and the instance `finitePlacesAboveAction` on `finitePlacesAbove L S`
  (`coe_smul_finitePlacesAbove`).

Complete types of these, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.Galois.finitePlaceAction.{u} {K L : Type u} [Field K] [Field L] [Algebra K L] :
  MulAction Gal(L/K) (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
Langlands.Galois.smul_finitePlace_def.{u} {K L : Type u} [Field K] [Field L] [Algebra K L] (σ : Gal(L/K))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
  σ • w = (Langlands.Global.AdelicFunctoriality.finitePlaceEquiv σ⁻¹.toRingEquiv) w
Langlands.Galois.valuation_smul_finitePlace.{u} {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  (σ : Gal(L/K)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) (x : L) :
  (IsDedekindDomain.HeightOneSpectrum.valuation L (σ • w)) (σ x) = (IsDedekindDomain.HeightOneSpectrum.valuation L w) x
Langlands.Galois.under_smul_finitePlace.{u} {K L : Type u} [Field K] [Field L] [Algebra K L] (σ : Gal(L/K))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
  IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) (σ • w) =
    IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) w
Langlands.Galois.finitePlacesAboveAction.{u} {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  MulAction Gal(L/K) ↑(Langlands.Galois.finitePlacesAbove L S)
Langlands.Galois.coe_smul_finitePlacesAbove.{u} {K L : Type u} [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (σ : Gal(L/K))
  (w : ↑(Langlands.Galois.finitePlacesAbove L S)) : ↑(σ • w) = σ • ↑w
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/MaxUnramifiedOutside.lean` (lines
11–27: `placesOver`, `IsUnramifiedOutside`), `Unramified.lean`, `Ramification.lean`,
`ValuationTransport.lean`, `ClassFieldGSUnram.lean` (lines 66–80:
`ramificationIdx_eq_one_of_isUnramifiedOutside`, `isUnramifiedOutside_of_ramificationIdx_eq_one`),
`GlobalClassFormation/IdeleCohomology/Ramified.lean` (`ramified_dvd_differentIdeal`,
`finite_setOf_ramified`), `PoitouTate/PoitouTateInfinite/LevelModulesDefs.lean` (lines 35–43:
`finite_setOf_natCast_mem`), the section on restriction of scalars of
`IsUnramifiedOutsideIffLeMaxUnramifiedOutside.lean` and of `BaseChangeDefs.lean`
(`isUnramifiedOutside_restrictScalars_iff_of_isUnramifiedIn`), `FiniteOpen.lean` (lines 17–45:
`placesOver_finite`, `mem_placesOver_of_natCast_mem`) and `SUnits.lean` (lines 50–65:
`mem_placesOver_iff`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: `placesOver` is
`finitePlacesAbove` with `L` explicit (Mathlib's `InfinitePlace.placesOver` is another notion);
the source's `underPlace` is Mathlib's `HeightOneSpectrum.under`; the two versions of the
restriction-of-scalars lemma (for an intermediate field `L` and for a number field `L` with an
unramifiedness hypothesis) are one theorem; `ramified_dvd_differentIdeal` →
`dvd_differentIdeal_of_ramificationIdx_ne_one`, `finite_setOf_ramified` →
`finite_setOf_ramificationIdx_ne_one`, `ramificationIdx_eq_one_of_isUnramifiedOutside` →
`IsUnramifiedOutside.ramificationIdx_eq_one`, with `w : HeightOneSpectrum (𝓞 E)` and an instance
`LiesOver` in place of the source's subtype of places over `v`; `exists_finiteGalois_le` of the foundations is restated
as `exists_finiteGaloisIntermediateField_le`, so that the file imports Mathlib only.

The action on places (`finitePlaceAction` … `coe_smul_finitePlacesAbove`) contains no text of the source.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VIII, §3, p. 452 (`k_S`, `G_S`, and the convention that `S`
  contains the archimedean places), and chapter IX, §1, p. 523 (`k_S` for an arbitrary set `S`,
  with the convention that `ℂ | ℝ` is ramified). Here `S` is a set of finite places and the real
  places may always ramify, which is Neukirch–Schmidt–Wingberg's `S ∪ S_∞`.
- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter I,
  §9, Proposition (9.6), p. 57 (with separable residue field extension the inertia group of a
  prime in a Galois extension has order `e`).
