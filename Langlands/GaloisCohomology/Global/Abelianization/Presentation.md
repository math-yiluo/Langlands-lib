# A presentation of the `S`-idèle class group

`Langlands/GaloisCohomology/Global/Abelianization/Presentation.lean`, namespace
`Langlands.GaloisCohomology`.

For a number field `K` (`K : Type u`) and a finite set `S` of finite places (`[Finite S]`), the
`S`-idèle class group `SIdeleClassGroup S = I_K / K^× U^S` of the module
`Langlands.GaloisCohomology.Global.Abelianization.SIdeleClassGroup` is presented by the local
groups at `S` and the divisors prime to `S`:

`sPresentation S : (∀ w : S, (FiniteCompletion K w)ˣ) × Multiplicative (SDivisor S) →* SIdeleClassGroup S`

sends `(a, D)` to the class of the idèle with components `a_w` at `w ∈ S`,
`localUniformizer v ^ D(v)` at `v ∉ S` and `1` at the archimedean places. It is surjective
(`sPresentation_surjective`), and its kernel is the image of
`principalPresentation S : Kˣ →* (∀ w : S, (FiniteCompletion K w)ˣ) × Multiplicative (SDivisor S)`,
`x ↦ ((x)_{w ∈ S}, div_S(x))` (`ker_sPresentation`). Here `SDivisor S` and `sDivisorOf S`
(the divisor prime to `S` of a unit of `K`) are those of the module
`Langlands.GaloisCohomology.Global.Units.Divisor`.

The uniformizers are fixed: `globalUniformizer v` is an element of `K` of valuation `exp (-1)` at
`v` (a choice, from Mathlib's `valuation_exists_uniformizer`), and `localUniformizer v` its image
in `K_v` (`valued_localUniformizer`). The order of an idèle at a finite place is `ideleOrd v x`
(`valued_finiteIdeleProjection`); it vanishes at all but finitely many places
(`finite_setOf_ideleOrd_ne_zero`), and on principal idèles it is the order `ordAt v` of the element
(`ideleOrd_diagonalUnits`). The idèle of a divisor is `sDivisorIdele S` and the idèle with given
components at `S` is `sPlacesIdele S`; their components are computed by
`finiteIdeleProjection_sDivisorIdele` and `finiteIdeleProjection_sPlacesIdele`.
`sPresentation_apply_one_right` and `sPresentation_one_single` evaluate the presentation on the
two factors.

## Complete types

```lean
@Langlands.GaloisCohomology.globalUniformizer : {K : Type u} → [inst : Field K] → [NumberField K] → Langlands.Global.FinitePlace K → Kˣ

@Langlands.GaloisCohomology.valuation_globalUniformizer : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K),
  (IsDedekindDomain.HeightOneSpectrum.valuation K v) ↑(Langlands.GaloisCohomology.globalUniformizer v) =
    WithZero.exp (-1)

@Langlands.GaloisCohomology.ordAt_globalUniformizer : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K),
  Langlands.GaloisCohomology.ordAt v (Langlands.GaloisCohomology.globalUniformizer v) = 1

@Langlands.GaloisCohomology.localUniformizer : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] → (v : Langlands.Global.FinitePlace K) → (Langlands.Global.FiniteCompletion K v)ˣ

@Langlands.GaloisCohomology.valued_localUniformizer : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K),
  Valued.v ↑(Langlands.GaloisCohomology.localUniformizer v) = WithZero.exp (-1)

@Langlands.GaloisCohomology.valued_localUniformizer_zpow : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K) (k : ℤ),
  Valued.v ↑(Langlands.GaloisCohomology.localUniformizer v ^ k) = WithZero.exp (-k)

@Langlands.GaloisCohomology.ideleOrd : {K : Type u} →
  [inst : Field K] → [inst_1 : NumberField K] → Langlands.Global.FinitePlace K → Langlands.Global.Ideles K → ℤ

@Langlands.GaloisCohomology.valued_finiteIdeleProjection : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K)
  (x : Langlands.Global.Ideles K),
  Valued.v ↑((Langlands.Global.finiteIdeleProjection K v) x) = WithZero.exp (-Langlands.GaloisCohomology.ideleOrd v x)

@Langlands.GaloisCohomology.finite_setOf_ideleOrd_ne_zero : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (x : Langlands.Global.Ideles K),
  {v | Langlands.GaloisCohomology.ideleOrd v x ≠ 0}.Finite

@Langlands.GaloisCohomology.ideleOrd_diagonalUnits : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K] (v : Langlands.Global.FinitePlace K) (a : Kˣ),
  Langlands.GaloisCohomology.ideleOrd v ((Langlands.Global.diagonalUnits K) a) = Langlands.GaloisCohomology.ordAt v a

@Langlands.GaloisCohomology.sDivisorExponent : {K : Type u} →
  [inst : Field K] →
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
      Langlands.GaloisCohomology.SDivisor S → Langlands.Global.FinitePlace K → ℤ

@Langlands.GaloisCohomology.sDivisorExponent_of_notMem : ∀ {K : Type u} [inst : Field K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (D : Langlands.GaloisCohomology.SDivisor S) {v : Langlands.Global.FinitePlace K} (h : v ∉ S),
  Langlands.GaloisCohomology.sDivisorExponent S D v = D ⟨v, h⟩

@Langlands.GaloisCohomology.sDivisorExponent_of_mem : ∀ {K : Type u} [inst : Field K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (D : Langlands.GaloisCohomology.SDivisor S) {v : Langlands.Global.FinitePlace K},
  v ∈ S → Langlands.GaloisCohomology.sDivisorExponent S D v = 0

@Langlands.GaloisCohomology.sDivisorExponent_add : ∀ {K : Type u} [inst : Field K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (D₁ D₂ : Langlands.GaloisCohomology.SDivisor S) (v : Langlands.Global.FinitePlace K),
  Langlands.GaloisCohomology.sDivisorExponent S (D₁ + D₂) v =
    Langlands.GaloisCohomology.sDivisorExponent S D₁ v + Langlands.GaloisCohomology.sDivisorExponent S D₂ v

@Langlands.GaloisCohomology.sDivisorIdele : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Langlands.GaloisCohomology.SDivisor S →+ Additive (Langlands.Global.Ideles K)

@Langlands.GaloisCohomology.sDivisorIdele_single : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (v : { v // v ∉ S }) (k : ℤ),
  Additive.toMul ((Langlands.GaloisCohomology.sDivisorIdele S) fun₀ | v => k) =
    (Langlands.Global.finiteIdeleInclusion K ↑v) (Langlands.GaloisCohomology.localUniformizer ↑v) ^ k

@Langlands.GaloisCohomology.finiteIdeleProjection_sDivisorIdele : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (D : Langlands.GaloisCohomology.SDivisor S) (v : Langlands.Global.FinitePlace K),
  (Langlands.Global.finiteIdeleProjection K v) (Additive.toMul ((Langlands.GaloisCohomology.sDivisorIdele S) D)) =
    Langlands.GaloisCohomology.localUniformizer v ^ Langlands.GaloisCohomology.sDivisorExponent S D v

@Langlands.GaloisCohomology.sPlacesIdele : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        [Finite ↑S] → ((w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ) →* Langlands.Global.Ideles K

@Langlands.GaloisCohomology.finiteIdeleProjection_sPlacesIdele : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S]
  (a : (w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ) (v : Langlands.Global.FinitePlace K),
  (Langlands.Global.finiteIdeleProjection K v) ((Langlands.GaloisCohomology.sPlacesIdele S) a) =
    if h : v ∈ S then a ⟨v, h⟩ else 1

@Langlands.GaloisCohomology.sPresentation : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        [Finite ↑S] →
          ((w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ) ×
              Multiplicative (Langlands.GaloisCohomology.SDivisor S) →*
            Langlands.GaloisCohomology.SIdeleClassGroup S

@Langlands.GaloisCohomology.sPresentation_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S]
  (a : (w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ)
  (D : Multiplicative (Langlands.GaloisCohomology.SDivisor S)),
  (Langlands.GaloisCohomology.sPresentation S) (a, D) =
    (Langlands.GaloisCohomology.SIdeleClassGroup.mk S)
      ((Langlands.GaloisCohomology.sPlacesIdele S) a *
        Additive.toMul ((Langlands.GaloisCohomology.sDivisorIdele S) (Multiplicative.toAdd D)))

@Langlands.GaloisCohomology.sPresentation_apply_one_right : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S]
  (a : (w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ),
  (Langlands.GaloisCohomology.sPresentation S) (a, 1) =
    (Langlands.GaloisCohomology.SIdeleClassGroup.mk S) ((Langlands.GaloisCohomology.sPlacesIdele S) a)

@Langlands.GaloisCohomology.sPresentation_one_single : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S]
  (v : { v // v ∉ S }) (k : ℤ),
  (Langlands.GaloisCohomology.sPresentation S) (1, Multiplicative.ofAdd fun₀ | v => k) =
    (Langlands.GaloisCohomology.SIdeleClassGroup.mk S)
      ((Langlands.Global.finiteIdeleInclusion K ↑v) (Langlands.GaloisCohomology.localUniformizer ↑v ^ k))

@Langlands.GaloisCohomology.principalPresentation : {K : Type u} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        Kˣ →*
          ((w : ↑S) → (Langlands.Global.FiniteCompletion K ↑w)ˣ) ×
            Multiplicative (Langlands.GaloisCohomology.SDivisor S)

@Langlands.GaloisCohomology.principalPresentation_apply : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (x : Kˣ),
  (Langlands.GaloisCohomology.principalPresentation S) x =
    (fun w => (Langlands.Global.finiteIdeleProjection K ↑w) ((Langlands.Global.diagonalUnits K) x),
      Multiplicative.ofAdd ((Langlands.GaloisCohomology.sDivisorOf S) (Additive.ofMul x)))

@Langlands.GaloisCohomology.sPresentation_surjective : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S],
  Function.Surjective ⇑(Langlands.GaloisCohomology.sPresentation S)

@Langlands.GaloisCohomology.ker_sPresentation : ∀ {K : Type u} [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_2 : Finite ↑S],
  (Langlands.GaloisCohomology.sPresentation S).ker = (Langlands.GaloisCohomology.principalPresentation S).range
```

## Outline of the proofs

* `sPresentation_surjective`: an idèle `x` is equivalent modulo `U^S` to the idèle with its own
  components at `S` and `localUniformizer v ^ ideleOrd v x` at `v ∉ S`: the quotient has component
  `1` at `S` and valuation `1` outside `S`.
* `ker_sPresentation`: if the class of the idèle of `(a, D)` is trivial, that idèle is `x · u` with
  `x ∈ Kˣ` and `u ∈ U^S`; comparing components at `S` gives `a = (x)_S`, comparing valuations
  outside `S` gives `D = div_S(x)`. Conversely the idèle of `principalPresentation S x` is `x`
  times an element of `U^S`.

## Declarations

In the order of the file:

- `globalUniformizer` (def): An element of `K` of valuation `exp (-1)` at the finite place `v` (a choice).
- `valuation_globalUniformizer` (theorem): `globalUniformizer v` has valuation `exp (-1)` at `v`.
- `ordAt_globalUniformizer` (theorem): `globalUniformizer v` has order `1` at `v`.
- `localUniformizer` (def): The image of `globalUniformizer v` in `K_v`: a uniformizer of `K_v`.
- `valued_localUniformizer` (theorem): `localUniformizer v` is a uniformizer of `K_v`.
- `valued_localUniformizer_zpow` (theorem): The valuation of a power of `localUniformizer v`.
- `ideleOrd` (def): The order of an idèle at a finite place: minus the logarithm of the valuation of its component.
- `valued_finiteIdeleProjection` (theorem): The valuation of a component of an idèle in terms of `ideleOrd`.
- `finite_setOf_ideleOrd_ne_zero` (theorem): An idèle has order `0` at all but finitely many finite places.
- `ideleOrd_diagonalUnits` (theorem): The order of a principal idèle is the order of the element.
- `sDivisorExponent` (def): The coefficient at a finite place `v` of a divisor prime to `S`, extended by `0` on `S`.
- `sDivisorExponent_of_notMem` (theorem): The coefficient at a place outside `S`.
- `sDivisorExponent_of_mem` (theorem): The coefficient at a place of `S` is `0`.
- `sDivisorExponent_add` (theorem): `sDivisorExponent` is additive.
- `sDivisorIdele` (def): The idèle of a divisor `D` prime to `S`: the power `localUniformizer v ^ D v` at each finite place `v ∉ S`, and `1` at the places of `S` and at the archimedean places.
- `sDivisorIdele_single` (theorem): The idèle of a multiple of one place.
- `finiteIdeleProjection_sDivisorIdele` (theorem): The finite components of the idèle of a divisor.
- `sPlacesIdele` (def): The idèle with prescribed components at the places of the finite set `S`, and `1` at the other places.
- `finiteIdeleProjection_sPlacesIdele` (theorem): The finite components of `sPlacesIdele S a`.
- `sPresentation` (def): A presentation of the `S`-idèle class group for finite `S`: a family of local units at the places of `S` and a divisor `D` prime to `S` go to the class of the idèle with these components at `S` and `localUniformizer v ^ D v` at `v ∉ S`. It is surjective (`sPresentation_surjective`) and its kernel is the image of `Kˣ` under `principalPresentation` (`ker_sPresentation`).
- `sPresentation_apply` (theorem): The value of the presentation.
- `sPresentation_apply_one_right` (theorem): The presentation on the local groups at `S`.
- `sPresentation_one_single` (theorem): The presentation on a multiple of one place outside `S`.
- `principalPresentation` (def): A unit `x` of `K` goes to its components at the places of `S` and its divisor prime to `S`.
- `principalPresentation_apply` (theorem): The value of `principalPresentation S`.
- `sPresentation_surjective` (theorem): The presentation is surjective.
- `ker_sPresentation` (theorem): The kernel of the presentation is the image of `Kˣ`.

## Source and licence

Rewritten on the Library's idèle API after the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSDefs.lean`
(`localUniformizer`, `valued_localUniformizer`, `divisorIdele`, `divisorIdele_single`,
`placesIdele`, `sPresentation`, `sPresentation_apply`), `ClassFieldGSPresentation.lean`
(`valued_finiteProj`, `valued_localUniformizer_zpow`, `valued_diagonal`,
`finiteProj_placesIdele`, `divisorExponent` and its lemmas, `finiteProj_divisorIdele`,
`principalPresentation`, `sPresentation_surjective`, `ker_sPresentation`),
`MkFiniteEmbeddingGlobalUniformizer.lean` (`globalUniformizer`, `ordAt_globalUniformizer`,
`map_globalUniformizer`) and `GsRootsToUnitsCompactComparisonCup.lean` (`sPresentation_fst`). The
repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: Mathlib's idèles with the Library's
`finiteIdeleProjection` and `finiteIdeleInclusion` replace the source's `finiteProj` and
`finiteEmbedding`; the source's `ord` of an idèle is `ideleOrd`; `sDivisor` and `divS` are the
Library's `SDivisor` and `sDivisorOf`; `localUniformizer` is defined as the image of
`globalUniformizer`; the declarations are renamed (`sDivisorIdele`, `sPlacesIdele`,
`sDivisorExponent`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer, 2013), Chapter VIII, §3, p. 454 (the `S`-idèle class group) and Proposition
  (8.3.5), p. 455 (the exact sequence `0 → C_{K,S} → C_S(K) → Cl_S(K) → 0`; its proof identifies
  the cokernel of the `S`-idèles with the divisors prime to `S` modulo principal divisors, which is
  what `ker_sPresentation` records together with the local groups).
