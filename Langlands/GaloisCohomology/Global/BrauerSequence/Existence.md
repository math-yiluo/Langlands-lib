# Existence of global Brauer classes with prescribed local invariants

`Langlands/GaloisCohomology/Global/BrauerSequence/Existence.lean`, namespace
`Langlands.GaloisCohomology`.

**Real invariants.** `realCocycleValue w hw z ∈ ℂ` is the image of `z(c, c) · z(1, 1)`; it is
multiplicative in `z`, nonzero and real. `realInvariant_add`: the real invariant is additive;
`realInvariantHom` is it as a homomorphism; `realInvariant_injective`;
`realBrauerGroup_eq_of_eq_zero_iff`: two local classes at an infinite place are equal when both or
neither vanish.

**Groups of order two.** `eq_of_ne_of_natCard_eq_two`, `mul_self_eq_one_of_natCard_eq_two`;
`signCharacter : G →* Multiplicative (ZMod 2)` for `|G| = 2`, injective, `1` on the nontrivial
element.

**The field `K(i)`.** `sq_ne_neg_one_of_isReal`: under a real embedding no element squares to `-1`;
`exists_sq_eq_neg_one`: `Ω` contains `i`; `finrank_adjoin_sqrt_neg_one`: if `K` has a real place,
`[K(i) : K] = 2`.

**Realization.** `exists_sign_pattern`: for every predicate `s` on the infinite places there is `α ≠ 0` in `K` whose
image at each infinite place has nonzero real part, negative exactly where `s` holds;
`exists_realBrauerLocalization_ne_zero_iff`: there is a global class whose localization at each real
place `w` is nonzero exactly when `s w`; `exists_nsmul_rationalClass_eq_zero`; `exists_localInvariant_eq`:
a finitely supported family of finite invariants with sum zero is the family of local invariants of
a global class with trivial real localizations.

**Exactness.** `existsUnique_brauerLocalization_eq'`: a family of local Brauer classes at all places,
almost all zero at the finite places, with sum of invariants zero, is the family of localizations of
exactly one global class.

## Complete types

```lean
@Langlands.GaloisCohomology.realCocycleValue : {K : Type u_1} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (w : NumberField.InfinitePlace K) →
        w.IsReal →
          ↑(Langlands.ProfiniteCohomology.cocycles
                (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2) →
            ℂ

@Langlands.GaloisCohomology.realCocycleValue_add : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (z z' :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)),
  Langlands.GaloisCohomology.realCocycleValue w hw (z + z') =
    Langlands.GaloisCohomology.realCocycleValue w hw z * Langlands.GaloisCohomology.realCocycleValue w hw z'

@Langlands.GaloisCohomology.realCocycleValue_ne_zero : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)),
  Langlands.GaloisCohomology.realCocycleValue w hw z ≠ 0

@Langlands.GaloisCohomology.realCocycleValue_im : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (z :
    ↑(Langlands.ProfiniteCohomology.cocycles
        (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2)),
  (Langlands.GaloisCohomology.realCocycleValue w hw z).im = 0

@Langlands.GaloisCohomology.realInvariant_add : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) (y y' : Langlands.GaloisCohomology.RealBrauerGroup w),
  Langlands.GaloisCohomology.realInvariant w (y + y') =
    Langlands.GaloisCohomology.realInvariant w y + Langlands.GaloisCohomology.realInvariant w y'

@Langlands.GaloisCohomology.realInvariantHom : {K : Type u_1} →
  [inst : Field K] →
    [NumberField K] →
      (w : NumberField.InfinitePlace K) →
        Langlands.GaloisCohomology.RealBrauerGroup w →+ Langlands.ClassFieldTheory.Local.RationalModIntegers

@Langlands.GaloisCohomology.realInvariantHom_apply : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (y : Langlands.GaloisCohomology.RealBrauerGroup w),
  (Langlands.GaloisCohomology.realInvariantHom w) y = Langlands.GaloisCohomology.realInvariant w y

@Langlands.GaloisCohomology.realInvariant_injective : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K), Function.Injective (Langlands.GaloisCohomology.realInvariant w)

@Langlands.GaloisCohomology.realBrauerGroup_eq_of_eq_zero_iff : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (w : NumberField.InfinitePlace K) {y y' : Langlands.GaloisCohomology.RealBrauerGroup w}, (y = 0 ↔ y' = 0) → y = y'

@Langlands.GaloisCohomology.eq_of_ne_of_natCard_eq_two : ∀ {G : Type u_1} {g h x : G},
  Nat.card G = 2 → g ≠ x → h ≠ x → g = h

@Langlands.GaloisCohomology.mul_self_eq_one_of_natCard_eq_two : ∀ {G : Type u_1} [inst : Group G],
  Nat.card G = 2 → ∀ (g : G), g * g = 1

@Langlands.GaloisCohomology.signCharacter : {G : Type u_1} →
  [inst : Group G] → Nat.card G = 2 → G →* Multiplicative (ZMod 2)

@Langlands.GaloisCohomology.signCharacter_apply_of_ne_one : ∀ {G : Type u_1} [inst : Group G] (hG : Nat.card G = 2)
  {g : G}, g ≠ 1 → (Langlands.GaloisCohomology.signCharacter hG) g = Multiplicative.ofAdd 1

@Langlands.GaloisCohomology.signCharacter_injective : ∀ {G : Type u_1} [inst : Group G] (hG : Nat.card G = 2),
  Function.Injective ⇑(Langlands.GaloisCohomology.signCharacter hG)

@Langlands.GaloisCohomology.sq_ne_neg_one_of_isReal : ∀ {L : Type u_1} [inst : Field L] {φ : L →+* ℂ},
  NumberField.ComplexEmbedding.IsReal φ → ∀ (r : L), r ^ 2 ≠ -1

@Langlands.GaloisCohomology.exists_sq_eq_neg_one : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω] [IsSepClosure K Ω] [CharZero K], ∃ (i : Ω), i ^ 2 = -1

@Langlands.GaloisCohomology.finrank_adjoin_sqrt_neg_one : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : Field Ω]
  [inst_2 : Algebra K Ω],
  (∃ (w : NumberField.InfinitePlace K), w.IsReal) → ∀ {i : Ω}, i ^ 2 = -1 → Module.finrank K ↥K⟮i⟯ = 2

@Langlands.GaloisCohomology.exists_sign_pattern : ∀ {K : Type u_1} [inst : Field K] [NumberField K]
  (s : NumberField.InfinitePlace K → Prop),
  ∃ (α : K), α ≠ 0 ∧ ∀ (w : NumberField.InfinitePlace K), ((w.embedding α).re < 0 ↔ s w) ∧ (w.embedding α).re ≠ 0

@Langlands.GaloisCohomology.exists_realBrauerLocalization_ne_zero_iff : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (s : NumberField.InfinitePlace K → Prop),
  ∃ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
    ∀ (w : NumberField.InfinitePlace K),
      w.IsReal → ((Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x ≠ 0 ↔ s w)

Langlands.GaloisCohomology.exists_nsmul_rationalClass_eq_zero : ∀
  (q : Langlands.ClassFieldTheory.Local.RationalModIntegers), ∃ (n : ℕ), n ≠ 0 ∧ n • q = 0

@Langlands.GaloisCohomology.exists_localInvariant_eq : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω] (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (α :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
      Langlands.ClassFieldTheory.Local.RationalModIntegers),
  (Function.support α).Finite →
    ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), α v = 0 →
      ∃ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)),
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.localInvariant ι v) x = α v) ∧
          ∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = 0

@Langlands.GaloisCohomology.existsUnique_brauerLocalization_eq' : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (a :
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) →
      Langlands.GaloisCohomology.LocalBrauerGroup v)
  (b : (w : NumberField.InfinitePlace K) → Langlands.GaloisCohomology.RealBrauerGroup w),
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | a v ≠ 0}.Finite →
    ∑ᶠ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.finiteInvariant v) (a v) +
          ∑ w : NumberField.InfinitePlace K, Langlands.GaloisCohomology.realInvariant w (b w) =
        0 →
      ∃! x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2),
        (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
            (Langlands.GaloisCohomology.brauerLocalization ι v 2) x = a v) ∧
          ∀ (w : NumberField.InfinitePlace K), (Langlands.GaloisCohomology.realBrauerLocalization ι w 2) x = b w
```

## Outline of the proofs

Additivity: `realInvariant_cohomologyπ` expresses the invariant as `signClass` of
`realCocycleValue`, and the Library's `signClass_mul` is additive on nonzero reals. Real components:
if `K` has a real place, `K(i)/K` is quadratic (the minimal polynomial `X² + 1` has no root in `K`),
hence Galois and cyclic (`Algebra.IsQuadraticExtension`); every real place ramifies in `K(i)`, so its
place `realPlace ι K(i) w` has a conjugation `c ≠ 1` (`exists_isConj_of_isRamified`), and the
Library's `archimedeanInvariant_cyclicClass_of_isConj` gives the archimedean invariant of the cyclic
class of `α` as `1/2` or `0` according to the sign of `α` at `w`; `realLocalInvariant_unitsInflation`
transports this to the global class, and `α` comes from weak approximation (the Library's
`exists_algebraMap_mem_open`). Finite components: choose `m` killing all prescribed invariants and a
cyclic layer `E` with local degrees divisible by `m` above their support (`exists_isCyclic_dvd_localDegree`);
`exists_relativeCohomology_of_finiteInvariants_archimedean` (the module
`Langlands.ClassFieldTheory.Global.RelativeFiniteBrauerProfiles`) gives a class at level `E` with these
invariants at the chosen places and trivial archimedean invariants; its inflation has the required
invariants by `exists_localPlace_eq`, `localInvariant_eq` and `localInvariant_unitsInflation`.
Exactness: realize the real components by `x₀`; the remaining finite invariants have sum zero by the
reciprocity law for `x₀`; realize them by `x₁`; `x₀ + x₁` works, and uniqueness is the Hasse
principle.

## Declarations

`realCocycleValue`, `realCocycleValue_add`, `realCocycleValue_ne_zero`, `realCocycleValue_im`,
`realInvariant_add`, `realInvariantHom`, `realInvariantHom_apply`, `realInvariant_injective`,
`realBrauerGroup_eq_of_eq_zero_iff`, `eq_of_ne_of_natCard_eq_two`,
`mul_self_eq_one_of_natCard_eq_two`, `signCharacter`, `signCharacter_apply_of_ne_one`,
`signCharacter_injective`, `sq_ne_neg_one_of_isReal`, `exists_sq_eq_neg_one`,
`finrank_adjoin_sqrt_neg_one`,
`exists_sign_pattern`, `exists_realBrauerLocalization_ne_zero_iff`,
`exists_nsmul_rationalClass_eq_zero`, `exists_localInvariant_eq`, `existsUnique_brauerLocalization_eq'`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`. It replaces
the source's `sumPlaceInv_eq_zero_iff` and `sumPlaceInv_surjective`
(`GlobalClassFormation/ExistsUnitsToIdelesEqOfIdelesSumInvEqZero.lean`, `LocalInvariants.lean`) by
proofs from the Library's global class field theory at finite levels.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition, corrected
  printing (Springer 2013): Theorem (8.1.17), p. 437; Proposition (8.1.9), p. 431 (the totally
  imaginary quadratic extension at the real places); Proposition (1.7.1), p. 74.
- J. Neukirch, *Algebraic Number Theory* (Springer 1999), Chapter II, (3.4) Approximation Theorem,
  p. 117.
