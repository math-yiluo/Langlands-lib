# Local cohomology in degrees `≥ 3` at a finite level, and `H³` of the idèles

`Langlands/GaloisCohomology/Global/BrauerSequence/HigherDegrees/LocalVanishing.lean`, namespace
`Langlands.GaloisCohomology`.

**Finite places.** Let `I` be an invariant family of the Library forming a relative class formation
(`I.RelativeClassFormation`, with `I.FundamentalClasses`), `F` a `p`-adic field and `L / F` finite
Galois.

* `exists_relativeOrdinaryCup_eq`: every class of `Hⁿ⁺²(Gal(L/F), Lˣ)`, `n ≥ 1`, is the ordinary cup
  product `u ∪ x` of a fundamental class `u` with a class `x ∈ Hⁿ(Gal(L/F), ℤ)`;
* `exists_isFundamentalClass`: a fundamental class exists;
* `subsingleton_relativeCohomology_three`: `H³(Gal(L/F), Lˣ) = 0`;
* `relativeInflationLinear_eq_zero_of_dvd`: for a Galois extension `M ⊇ L` of `F` with
  `[L : F] ∣ [M : L]`, inflation `Hⁿ⁺²(Gal(L/F), Lˣ) → Hⁿ⁺²(Gal(M/F), Mˣ)` is zero for `n ≥ 1`.

**Infinite places.** For an infinite place `w` of a Galois extension `E / F` with stabilizer `D_w`:
`extensionEmbedding_infiniteLocalRepresentation_of_isConj`: a conjugation of `w` acts on `E_wˣ` by
complex conjugation; `exists_star_eq_mul_of_mul_star_eq_one`: Hilbert 90 for `ℂ / ℝ` on numbers;
`isZero_H1_infiniteLocalRepresentation`: `H¹(D_w, E_wˣ) = 0`; `isCyclic_stabilizer_infinitePlace`:
`D_w` is cyclic; `isZero_groupCohomology_infiniteLocalRepresentation_odd`: the cohomology of `E_wˣ`
vanishes in odd degrees.

**Idèles.** `subsingleton_relativeCohomology_three_adicCompletion`: `H³(Gal(E_w/F_v), E_wˣ) = 0` at a
finite place; `subsingleton_relativeIdeleCohomology_three`: **`H³(Gal(E/F), J_E) = 0`**.

## Complete types

```lean
@Langlands.GaloisCohomology.exists_relativeOrdinaryCup_eq : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)]
  (I : Langlands.ClassFieldTheory.Local.InvariantFamily p),
  I.RelativeClassFormation →
    ∀ (F : Langlands.PadicField p) (L : Type u_1) [inst_1 : Field L] [inst_2 : Algebra F.Carrier L]
      [inst_3 : FiniteDimensional F.Carrier L] [inst_4 : IsGalois F.Carrier L]
      (c : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F.Carrier L 2)),
      Langlands.ClassFieldTheory.Local.IsFundamentalClass F.Carrier L (I.relative F L) c →
        ∀ (n : ℕ) [NeZero n] (y : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F.Carrier L (n + 2))),
          ∃ (x : ↑(Langlands.ClassFieldTheory.Local.integralCohomology F.Carrier L n)),
            y = (Langlands.ClassFieldTheory.Local.relativeOrdinaryCup F.Carrier L n c) x
@Langlands.GaloisCohomology.exists_isFundamentalClass : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)]
  (I : Langlands.ClassFieldTheory.Local.InvariantFamily p) (F : Langlands.PadicField p) (L : Type u_1)
  [inst_1 : Field L] [inst_2 : Algebra F.Carrier L] [inst_3 : FiniteDimensional F.Carrier L]
  [inst_4 : IsGalois F.Carrier L],
  I.FundamentalClasses →
    ∃ (c : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F.Carrier L 2)),
      Langlands.ClassFieldTheory.Local.IsFundamentalClass F.Carrier L (I.relative F L) c
@Langlands.GaloisCohomology.subsingleton_relativeCohomology_three : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)]
  (I : Langlands.ClassFieldTheory.Local.InvariantFamily p),
  I.RelativeClassFormation →
    ∀ (F : Langlands.PadicField p) (L : Type u_1) [inst_1 : Field L] [inst_2 : Algebra F.Carrier L]
      [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L],
      I.FundamentalClasses → Subsingleton ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F.Carrier L 3)
@Langlands.GaloisCohomology.relativeInflationLinear_eq_zero_of_dvd : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)]
  (I : Langlands.ClassFieldTheory.Local.InvariantFamily p),
  I.RelativeClassFormation →
    ∀ (F : Langlands.PadicField p) (L : Type u_1) [inst_1 : Field L] [inst_2 : Algebra F.Carrier L]
      [FiniteDimensional F.Carrier L] [inst_4 : IsGalois F.Carrier L],
      I.FundamentalClasses →
        ∀ (M : Type u_1) [inst_5 : Field M] [inst_6 : Algebra F.Carrier M] [inst_7 : Algebra L M]
          [inst_8 : IsScalarTower F.Carrier L M] [FiniteDimensional F.Carrier M] [IsGalois F.Carrier M],
          Module.finrank F.Carrier L ∣ Module.finrank L M →
            ∀ (n : ℕ) [NeZero n] (y : ↑(Langlands.ClassFieldTheory.Local.relativeCohomology F.Carrier L (n + 2))),
              (Langlands.ClassFieldTheory.Local.relativeInflationLinear F.Carrier L M (n + 2)) y = 0
@Langlands.GaloisCohomology.extensionEmbedding_infiniteLocalRepresentation_of_isConj : ∀ {F E : Type u_1}
  [inst : Field F] [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E)
  (c : ↥(MulAction.stabilizer Gal(E/F) w)),
  NumberField.ComplexEmbedding.IsConj w.embedding ↑c →
    ∀ (a : ↑(Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w)),
      (NumberField.InfinitePlace.Completion.extensionEmbedding w)
          ↑(Additive.toMul (((Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w).ρ c) a)) =
        star ((NumberField.InfinitePlace.Completion.extensionEmbedding w) ↑(Additive.toMul a))
Langlands.GaloisCohomology.exists_star_eq_mul_of_mul_star_eq_one : ∀ (ζ : ℂ),
  star ζ * ζ = 1 → ∃ (η : ℂ), η ≠ 0 ∧ star η = ζ * η
@Langlands.GaloisCohomology.isZero_H1_infiniteLocalRepresentation : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E),
  CategoryTheory.Limits.IsZero (groupCohomology (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w) 1)
@Langlands.GaloisCohomology.isCyclic_stabilizer_infinitePlace : ∀ {F E : Type u_1} [inst : Field F] [inst_1 : Field E]
  [inst_2 : Algebra F E] (w : NumberField.InfinitePlace E), IsCyclic ↥(MulAction.stabilizer Gal(E/F) w)
@Langlands.GaloisCohomology.isZero_groupCohomology_infiniteLocalRepresentation_odd : ∀ {F E : Type u_1} [inst : Field F]
  [inst_1 : Field E] [inst_2 : NumberField E] [inst_3 : Algebra F E] (w : NumberField.InfinitePlace E) [Finite Gal(E/F)]
  (n : ℕ),
  Odd n →
    CategoryTheory.Limits.IsZero (groupCohomology (Langlands.ClassFieldTheory.Global.infiniteLocalRepresentation F w) n)
Langlands.GaloisCohomology.subsingleton_relativeCohomology_three_adicCompletion : ∀ (F E : Type u_1) [inst : Field F]
  [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
  (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) [inst_6 : w.asIdeal.LiesOver v.asIdeal],
  Subsingleton
    ↑(Langlands.ClassFieldTheory.Local.relativeCohomology (Langlands.Global.CompletionPadic.padicField v).Carrier
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E w) 3)
Langlands.GaloisCohomology.subsingleton_relativeIdeleCohomology_three : ∀ (F E : Type u_1) [inst : Field F]
  [NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] [IsGalois F E],
  Subsingleton ↑(Langlands.ClassFieldTheory.Global.relativeIdeleCohomology F E 3)
```

## Outline of the proofs

Local Tate–Nakayama: the Library's `classFormationTateIsomorphisms` (from `tateCupIsomorphism`) makes
cup product with a fundamental class bijective on Tate cohomology in every degree; in positive degree
Tate and ordinary cohomology agree and the Tate cup is the ordinary cup
(`relativeTateToOrdinary_relativeTateCup`). In degree three `x ∈ H¹(Gal(L/F), ℤ) = 0`
(`isZero_H1_trivial_integers`). For inflation, the Library's `ordinaryInflation_of_relativeClassFormation`
gives `infl(u_L ∪ x) = [M : L] · (u_M ∪ infl x)`, and `[L : F] · x = 0` in positive degree
(`card_smul_groupCohomology`). At an infinite place, either `D_w` is trivial, or it is `{1, c}` with
`c` a complex conjugation of `w`, `w` complex and `E_w ≅ ℂ`; a 1-cocycle `f` satisfies
`f(c) · c(f(c)) = 1`, and an explicit `η` with `η̄ / η = f(c)` gives a primitive (Mathlib's
`InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex`). Odd degrees follow by
periodicity. `H³(J_E) = 0` is `eq_zero_of_ideleLocalMap_eq_zero` with these local vanishings.

## Declarations

`exists_relativeOrdinaryCup_eq`, `exists_isFundamentalClass`, `subsingleton_relativeCohomology_three`, `relativeInflationLinear_eq_zero_of_dvd`, `extensionEmbedding_infiniteLocalRepresentation_of_isConj`, `exists_star_eq_mul_of_mul_star_eq_one`, `isZero_H1_infiniteLocalRepresentation`, `isCyclic_stabilizer_infinitePlace`, `isZero_groupCohomology_infiniteLocalRepresentation_odd`, `subsingleton_relativeCohomology_three_adicCompletion`, `subsingleton_relativeIdeleCohomology_three`.

## Source and licence

New file; it contains no text of the repository `leanprover-community/riemann-hypothesis`.

## References

- J.-P. Serre, *Local Class Field Theory*, in J. W. S. Cassels, A. Fröhlich (eds.), *Algebraic Number
  Theory* (Academic Press 1967), Chapter VI, §2.1, Theorem 1, p. 139 (`α ↦ α · u_{L/K}` is an
  isomorphism `Ĥ^q(G, ℤ) → Ĥ^{q+2}(G, Lˣ)`).
- J. T. Tate, *Global Class Field Theory*, ibid., Chapter VII, §7, Proposition 7.3, p. 177.
