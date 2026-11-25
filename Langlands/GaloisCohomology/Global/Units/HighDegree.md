# `H³` of the units and of the `S`-units of `K_S`

`Langlands/GaloisCohomology/Global/Units/HighDegree.lean`, namespace `Langlands.GaloisCohomology`.

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K`, `K_S ⊆ Ω` the
maximal extension unramified outside `S` (ramification at the infinite places allowed),
`G_S = Gal(K_S/K)`, `𝒪_Sˣ` the `S`-units of `K_S`, `D` the divisors of `K_S` prime to `S`
(`sDivisorModule S ι`), and `ℓ` a prime such that every finite place above `ℓ` lies in `S`.

**Theorem.**
1. (`eq_zero_of_infl_three_eq_zero`) For a closed normal subgroup `N` of a profinite group `G` and a
   smooth `G`-module `A` with `H¹(N, A) = 0` and every class of `H²(N, A)` killed by an integer prime to
   `ℓ`, inflation `H³(G/N, A^N) → H³(G, A)` is injective on classes killed by a power of `ℓ`.
2. (`unitsRestriction_maximal_eq_zero_of_primary`) Every Brauer class of `K` killed by a power of `ℓ`
   dies in `K_S`.
3. (`exists_coprime_nsmul_cohomology_two_ker_quotientMap`) Every class of
   `H²(Gal(Ω/K_S), Ωˣ)` is killed by an integer prime to `ℓ`.
4. (`eq_zero_of_cohomology_three_maximalUnits`) `H³(G_S, K_Sˣ)(ℓ) = 0`.
5. (`exists_generator_outsideLocalizationHom`) For `v ∉ S` the image of the local Galois group at `v`
   in `G_S` is topologically cyclic up to every neighbourhood of `1`.
6. (`exists_coeffMap_unitsToSDivisor_eq`) Every class of `H²(G_S, D)` killed by a power of `ℓ` is the
   divisor class of a class of `H²(G_S, K_Sˣ)`.
7. (`eq_zero_of_cohomology_three_maximalSUnits`) `H³(G_S, 𝒪_Sˣ)(ℓ) = 0`.

(7) is NSW (8.3.11) (iv) for `p = ℓ`; NSW prove it with the class formation of `S`-idèle classes, here
the divisors of `K_S` prime to `S` are used, as in the source.

Proof. (1) Dimension shifting with the coinduced module and the five-term exact sequence
(`fiveTerm_exact`, `transgression`): the class comes from `H²(G/N, ·)` of the cokernel, where its
inflation lies in the image of the transgression of `H¹(N, ·) ≅ H²(N, A)`, killed by an integer prime
to `ℓ`. (2) Only finitely many local invariants of the class are nonzero; it dies in a totally complex
finite extension inside `K_S` whose local degrees at these places are multiples of `ℓ^k`
(`Langlands.GaloisCohomology.Global.Units.ComplexRestriction`), hence in `K_S`. (3) A class of
`H²(Gal(Ω/K_S), Ωˣ)` is restricted from an open subgroup `Gal(Ω/F)` with `F ⊆ K_S`
(`exists_resOfLE_eq`); its `ℓ`-primary part dies in the maximal extension of `F` unramified outside
the places above `S`, which is `K_S` (`resOfLE_openCohomologyIso_inv_eq_zero`). (4) Inflation
`H³(G_S, K_Sˣ) → H³(Gal(Ω/K), Ωˣ) = 0` (`subsingleton_cohomology_three_unitsModule` of the module
`Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees`) with (1), Hilbert 90 and (3).
(5) The decomposition groups of an unramified place in the finite Galois levels of `K_S` are cyclic
(`isCyclic_range_decompositionHom_level`). (6) For `v ∉ S` and `r = k/ℓ^n`, a Brauer class with
invariant `r` at `v`, `−r` at a place above `ℓ` and `0` elsewhere is `ℓ`-primary and comes from
`H²(G_S, K_Sˣ)` by (2) (`exists_maximalUnits_localInvariant_single`); by the comparison of local
classes and order classes (`brauerLocalization_maximalUnitsInflation_eq_zero_iff`) these `ℓ^n`
classes have distinct components at `v`, killed by `ℓ^n`, and zero components at the other places
outside `S` (`exists_maximalUnits_component_family`). By (5) and `card_le_of_topologicallyCyclic`
there are at most `ℓ^n` such components (`card_le_sDivisor_component`), so every component of an
`ℓ^n`-torsion divisor class is attained (`mem_range_of_card_le`,
`exists_unitsToSDivisor_component_eq`); a finite sum over the support of the class gives (6), since a
class of `H²(G_S, D)` is determined by its components (`eq_zero_of_divisorEval_eq_zero`). (7) By (4) a
class of `H³(G_S, 𝒪_Sˣ)(ℓ)` is the connecting image of a class `p` of `H²(G_S, K_Sˣ/𝒪_Sˣ)`, which may be
taken `ℓ`-primary; by (6) its divisor class is that of an `ℓ`-primary class `y` of `H²(G_S, K_Sˣ)`, so
`p` minus the image of `y` lies in the kernel to `H²(G_S, D)`, which is killed by integers prime to
`ℓ` (`exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero`), and is `ℓ`-primary, hence zero; the
connecting map kills the image of `y`.

Declarations, in order: `eq_zero_of_infl_three_eq_zero`, `exists_primary_add_coprime`,
`isCyclic_range_decompositionHom_level`, `inv_mul_mem_fixingSubgroup_of_decompositionHom_eq`,
`exists_generator_outsideLocalizationHom`, `unitsRestriction_maximal_eq_zero_of_primary`,
`isClosed_ker_quotientMap`, `algebraMap_fixedField_mem`, `resOfLE_openCohomologyIso_inv_eq_zero`,
`exists_coprime_nsmul_cohomology_two_ker_quotientMap`, `eq_zero_of_cohomology_three_maximalUnits`,
`exists_natCast_mem_asIdeal`, `exists_maximalUnits_localInvariant_single`,
`compactSpace_and_totallyDisconnectedSpace_localGal`, `injective_rationalClass_div`,
`nsmul_rationalClass_div_eq_zero`, `exists_maximalUnits_component_family`, `mem_range_of_card_le`,
`card_le_sDivisor_component`, `exists_unitsToSDivisor_component_eq`,
`exists_coeffMap_unitsToSDivisor_eq`, `coeffMap_unitsModSUnitsToSDivisor_mkQ`,
`eq_zero_of_cohomology_three_maximalSUnits`.

The restriction to `ℓ`-primary parts in capitulation is removed in the module
`Langlands.GaloisCohomology.Global.Units.CapitulationPrincipalIdeal`, which imports the bridge
`Langlands.ClassFieldTheory.Global.Artin.PrincipalIdeal` to the principal ideal theorem of the NYLL copy:
for every finite level `L` of `K_S / K` there is a finite level `L' ⊇ L` in which every divisor of `L` prime
to `S` is the divisor of a unit (`exists_level_forall_unitsToSDivisor_eq`), so that, for every set `S` of
finite places and with no prime `ℓ`, the divisor map `K_Sˣ → Div_S(K_S)` is onto (`unitsToSDivisor_surjective`)
and the divisor class module is zero (`isZero_sDivisorClassModule`); `0 → 𝒪_Sˣ → K_Sˣ → D → 0` is then short
exact (`sUnitsDivisorSequence_shortExact`) and `K_Sˣ/𝒪_Sˣ → D` is an isomorphism
(`isIso_unitsModSUnitsToSDivisor`). This file does not import the copy; its last step uses that the kernel to `H²(G_S, D)` is
killed by integers prime to `ℓ`.

## Complete types

```lean
@Langlands.GaloisCohomology.eq_zero_of_infl_three_eq_zero : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  (A : Rep.{u_1, u_1, u_1} k G) [inst_6 : Langlands.IsSmoothRep A] (N : Subgroup G) [inst_7 : N.Normal],
  IsClosed ↑N →
    CategoryTheory.Limits.IsZero (Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype A) 1) →
      ∀ (ℓ : ℕ),
        (∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res N.subtype A) 2)),
            ∃ (m : ℕ), m.Coprime ℓ ∧ m • y = 0) →
          ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (A.quotientToInvariants N) 3)),
            (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.infl A N 3)) x = 0 → ∀ (j : ℕ), ℓ ^ j • x = 0 → x = 0
@Langlands.GaloisCohomology.exists_primary_add_coprime : ∀ {M : Type u_1} [inst : AddCommGroup M] {ℓ : ℕ},
  Nat.Prime ℓ →
    ∀ {y : M},
      IsOfFinAddOrder y →
        ∃ (y₁ : M) (y₂ : M), y = y₁ + y₂ ∧ (∃ (a : ℕ), ℓ ^ a • y₁ = 0) ∧ ∃ (m : ℕ), m.Coprime ℓ ∧ m • y₂ = 0
@Langlands.GaloisCohomology.isCyclic_range_decompositionHom_level : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (E : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)),
  IsCyclic
    ↥(↑(Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
            (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))).range
@Langlands.GaloisCohomology.inv_mul_mem_fixingSubgroup_of_decompositionHom_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
  (E : FiniteGaloisIntermediateField K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S))
  {h h' :
    Gal(AlgebraicClosure
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
          ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)},
  (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
        h =
      (Langlands.Galois.decompositionHom (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
          (Langlands.GaloisCohomology.levelEmbedding S ι (↑v) E.toIntermediateField))
        h' →
    ((Langlands.GaloisCohomology.outsideLocalizationHom S ι v) h)⁻¹ *
        (Langlands.GaloisCohomology.outsideLocalizationHom S ι v) h' ∈
      E.fixingSubgroup
@Langlands.GaloisCohomology.exists_generator_outsideLocalizationHom : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsGalois K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }),
  ∀ V ∈ nhds 1,
    ∃ (h₀ :
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)),
      ∀
        (h :
          Gal(AlgebraicClosure
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)),
        ∃ (k : ℤ),
          ((Langlands.GaloisCohomology.outsideLocalizationHom S ι v) (h₀ ^ k))⁻¹ *
              (Langlands.GaloisCohomology.outsideLocalizationHom S ι v) h ∈
            V
@Langlands.GaloisCohomology.unitsRestriction_maximal_eq_zero_of_primary : ∀ {K Ω : Type u_1} [inst : Field K]
  [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K Ω) 2)) {k : ℕ},
        ℓ ^ k • x = 0 →
          (ModuleCat.Hom.hom
                (Langlands.GaloisCohomology.unitsRestriction K (↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) Ω
                  2))
              x =
            0
@Langlands.GaloisCohomology.isClosed_ker_quotientMap : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  IsClosed ↑(↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker
@Langlands.GaloisCohomology.algebraMap_fixedField_mem : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (U : OpenSubgroup Gal(Ω/K)),
  (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker ≤ ↑U →
    ∀ (x : ↥(IntermediateField.fixedField ↑U)),
      (Algebra.algebraMap (↥(IntermediateField.fixedField ↑U)) Ω) x ∈ Langlands.Galois.maximalUnramifiedOutside K Ω S
@Langlands.GaloisCohomology.resOfLE_openCohomologyIso_inv_eq_zero : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (U : OpenSubgroup Gal(Ω/K))
  (hNU : (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker ≤ ↑U)
  (z :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule (↥(IntermediateField.fixedField ↑U)) Ω) 2)),
  (ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.unitsRestriction (↥(IntermediateField.fixedField ↑U))
            (↥(Langlands.Galois.maximalUnramifiedOutside (↥(IntermediateField.fixedField ↑U)) Ω
                (Langlands.Galois.finitePlacesAbove (↥(IntermediateField.fixedField ↑U)) S)))
            Ω 2))
        z =
      0 →
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.resOfLE (Langlands.GaloisCohomology.unitsModule K Ω) hNU 2))
        ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.openCohomologyIso U 2).inv) z) =
      0
@Langlands.GaloisCohomology.exists_coprime_nsmul_cohomology_two_ker_quotientMap : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀
        (y :
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Rep.res (↑(Langlands.Galois.GaloisGroupUnramifiedOutside.quotientMap K Ω S)).ker.subtype
                (Langlands.GaloisCohomology.unitsModule K Ω))
              2)),
        ∃ (m : ℕ), m.Coprime ℓ ∧ m • y = 0
@Langlands.GaloisCohomology.eq_zero_of_cohomology_three_maximalUnits : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀
        (x :
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 3))
        {k : ℕ}, ℓ ^ k • x = 0 → x = 0
@Langlands.GaloisCohomology.exists_natCast_mem_asIdeal : ∀ {K : Type u_1} [inst : Field K] [NumberField K] {ℓ : ℕ},
  Nat.Prime ℓ → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal
@Langlands.GaloisCohomology.exists_maximalUnits_localInvariant_single : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
        (r : Langlands.ClassFieldTheory.Local.RationalModIntegers) {n : ℕ},
        ℓ ^ n • r = 0 →
          ∃ (z :
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
            (Langlands.GaloisCohomology.localInvariant ι ↑v)
                  ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2) z) =
                r ∧
              ∀ w ∉ S,
                w ≠ ↑v →
                  (Langlands.GaloisCohomology.brauerLocalization ι w 2)
                      ((Langlands.GaloisCohomology.maximalUnitsInflation K Ω S 2) z) =
                    0
@Langlands.GaloisCohomology.compactSpace_and_totallyDisconnectedSpace_localGal : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  CompactSpace
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
            v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) ∧
    TotallyDisconnectedSpace
      Gal(AlgebraicClosure
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)
@Langlands.GaloisCohomology.injective_rationalClass_div : ∀ {m : ℕ},
  m ≠ 0 → Function.Injective fun (k : Fin m) => Langlands.ClassFieldTheory.Local.rationalClass (↑↑k / ↑m)
@Langlands.GaloisCohomology.nsmul_rationalClass_div_eq_zero : ∀ {m : ℕ},
  m ≠ 0 → ∀ (k : ℕ), m • Langlands.ClassFieldTheory.Local.rationalClass (↑k / ↑m) = 0
@Langlands.GaloisCohomology.exists_maximalUnits_component_family : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }) (n : ℕ),
        ∃ (z :
          Fin (ℓ ^ n) →
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
          (Function.Injective fun (k : Fin (ℓ ^ n)) =>
              (ModuleCat.Hom.hom
                  (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
                    (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                      (ULift.{u_1, 0} ℤ) v)
                    2))
                ((ModuleCat.Hom.hom
                    (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                  (z k))) ∧
            (∀ (k : Fin (ℓ ^ n)),
                ℓ ^ n •
                    (ModuleCat.Hom.hom
                        (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
                          (Langlands.GaloisCohomology.divisorEval
                            (Langlands.GaloisCohomology.outsideLocalizationHom S ι) (ULift.{u_1, 0} ℤ) v)
                          2))
                      ((ModuleCat.Hom.hom
                          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                        (z k)) =
                  0) ∧
              ∀ (k : Fin (ℓ ^ n))
                (w : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }),
                w ≠ v →
                  (ModuleCat.Hom.hom
                        (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι w)
                          (Langlands.GaloisCohomology.divisorEval
                            (Langlands.GaloisCohomology.outsideLocalizationHom S ι) (ULift.{u_1, 0} ℤ) w)
                          2))
                      ((ModuleCat.Hom.hom
                          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                        (z k)) =
                    0
@Langlands.GaloisCohomology.mem_range_of_card_le : ∀ {C : Type u_1} {m : ℕ} {Φ : Fin m → C},
  Function.Injective Φ →
    ∀ (P : C → Prop),
      (∀ (s : Finset C), (∀ c ∈ s, P c) → s.card ≤ m) →
        (∀ (k : Fin m), P (Φ k)) → ∀ {c : C}, P c → ∃ (k : Fin m), Φ k = c
@Langlands.GaloisCohomology.card_le_sDivisor_component : ∀ {K Ω : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : Field Ω] [inst_3 : Algebra K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) [inst_4 : IsGalois K Ω]
  (ι : Langlands.Galois.PlaceEmbeddings K Ω)
  (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }) {m : ℕ},
  m ≠ 0 →
    ∀
      (s :
        Finset
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.trivialModule
                Gal(AlgebraicClosure
                    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K
                      ↑v)/IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
                (ULift.{u_1, 0} ℤ))
              2)),
      (∀ c ∈ s,
          m • c = 0 ∧
            ∃ (d' :
              ↑(Langlands.ProfiniteCohomology.cohomology
                  (Langlands.GaloisCohomology.divisorModule (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                    (ULift.{u_1, 0} ℤ))
                  2)),
              (ModuleCat.Hom.hom
                    (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
                      (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                        (ULift.{u_1, 0} ℤ) v)
                      2))
                  d' =
                c) →
        s.card ≤ m
@Langlands.GaloisCohomology.exists_unitsToSDivisor_component_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (v : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S })
        (d :
          ↑(Langlands.ProfiniteCohomology.cohomology
              (Langlands.GaloisCohomology.divisorModule (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                (ULift.{u_1, 0} ℤ))
              2))
        {n : ℕ},
        ℓ ^ n • d = 0 →
          ∃ (z :
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
            (ModuleCat.Hom.hom
                    (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
                      (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                        (ULift.{u_1, 0} ℤ) v)
                      2))
                  ((ModuleCat.Hom.hom
                      (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                    z) =
                (ModuleCat.Hom.hom
                    (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι v)
                      (Langlands.GaloisCohomology.divisorEval (Langlands.GaloisCohomology.outsideLocalizationHom S ι)
                        (ULift.{u_1, 0} ℤ) v)
                      2))
                  d ∧
              ∀ (w : { v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S }),
                w ≠ v →
                  (ModuleCat.Hom.hom
                        (Langlands.ProfiniteCohomology.map (Langlands.GaloisCohomology.outsideLocalizationHom S ι w)
                          (Langlands.GaloisCohomology.divisorEval
                            (Langlands.GaloisCohomology.outsideLocalizationHom S ι) (ULift.{u_1, 0} ℤ) w)
                          2))
                      ((ModuleCat.Hom.hom
                          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                        z) =
                    0
@Langlands.GaloisCohomology.exists_coeffMap_unitsToSDivisor_eq : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (ι : Langlands.Galois.PlaceEmbeddings K Ω)
        (d : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.sDivisorModule S ι) 2)) {n : ℕ},
        ℓ ^ n • d = 0 →
          ∃ (z :
            ↑(Langlands.ProfiniteCohomology.cohomology
                (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) 2)),
            (ModuleCat.Hom.hom
                  (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) 2))
                z =
              d
@Langlands.GaloisCohomology.coeffMap_unitsModSUnitsToSDivisor_mkQ : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (ι : Langlands.Galois.PlaceEmbeddings K Ω) (n : ℕ)
  (z :
    ↑(Langlands.ProfiniteCohomology.cohomology
        (Langlands.GaloisCohomology.unitsModule K ↥(Langlands.Galois.maximalUnramifiedOutside K Ω S)) n)),
  (ModuleCat.Hom.hom
        (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsModSUnitsToSDivisor S ι) n))
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.sUnitsQuotSequence K Ω S).g n))
        z) =
    (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.unitsToSDivisor S ι) n)) z
@Langlands.GaloisCohomology.eq_zero_of_cohomology_three_maximalSUnits : ∀ {K Ω : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [inst_4 : IsSepClosure K Ω]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {ℓ : ℕ},
  Nat.Prime ℓ →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑ℓ ∈ v.asIdeal → v ∈ S) →
      ∀ (x : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.maximalSUnitsModule K Ω S) 3))
        {k : ℕ}, ℓ ^ k • x = 0 → x = 0
```

## Literature

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VIII §3, (8.3.11)
  Proposition (iv), p. 458 (`H³(G_S, 𝒪_Sˣ)(p) = 0` for `p` invertible on `S`).

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files under
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/`: `EqZeroOfCohomologyInflThreeEqZero.lean`
(lines 14–76, `eq_zero_of_cohomologyInfl_three_eq_zero`, here `eq_zero_of_infl_three_eq_zero`),
`FiniteSetOfNsmulEqZeroQZ.lean` (lines 45–110, `exists_place_above` and `exists_gsLocalRes_eq_single`,
here `exists_natCast_mem_asIdeal` and `exists_maximalUnits_localInvariant_single`, with new proofs from
the Library's Brauer sequence), `SurjectiveOfInjectiveOfInjective.lean` (lines 150–273,
`exists_sUnitsQuotDiv_gsQuotMor_eq` and `eq_zero_of_h3_sUnits_of_frob`, here
`exists_coeffMap_unitsToSDivisor_eq` and `eq_zero_of_cohomology_three_maximalSUnits`).
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the counting at a place outside `S` uses
`card_le_of_topologicallyCyclic` in place of the source's Frobenius data; `H²(Gal(Ω/K_S), Ωˣ)` is
treated through open subgroups and the Library's Brauer sequence, not through the source's limit modules
(`HighInflUnits.lean`, `exists_coprime_nsmul_cohomology_gsKernel`); `H³(Gal(Ω/K), Ωˣ) = 0` is the
Library's theorem.
