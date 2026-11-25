import Langlands.GaloisCohomology.Global.Units.Inflation

/-!
# The divisor sequence of `K_S` prime to `S`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places, `G_S = Gal(K_S/K)`,
`ι : PlaceEmbeddings K Ω` and `ℓ` a prime such that every place above `ℓ` lies in `S`.

* `sDivisorClassModule S ι`: the quotient `P` of the divisor module `D = sDivisorModule S ι` by the
  principal divisors (the image of `unitsToSDivisor`); it is a smooth `G_S`-module whose elements are
  killed by integers prime to `ℓ` (`exists_coprime_nsmul_sDivisorClass`, by capitulation).
* `sDivisorSequence S ι`: the short exact sequence `0 → K_Sˣ/𝒪_Sˣ → D → P → 0`.
* `exists_coprime_nsmul_cohomology_one_unitsModSUnits`: `H¹(G_S, K_Sˣ/𝒪_Sˣ)` is killed, element by
  element, by integers prime to `ℓ` (`H¹(G_S, D) = 0`); likewise the kernel of
  `H²(G_S, K_Sˣ/𝒪_Sˣ) → H²(G_S, D)` (`exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero`).
* `brauerLocalization_maximalUnitsInflation_eq_zero_iff`: for a class `z` of `H²(G_S, K_Sˣ)` and a
  place `v ∉ S`, the localization at `v` of its inflation to `H²(Gal(Ω/K), Ωˣ)` vanishes if and only
  if the component at `v` of its divisor class in `H²(G_S, D)` (a class of `H²(K_v, ℤ)`) does.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Primary

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An element killed by a power of `ℓ` and by an integer prime to `ℓ` is zero. -/
theorem eq_zero_of_coprime_nsmul_eq_zero {ℓ N k : ℕ} (hN : N.Coprime ℓ) {x : A} (h₁ : N • x = 0)
    (h₂ : ℓ ^ k • x = 0) : x = 0 := by
  have hc : Nat.gcd N (ℓ ^ k) = 1 := Nat.Coprime.pow_right k hN
  have h : addOrderOf x ∣ 1 := by
    rw [← hc]
    exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h₁) (addOrderOf_dvd_of_nsmul_eq_zero h₂)
  have h0 := addOrderOf_nsmul_eq_zero x
  rwa [Nat.dvd_one.1 h, one_nsmul] at h0

/-- If `y` has finite order and `f y` is killed by a power of the prime `ℓ`, then `f y = f y'` for an
element `y'` killed by a power of `ℓ`. -/
theorem exists_primary_map_eq (f : A →+ B) {ℓ : ℕ} (hℓ : ℓ.Prime) {y : A} (hy : IsOfFinAddOrder y)
    {k : ℕ} (hk : ℓ ^ k • f y = 0) : ∃ y' : A, (∃ j : ℕ, ℓ ^ j • y' = 0) ∧ f y' = f y := by
  obtain ⟨a, N, hN, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (addOrderOf_pos_iff.2 hy).ne' ℓ
    hℓ.ne_one
  have hcop : N.Coprime (ℓ ^ (a + k + 1)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hN))
  have hlt : 1 < ℓ ^ (a + k + 1) := Nat.one_lt_pow (by omega) hℓ.one_lt
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
  refine ⟨(N * t) • y, ⟨a, ?_⟩, ?_⟩
  · rw [smul_smul, show ℓ ^ a * (N * t) = t * (ℓ ^ a * N) by ring, ← smul_smul, ← hn,
      addOrderOf_nsmul_eq_zero, smul_zero]
  · have hfy : ℓ ^ (a + k + 1) • f y = 0 := by
      rw [show a + k + 1 = (a + 1) + k by omega, pow_add, ← smul_smul, hk, smul_zero]
    have e := Nat.div_add_mod (N * t) (ℓ ^ (a + k + 1))
    rw [ht] at e
    rw [map_nsmul, ← e, add_nsmul, mul_comm (ℓ ^ (a + k + 1)), ← smul_smul, hfy, smul_zero,
      zero_add, one_nsmul]

end Primary

section Picard

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- The principal divisors (prime to `S`) of `K_S`: the image of the divisor map. -/
def sPrincipalDivisors : Submodule (ULift.{u} ℤ) (sDivisorModule S ι) :=
  LinearMap.range (unitsToSDivisor S ι).hom.toLinearMap

theorem mem_sPrincipalDivisors_iff (f : sDivisorModule S ι) :
    f ∈ sPrincipalDivisors S ι ↔ ∃ y, (unitsToSDivisor S ι).hom y = f :=
  Iff.rfl

theorem sPrincipalDivisors_le_comap (g : GaloisGroupUnramifiedOutside K Ω S) :
    sPrincipalDivisors S ι ≤ (sPrincipalDivisors S ι).comap ((sDivisorModule S ι).ρ g) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨(unitsModule K (maximalUnramifiedOutside K Ω S)).ρ g y, Rep.hom_comm_apply _ g y⟩

/-- The `G_S`-module `P` of divisor classes of `K_S` prime to `S`. -/
abbrev sDivisorClassModule : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S) :=
  (sDivisorModule S ι).quotient (sPrincipalDivisors S ι) (sPrincipalDivisors_le_comap S ι)

theorem sUnitsSubmodule_le_ker :
    sUnitsSubmodule K Ω S ≤ LinearMap.ker (unitsToSDivisor S ι).hom.toLinearMap := by
  intro x hx
  exact (unitsToSDivisor_eq_zero_iff S ι (Additive.toMul x)).2 hx

/-- The divisor map on `K_Sˣ/𝒪_Sˣ`. -/
def unitsModSUnitsToSDivisor : unitsModSUnitsModule K Ω S ⟶ sDivisorModule S ι :=
  Rep.ofHom ⟨(sUnitsSubmodule K Ω S).liftQ (unitsToSDivisor S ι).hom.toLinearMap
    (sUnitsSubmodule_le_ker S ι), fun g => by
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H a => exact Rep.hom_comm_apply (unitsToSDivisor S ι) g a⟩

theorem unitsModSUnitsToSDivisor_mk (a : unitsModule K (maximalUnramifiedOutside K Ω S)) :
    (unitsModSUnitsToSDivisor S ι).hom (Submodule.Quotient.mk a) = (unitsToSDivisor S ι).hom a :=
  rfl

/-- `0 → K_Sˣ/𝒪_Sˣ → D → P → 0`. -/
def sDivisorSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) :=
  ShortComplex.mk (unitsModSUnitsToSDivisor S ι)
    (Rep.mkQ _ (sPrincipalDivisors S ι) (sPrincipalDivisors_le_comap S ι)) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H a => exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)

theorem sDivisorSequence_shortExact : (sDivisorSequence S ι).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro f hf
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hf
    exact ⟨Submodule.Quotient.mk y, hy⟩
  mono_f := by
    refine (Rep.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      exact (Submodule.Quotient.mk_eq_zero _).2
        ((unitsToSDivisor_eq_zero_iff S ι (Additive.toMul a)).1 hx)
  epi_g := (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

instance isSmoothRep_sDivisorClassModule : IsSmoothRep (sDivisorClassModule S ι) :=
  isSmoothRep_quotient _ _ _

instance isSmoothRep_sDivisorSequence_X₁ :
    IsSmoothRep (sDivisorSequence S ι).X₁ :=
  inferInstanceAs (IsSmoothRep (unitsModSUnitsModule K Ω S))

instance isSmoothRep_sDivisorSequence_X₂ :
    IsSmoothRep (sDivisorSequence S ι).X₂ :=
  inferInstanceAs (IsSmoothRep (sDivisorModule S ι))

instance isSmoothRep_sDivisorSequence_X₃ :
    IsSmoothRep (sDivisorSequence S ι).X₃ :=
  inferInstanceAs (IsSmoothRep (sDivisorClassModule S ι))

end Picard

section PicardPrime

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- Every divisor class of `K_S` prime to `S` is killed by an integer prime to `ℓ`. -/
theorem exists_coprime_nsmul_sDivisorClass (p : sDivisorClassModule S ι) :
    ∃ N : ℕ, N.Coprime ℓ ∧ N • p = 0 := by
  induction p using Submodule.Quotient.induction_on with
  | H f =>
    have : IsSepClosed Ω := IsSepClosure.sep_closed K
    obtain ⟨N, hN, y, hy⟩ := exists_coprime_nsmul_eq_unitsToSDivisor S ι hℓ hS f
    refine ⟨N, hN, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨Additive.ofMul y, hy⟩

include hℓ hS in
/-- `H¹(G_S, K_Sˣ/𝒪_Sˣ)` is killed, element by element, by integers prime to `ℓ`. -/
theorem exists_coprime_nsmul_cohomology_one_unitsModSUnits
    (x : cohomology (unitsModSUnitsModule K Ω S) 1) : ∃ N : ℕ, N.Coprime ℓ ∧ N • x = 0 := by
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  have hS' := sDivisorSequence_shortExact S ι
  have h1 : (coeffMap (unitsModSUnitsToSDivisor S ι) 1).hom x = 0 :=
    (ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_one_divisorModule_int (outsideLocalizationHom S ι))).elim _ _
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS' 0 1 rfl) x h1
  obtain ⟨N, hN, hNp⟩ := exists_coprime_nsmul_cohomology_eq_zero (sDivisorClassModule S ι) ℓ
    (exists_coprime_nsmul_sDivisorClass S ι hℓ hS) 0 p
  have hp' : (δ hS' 0 1 rfl).hom p = x := hp
  refine ⟨N, hN, ?_⟩
  rw [← hp']
  exact (map_nsmul (δ hS' 0 1 rfl).hom N p).symm.trans (by rw [show N • p = 0 from hNp, map_zero]; rfl)

include hℓ hS in
/-- The kernel of `H²(G_S, K_Sˣ/𝒪_Sˣ) → H²(G_S, D)` is killed, element by element, by integers prime
to `ℓ`. -/
theorem exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero
    (x : cohomology (unitsModSUnitsModule K Ω S) 2)
    (hx : (coeffMap (unitsModSUnitsToSDivisor S ι) 2).hom x = 0) :
    ∃ N : ℕ, N.Coprime ℓ ∧ N • x = 0 := by
  have hS' := sDivisorSequence_shortExact S ι
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS' 1 2 rfl) x hx
  obtain ⟨N, hN, hNp⟩ := exists_coprime_nsmul_cohomology_eq_zero (sDivisorClassModule S ι) ℓ
    (exists_coprime_nsmul_sDivisorClass S ι hℓ hS) 1 p
  have hp' : (δ hS' 1 2 rfl).hom p = x := hp
  refine ⟨N, hN, ?_⟩
  rw [← hp']
  exact (map_nsmul (δ hS' 1 2 rfl).hom N p).symm.trans (by rw [show N • p = 0 from hNp, map_zero]; rfl)

end PicardPrime

section Compose

variable {k G H L : Type u} [CommRing k] [Group G] [Group H] [Group L] [TopologicalSpace G]
  [TopologicalSpace H] [TopologicalSpace L] [IsTopologicalGroup G] [IsTopologicalGroup H]
  [IsTopologicalGroup L] {A : Rep.{u} k G} {B : Rep.{u} k H} {C : Rep.{u} k L} [IsSmoothRep A]
  [IsSmoothRep B] [IsSmoothRep C]

/-- `map_comp`, applied to an element. -/
theorem map_map_apply (φ : H →ₜ* G) (f : Rep.res (φ : H →* G) A ⟶ B) (ψ : L →ₜ* H)
    (g : Rep.res (ψ : L →* H) B ⟶ C) (n : ℕ) (x : cohomology A n) :
    (map ψ g n).hom ((map φ f n).hom x) =
      (map (φ.comp ψ) ((Rep.resFunctor (ψ : L →* H)).map f ≫ g) n).hom x := by
  rw [map_comp]
  rfl

/-- A coefficient map followed by a map along `φ`, applied to an element. -/
theorem map_coeffMap_hom_apply (φ : H →ₜ* G) {A' : Rep.{u} k G} [IsSmoothRep A'] (f : A ⟶ A')
    (g : Rep.res (φ : H →* G) A' ⟶ B) (n : ℕ) (x : cohomology A n) :
    (map φ g n).hom ((coeffMap f n).hom x) =
      (map φ ((Rep.resFunctor (φ : H →* G)).map f ≫ g) n).hom x := by
  have h := map_comp (ContinuousMonoidHom.id G) f φ g n
  have h' := ProfiniteCohomology.map_congr (A := A) (B := B)
    (φ := (ContinuousMonoidHom.id G).comp φ) (ψ := φ)
    ((Rep.resFunctor (φ : H →* G)).map f ≫ g) ((Rep.resFunctor (φ : H →* G)).map f ≫ g)
    (by ext; rfl) (fun _ => rfl) n
  exact (congrArg (fun F => F.hom x) h).symm.trans (congrArg (fun F => F.hom x) h')

end Compose

section LocalOrderClass

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

variable {S} in
/-- At `v ∉ S`, `sOrder` of a unit of a finite subextension `L` of `K_S` is its exponent at the
place of `ι` in `L`. -/
theorem sOrder_units_map {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (L : IntermediateField K (maximalUnramifiedOutside K Ω S)) [FiniteDimensional K L] (x : Lˣ) :
    haveI := NumberField.of_module_finite K L
    sOrder S ι v (Units.map L.val.toRingHom.toMonoidHom x) =
      placeExponent v (levelEmbedding S ι v L) x := by
  have hmem : ((Units.map L.val.toRingHom.toMonoidHom x : (maximalUnramifiedOutside K Ω S)ˣ) :
      maximalUnramifiedOutside K Ω S) ∈ L := (x : L).2
  have e := sOrder_eq ι hv _ hmem
  have e' : levelUnit _ hmem = x := Units.ext rfl
  rw [e'] at e
  exact e

variable (E : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
  (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})

/-- The restriction `G_S → Gal(E/K)` composed with the localization at `v` is the decomposition
homomorphism of the embedding of `E` given by `ι`. -/
theorem normalKrullRestriction_localizationHom
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K)) :
    BrauerComparison.normalKrullRestriction K E.toIntermediateField (maximalUnramifiedOutside K Ω S)
      (localizationHom ι S v.1 σ) =
        decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField) σ :=
  levelRestrict_localizationHom S ι v.1 E σ

/-- The localization at `v` of the inflation of a class of a finite level `E` of `K_S`. -/
theorem brauerLocalization_maximalUnitsInflation_unitsTowerMap
    (b : cohomology (unitsModule K E.toIntermediateField) 2) :
    haveI := NumberField.of_module_finite K E.toIntermediateField
    brauerLocalization ι v.1 2 (maximalUnitsInflation K Ω S 2
      ((unitsTowerMap K E.toIntermediateField (maximalUnramifiedOutside K Ω S) 2).hom b)) =
      (map (decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField))
        (localUnitsHomOf v.1 (levelEmbedding S ι v.1 E.toIntermediateField)) 2).hom b := by
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K _
  let nK := BrauerComparison.normalKrullRestriction K E.toIntermediateField
    (maximalUnramifiedOutside K Ω S)
  let fE : Rep.res (nK : _ →* _) (unitsModule K E.toIntermediateField) ⟶
      unitsModule K (maximalUnramifiedOutside K Ω S) :=
    underlyingHom nK (BrauerComparison.continuousUnitInflationCoefficients K
      E.toIntermediateField (maximalUnramifiedOutside K Ω S))
  have e1 := map_comp (GaloisGroupUnramifiedOutside.quotientMap K Ω S) (maximalUnitsHom K Ω S)
    (decompositionHom (v.1.adicCompletion K) (ι.finite v.1)) (unitsLocalHom ι v.1) 2
  have e2 := map_comp nK fE ((GaloisGroupUnramifiedOutside.quotientMap K Ω S).comp
    (decompositionHom (v.1.adicCompletion K) (ι.finite v.1)))
    ((Rep.resFunctor (decompositionHom (v.1.adicCompletion K) (ι.finite v.1) :
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →* Gal(Ω/K))).map
        (maximalUnitsHom K Ω S) ≫ unitsLocalHom ι v.1) 2
  refine (congrArg (fun F => F.hom ((map nK fE 2).hom b)) e1).symm.trans ?_
  refine (congrArg (fun F => F.hom b) e2).symm.trans ?_
  refine congrArg (fun F => F.hom b) (ProfiniteCohomology.map_congr _
    (localUnitsHomOf v.1 (levelEmbedding S ι v.1 E.toIntermediateField)) ?_ (fun x => ?_) 2)
  · ext σ : 1
    exact (congrArg nK (localizationHom_eq_quotientMap ι S v.1 σ).symm).trans
      (normalKrullRestriction_localizationHom S ι E v σ)
  · exact Additive.toMul.injective (Units.ext rfl)

/-- The component at `v` of the divisor class of the inflation of a class of a finite level `E` of
`K_S`. -/
theorem map_divisorEval_unitsToSDivisor_unitsTowerMap
    (b : cohomology (unitsModule K E.toIntermediateField) 2) :
    haveI := NumberField.of_module_finite K E.toIntermediateField
    (map (outsideLocalizationHom S ι v)
      (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
        ((coeffMap (unitsToSDivisor S ι) 2).hom
          ((unitsTowerMap K E.toIntermediateField (maximalUnramifiedOutside K Ω S) 2).hom b)) =
      (map (decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField))
        (localExponentHom v.1 (levelEmbedding S ι v.1 E.toIntermediateField)) 2).hom b := by
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K _
  let nK := BrauerComparison.normalKrullRestriction K E.toIntermediateField
    (maximalUnramifiedOutside K Ω S)
  let fE : Rep.res (nK : _ →* _) (unitsModule K E.toIntermediateField) ⟶
      unitsModule K (maximalUnramifiedOutside K Ω S) :=
    underlyingHom nK (BrauerComparison.continuousUnitInflationCoefficients K
      E.toIntermediateField (maximalUnramifiedOutside K Ω S))
  refine (map_coeffMap_hom_apply (outsideLocalizationHom S ι v) (unitsToSDivisor S ι)
    (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2 ((map nK fE 2).hom b)).trans ?_
  have e2 := map_comp nK fE (outsideLocalizationHom S ι v)
    ((Rep.resFunctor (outsideLocalizationHom S ι v :
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
        GaloisGroupUnramifiedOutside K Ω S)).map (unitsToSDivisor S ι) ≫
      divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2
  refine (congrArg (fun F => F.hom b) e2).symm.trans ?_
  refine congrArg (fun F => F.hom b) (ProfiniteCohomology.map_congr _
    (localExponentHom v.1 (levelEmbedding S ι v.1 E.toIntermediateField)) ?_ (fun x => ?_) 2)
  · ext σ : 1
    exact normalKrullRestriction_localizationHom S ι E v σ
  · show ULift.up (sOrder S ι v.1 (galUnitsHom K _ 1 (Units.map
      E.toIntermediateField.val.toRingHom.toMonoidHom (Additive.toMul x)))) =
        ULift.up (placeExponent v.1 (levelEmbedding S ι v.1 E.toIntermediateField)
          (Additive.toMul x))
    rw [map_one]
    exact congrArg ULift.up (sOrder_units_map ι v.2 E.toIntermediateField (Additive.toMul x))

/-- **Local class and order class over `G_S`.** For a class `z` of `H²(G_S, K_Sˣ)` and a place
`v ∉ S`, the localization at `v` of the inflation of `z` vanishes if and only if the component at `v`
of the divisor class of `z` (a class of `H²(K_v, ℤ)`) vanishes. -/
theorem brauerLocalization_maximalUnitsInflation_eq_zero_iff
    (z : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2) :
    brauerLocalization ι v.1 2 (maximalUnitsInflation K Ω S 2 z) = 0 ↔
      (map (outsideLocalizationHom S ι v)
        (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom z) = 0 := by
  obtain ⟨E, a, rfl⟩ := exists_unitsInflation_eq 2 z
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K _
  rw [unitsInflation_apply_eq, brauerLocalization_maximalUnitsInflation_unitsTowerMap,
    map_divisorEval_unitsToSDivisor_unitsTowerMap]
  have hu := isUnramifiedIn_of_maximalUnramifiedOutside S E.toIntermediateField v.2
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hu
  exact map_localUnitsHomOf_eq_zero_iff v.1 _ (hu _ (placeOfAlgHom _).2) _

end LocalOrderClass

end

end Langlands.GaloisCohomology
