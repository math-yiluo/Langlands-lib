import Langlands.GaloisCohomology.Global.Localization
import Langlands.GaloisCohomology.Local.Invariant
import Langlands.Global.FiniteCompletionLocalField
import Langlands.Global.AdelicFunctoriality.Extension

/-!
# The fundamental exact sequence of the Brauer group of a number field: statement

Let `K` be a number field, `Ω` a separable closure of `K` and `ι : PlaceEmbeddings K Ω` a choice of
embeddings of `Ω` into algebraic closures of the completions. The Brauer group of `K` is
`H²(Gal(Ω/K), Ωˣ)` in the cochain model of the foundations. This file defines its localizations
`brauerLocalization ι v` at the finite places and `realBrauerLocalization ι w` at the infinite places
(restriction along the decomposition homomorphisms of `ι`, with coefficients `Ωˣ → K̄_vˣ` given by
`ι`), the local invariants (`finiteInvariant`, the local theory's invariant of `K_v`;
`realInvariant`, `1/2` on a nonzero class of a real place), and states, as one structure
`BrauerSequenceData K Ω ι`, the results of global class field theory in cohomological form,
numbered here (I1) to (I4):

* (I1) a class is determined by its localizations; only finitely many finite localizations are
  nonzero; the sum of all local invariants is zero; a family of local classes with finite support
  and sum of invariants zero comes from a unique global class;
* (I2) `H³(Gal(Ω/K), Ωˣ) = 0`, and in degrees `r ≥ 4` the localization to the real places is an
  isomorphism;
* (I3) a class killed by `m` with trivial real invariants dies in every finite extension `E ⊆ Ω`
  whose local degrees at the places where the class is nonzero are multiples of `m`;
* (I4) for a finite set `T` of finite places and `m ≠ 0` there is a finite cyclic extension of `K`
  in `Ω` whose local degrees above `T` are multiples of `m`.

`BrauerSequenceStatement` asserts the data for every number field, closure and choice of
embeddings. The theorems at the end are stated from `BrauerSequenceData`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.ClassFieldTheory.Local
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section LocalInvariants

variable {K : Type u} [Field K] [NumberField K]

/-- The completion `K_v` at a finite place has characteristic zero. -/
instance charZero_adicCompletion' (v : HeightOneSpectrum (𝓞 K)) : CharZero (v.adicCompletion K) :=
  charZero_adicCompletion v

/-- The completion `K_w` at an infinite place has characteristic zero. -/
instance charZero_infinitePlaceCompletion (w : InfinitePlace K) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap K w.Completion).injective

/-- The local Brauer group `H²(Gal(K̄_v/K_v), K̄_vˣ)` at a finite place `v`. -/
abbrev LocalBrauerGroup (v : HeightOneSpectrum (𝓞 K)) : Type u :=
  cohomology (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) 2

/-- The local Brauer group `H²(Gal(K̄_w/K_w), K̄_wˣ)` at an infinite place `w`. -/
abbrev RealBrauerGroup (w : InfinitePlace K) : Type u :=
  cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) 2

/-- The invariant `H²(K_v, K̄_vˣ) ≃ ℚ/ℤ` at a finite place: the local theory's `Local.invariant` of
the completion with its own topology and valuation (`FiniteCompletion.valuativeRel`). -/
def finiteInvariant (v : HeightOneSpectrum (𝓞 K)) : LocalBrauerGroup v ≃+ RationalModIntegers :=
  letI := Langlands.Global.FiniteCompletion.valuativeRel v
  letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  Local.invariant (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))

open Classical in
/-- The invariant at an infinite place: `1/2` on a nonzero class, `0` on the zero class. (The group
has at most two elements; it is zero at a complex place.) -/
def realInvariant (w : InfinitePlace K) (y : RealBrauerGroup w) : RationalModIntegers :=
  if y = 0 then 0 else rationalClass (1 / 2)

omit [NumberField K] in
/-- The real invariant of the zero class is zero. -/
theorem realInvariant_zero (w : InfinitePlace K) : realInvariant w 0 = 0 := by
  simp [realInvariant]

omit [NumberField K] in
/-- The real invariant vanishes exactly on the zero class. -/
theorem realInvariant_eq_zero_iff (w : InfinitePlace K) (y : RealBrauerGroup w) :
    realInvariant w y = 0 ↔ y = 0 := by
  classical
  unfold realInvariant
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    intro h0
    have h1 : (1 / 2 : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ) :=
      (QuotientAddGroup.eq_zero_iff _).1 h0
    obtain ⟨n, hn⟩ := h1
    have : (n : ℚ) = 1 / 2 := by simpa using hn
    have h2 : (2 * n : ℚ) = 1 := by rw [this]; norm_num
    have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
    omega

end LocalInvariants

section Localization

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- The coefficient map `Ωˣ → K̄_vˣ` of `ι` at a finite place, as a morphism of modules of
`Gal(K̄_v/K_v)`. -/
def unitsLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    Rep.res (decompositionHom (v.adicCompletion K) (ι.finite v) :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →* Gal(Ω/K))
      (unitsModule K Ω) ⟶
      unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (Units.map (ι.finite v : Ω →* AlgebraicClosure (v.adicCompletion K)))) :
      Additive Ωˣ →ₗ[ULift.{u} ℤ] Additive (AlgebraicClosure (v.adicCompletion K))ˣ), fun σ => by
    ext x
    exact Units.ext (decompositionHom_apply (ι.finite v) σ
      ((Additive.toMul (show Additive Ωˣ from x) : Ωˣ) : Ω))⟩

/-- `unitsLocalHom` is `ι.finite v` on units. -/
theorem unitsLocalHom_hom_apply (v : HeightOneSpectrum (𝓞 K)) (x : Additive Ωˣ) :
    (((Additive.toMul ((unitsLocalHom ι v).hom x) : (AlgebraicClosure (v.adicCompletion K))ˣ)) :
      AlgebraicClosure (v.adicCompletion K)) = ι.finite v ((Additive.toMul x : Ωˣ) : Ω) :=
  rfl

/-- The coefficient map `Ωˣ → K̄_wˣ` of `ι` at an infinite place. -/
def realUnitsLocalHom (w : InfinitePlace K) :
    Rep.res (decompositionHom w.Completion (ι.infinite w) :
        Gal(AlgebraicClosure w.Completion/w.Completion) →* Gal(Ω/K))
      (unitsModule K Ω) ⟶ unitsModule w.Completion (AlgebraicClosure w.Completion) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (Units.map (ι.infinite w : Ω →* AlgebraicClosure w.Completion))) :
      Additive Ωˣ →ₗ[ULift.{u} ℤ] Additive (AlgebraicClosure w.Completion)ˣ), fun σ => by
    ext x
    exact Units.ext (decompositionHom_apply (ι.infinite w) σ
      ((Additive.toMul (show Additive Ωˣ from x) : Ωˣ) : Ω))⟩

/-- Localization `Hⁿ(Gal(Ω/K), Ωˣ) → Hⁿ(K_v, K̄_vˣ)` at a finite place. -/
def brauerLocalization (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    cohomology (unitsModule K Ω) n →+
      cohomology (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))) n :=
  (map (decompositionHom (v.adicCompletion K) (ι.finite v)) (unitsLocalHom ι v) n).hom.toAddMonoidHom

/-- Localization `Hⁿ(Gal(Ω/K), Ωˣ) → Hⁿ(K_w, K̄_wˣ)` at an infinite place. -/
def realBrauerLocalization (w : InfinitePlace K) (n : ℕ) :
    cohomology (unitsModule K Ω) n →+
      cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) n :=
  (map (decompositionHom w.Completion (ι.infinite w)) (realUnitsLocalHom ι w) n).hom.toAddMonoidHom

/-- The local invariant at a finite place of a global Brauer class. -/
def localInvariant (v : HeightOneSpectrum (𝓞 K)) : cohomology (unitsModule K Ω) 2 →+ RationalModIntegers :=
  (finiteInvariant v).toAddMonoidHom.comp (brauerLocalization ι v 2)

/-- The local invariant at an infinite place of a global Brauer class. -/
def realLocalInvariant (w : InfinitePlace K) (x : cohomology (unitsModule K Ω) 2) :
    RationalModIntegers :=
  realInvariant w (realBrauerLocalization ι w 2 x)

/-- `localInvariant` is `finiteInvariant` of the localization. -/
theorem localInvariant_apply (v : HeightOneSpectrum (𝓞 K)) (x : cohomology (unitsModule K Ω) 2) :
    localInvariant ι v x = finiteInvariant v (brauerLocalization ι v 2 x) :=
  rfl

/-- The local invariant vanishes exactly when the localization does. -/
theorem localInvariant_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : cohomology (unitsModule K Ω) 2) :
    localInvariant ι v x = 0 ↔ brauerLocalization ι v 2 x = 0 := by
  rw [localInvariant_apply, AddEquiv.map_eq_zero_iff]

/-- The real local invariant vanishes exactly when the localization does. -/
theorem realLocalInvariant_eq_zero_iff (w : InfinitePlace K) (x : cohomology (unitsModule K Ω) 2) :
    realLocalInvariant ι w x = 0 ↔ realBrauerLocalization ι w 2 x = 0 :=
  realInvariant_eq_zero_iff w _

end Localization

section Restriction

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Restriction `H²(Gal(Ω/K), Ωˣ) → H²(Gal(Ω/E), Ωˣ)` to a finite subextension `E` of `Ω / K`. -/
def brauerRestriction (E : IntermediateField K Ω) :
    cohomology (unitsModule K Ω) 2 →+ cohomology (unitsModule E Ω) 2 :=
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  (unitsRestriction K E Ω 2).hom.toAddMonoidHom

/-- The local degree `[E_w : K_v]` of a finite place `w` of a finite extension `E ⊆ Ω` of `K` over
the place `v` below it. -/
def localDegree (E : IntermediateField K Ω) [FiniteDimensional K E] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] : ℕ :=
  haveI := NumberField.of_module_finite K E
  Module.finrank (v.adicCompletion K) (w.adicCompletion E)

end Restriction

section Data

variable (K Ω : Type u) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω)

/-- The fundamental exact sequence of the Brauer group of a number field and its consequences, in
the cohomology of `Gal(Ω/K)` with coefficients `Ωˣ`: (I1) to (I4) of the module documentation. -/
structure BrauerSequenceData : Prop where
  /-- (I1) A global Brauer class is nonzero at only finitely many finite places. -/
  finite_support : ∀ x : cohomology (unitsModule K Ω) 2,
    {v : HeightOneSpectrum (𝓞 K) | brauerLocalization ι v 2 x ≠ 0}.Finite
  /-- (I1) A global Brauer class all of whose localizations vanish is zero. -/
  eq_zero_of_brauerLocalization_eq_zero : ∀ x : cohomology (unitsModule K Ω) 2,
    (∀ v, brauerLocalization ι v 2 x = 0) → (∀ w, realBrauerLocalization ι w 2 x = 0) → x = 0
  /-- (I1) The reciprocity law: the sum of all local invariants of a global class is zero. -/
  sum_localInvariant_eq_zero : ∀ x : cohomology (unitsModule K Ω) 2,
    ∑ᶠ v, localInvariant ι v x + ∑ w, realLocalInvariant ι w x = 0
  /-- (I1) A family of local classes with finite support and sum of invariants zero comes from a
  unique global class. -/
  existsUnique_brauerLocalization_eq : ∀ (a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v)
    (b : ∀ w : InfinitePlace K, RealBrauerGroup w),
    {v | a v ≠ 0}.Finite → ∑ᶠ v, finiteInvariant v (a v) + ∑ w, realInvariant w (b w) = 0 →
      ∃! x : cohomology (unitsModule K Ω) 2,
        (∀ v, brauerLocalization ι v 2 x = a v) ∧ ∀ w, realBrauerLocalization ι w 2 x = b w
  /-- (I2) `H³(Gal(Ω/K), Ωˣ) = 0`. -/
  subsingleton_cohomology_three : Subsingleton (cohomology (unitsModule K Ω) 3)
  /-- (I2) In degrees `r ≥ 4`, localization to the real places is an isomorphism. -/
  bijective_realBrauerLocalization : ∀ r : ℕ, 4 ≤ r →
    Function.Bijective fun (x : cohomology (unitsModule K Ω) r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realBrauerLocalization ι w.1 r x
  /-- (I3) A class killed by `m`, with trivial real localizations, dies in every finite extension
  `E ⊆ Ω` whose local degrees above the places where it is nonzero are multiples of `m`. -/
  brauerRestriction_eq_zero : ∀ (E : IntermediateField K Ω) [FiniteDimensional K E]
    (x : cohomology (unitsModule K Ω) 2) (m : ℕ), m • x = 0 →
      (∀ w, realBrauerLocalization ι w 2 x = 0) →
      (∀ v, brauerLocalization ι v 2 x ≠ 0 → ∀ (w : HeightOneSpectrum (𝓞 E))
        [w.asIdeal.LiesOver v.asIdeal], m ∣ localDegree E v w) →
      brauerRestriction E x = 0
  /-- (I4) For a finite set `T` of finite places and `m ≠ 0` there is a finite cyclic extension of
  `K` in `Ω` whose local degrees above `T` are multiples of `m`. -/
  exists_isCyclic_dvd_localDegree : ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ), m ≠ 0 →
    ∃ (E : IntermediateField K Ω) (_ : FiniteDimensional K E), IsGalois K E ∧ IsCyclic Gal(E/K) ∧
      ∀ v ∈ T, ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal], m ∣ localDegree E v w

/-- The fundamental exact sequence of the Brauer group, (I1) to (I4), for every number field `K`,
every separable closure `Ω` of `K` and every choice of embeddings at the places. -/
def BrauerSequenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ι : PlaceEmbeddings K Ω), BrauerSequenceData K Ω ι

end Data

namespace BrauerSequenceData

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {ι : PlaceEmbeddings K Ω} (h : BrauerSequenceData K Ω ι)
include h

/-- The localization of `H²(Gal(Ω/K), Ωˣ)` to all places is injective. -/
theorem brauerLocalization_injective :
    Function.Injective fun x : cohomology (unitsModule K Ω) 2 =>
      ((fun v => brauerLocalization ι v 2 x), fun w => realBrauerLocalization ι w 2 x) := by
  intro x y hxy
  rw [← sub_eq_zero]
  refine h.eq_zero_of_brauerLocalization_eq_zero _ (fun v => ?_) (fun w => ?_)
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrArg Prod.fst hxy) v
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrArg Prod.snd hxy) w

/-- Only finitely many local invariants of a global class are nonzero. -/
theorem finite_support_localInvariant (x : cohomology (unitsModule K Ω) 2) :
    (Function.support fun v => localInvariant ι v x).Finite :=
  (h.finite_support x).subset fun v hv => by
    rw [Function.mem_support, ne_eq, localInvariant_eq_zero_iff] at hv
    exact hv

/-- A global class is zero exactly when all its local invariants vanish. -/
theorem eq_zero_iff_localInvariant (x : cohomology (unitsModule K Ω) 2) :
    x = 0 ↔ (∀ v, localInvariant ι v x = 0) ∧ ∀ w, realLocalInvariant ι w x = 0 := by
  constructor
  · rintro rfl
    exact ⟨fun v => map_zero _, fun w => by
      rw [realLocalInvariant_eq_zero_iff, map_zero]⟩
  · rintro ⟨h1, h2⟩
    exact h.eq_zero_of_brauerLocalization_eq_zero x
      (fun v => (localInvariant_eq_zero_iff ι v x).1 (h1 v))
      (fun w => (realLocalInvariant_eq_zero_iff ι w x).1 (h2 w))

/-- Every family of local classes with finite support and sum of invariants zero is the family of
localizations of a global class. -/
theorem exists_brauerLocalization_eq (a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v)
    (b : ∀ w : InfinitePlace K, RealBrauerGroup w) (ha : {v | a v ≠ 0}.Finite)
    (hab : ∑ᶠ v, finiteInvariant v (a v) + ∑ w, realInvariant w (b w) = 0) :
    ∃ x : cohomology (unitsModule K Ω) 2,
      (∀ v, brauerLocalization ι v 2 x = a v) ∧ ∀ w, realBrauerLocalization ι w 2 x = b w :=
  (h.existsUnique_brauerLocalization_eq a b ha hab).exists

/-- For a totally complex number field, `Hʳ(Gal(Ω/K), Ωˣ) = 0` for all `r ≥ 3`. -/
theorem subsingleton_cohomology_of_three_le (hK : ∀ w : InfinitePlace K, w.IsComplex) {r : ℕ}
    (hr : 3 ≤ r) : Subsingleton (cohomology (unitsModule K Ω) r) := by
  rcases eq_or_lt_of_le hr with rfl | hr4
  · exact h.subsingleton_cohomology_three
  · refine ⟨fun x y => (h.bijective_realBrauerLocalization r hr4).1 ?_⟩
    funext w
    exact absurd (hK w.1) (InfinitePlace.not_isComplex_iff_isReal.2 w.2)

end BrauerSequenceData

end

end Langlands.GaloisCohomology

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section RealInvariant

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- The real invariant of the zero family vanishes. -/
theorem realInvariant_zero_apply (w : InfinitePlace K) :
    realInvariant w ((0 : ∀ w : InfinitePlace K, RealBrauerGroup w) w) = 0 := by
  classical
  simp [realInvariant]

end RealInvariant

end

end Langlands.GaloisCohomology
