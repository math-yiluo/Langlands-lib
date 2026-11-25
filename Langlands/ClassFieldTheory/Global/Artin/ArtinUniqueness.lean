import Langlands.Global.Arithmetic.ClassFieldStatement
import Langlands.Global.IdeleClosedSubgroupDensity
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Frobenius

/-!
# Uniqueness of a normalized Artin map

This file belongs to the Library and uses nothing of the NYLL library. It proves that a
continuous homomorphism from the idèle classes of a number field `K` to the Galois group of a
finite Galois extension `L / K` with the discrete topology is determined by the Library's
normalization `HasArithmeticArtinNormalization`.

Two lemmas carry the proof. **Density** (`ideleClass_hom_ext_of_uniformizers`): two
continuous homomorphisms from `IdeleClasses K` to a discrete group that agree on the
uniformizers of all finite places outside a finite set are equal; their equalizer is a closed
subgroup that contains the local units outside the finite set (every local unit is a
uniformizer times a power of a fixed one) and the principal idèles, so it is everything by the
Library's density theorem `Langlands.Global.IdeleDensity.eq_top_of_isClosed`.
**Ramification** (`finite_setOf_ramified`): only finitely many finite places of `K` lie below
a prime of `L` ramified over `K`, since a ramified prime divides the different ideal, which is
nonzero. Outside them, two normalized maps send a uniformizer to Frobenius elements at the
same unramified prime, and Mathlib's `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` makes these
equal.

## Main declarations

* `exists_uniformizer`, `ideleClass_hom_ext_of_uniformizers`.
* `finite_setOf_not_isUnramifiedAt`, `finite_setOf_ramified`.
* `eq_of_isArithFrobAt_mapAlgHom`: an arithmetic Frobenius at an unramified prime is unique
  in `L ≃ₐ[K] L`.
* `eq_of_hasArithmeticArtinNormalization`: two continuous normalized maps are equal.

## Sources

Milne, *Class Field Theory*, V Proposition 4.7 and Theorem 5.3; Neukirch, *Algebraic Number
Theory*, II (3.4) and VI (5.5)–(5.6); for the different, Neukirch III (2.6).
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Global.Artin

open Langlands.Global
open scoped NumberField

section Density

variable {K : Type u} [Field K] [NumberField K]

/-- Every finite completion has a uniformizer: a unit of valuation `exp (-1)`. -/
theorem exists_uniformizer (v : Langlands.Global.FinitePlace K) :
    ∃ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

/-- Two continuous homomorphisms from the idèle classes to a discrete group that agree on all
uniformizers of all finite places outside a finite set are equal. -/
theorem ideleClass_hom_ext_of_uniformizers {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (ρ₁ ρ₂ : IdeleClasses K →ₜ* G)
    (S : Finset (Langlands.Global.FinitePlace K))
    (h : ∀ v ∉ S, ∀ π : (FiniteCompletion K v)ˣ,
      Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        ρ₁ (finiteClassInclusion K v π) = ρ₂ (finiteClassInclusion K v π)) :
    ρ₁ = ρ₂ := by
  let E : Subgroup (IdeleClasses K) := MonoidHom.eqLocus ρ₁.toMonoidHom ρ₂.toMonoidHom
  have hE : IsClosed (E : Set (IdeleClasses K)) := isClosed_eq ρ₁.continuous ρ₂.continuous
  let H : Subgroup (Ideles K) := E.comap (ideleClassMap K).toMonoidHom
  have hH : IsClosed (H : Set (Ideles K)) := hE.preimage (ideleClassMap K).continuous
  have hprin : ∀ a : Kˣ, diagonalUnits K a ∈ H := by
    intro a
    have h1 : ideleClassMap K (diagonalUnits K a) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    change ρ₁ (ideleClassMap K (diagonalUnits K a)) = ρ₂ (ideleClassMap K (diagonalUnits K a))
    rw [h1, map_one, map_one]
  have hloc : ∀ v ∉ S, ∀ a : (FiniteCompletion K v)ˣ, finiteIdeleInclusion K v a ∈ H := by
    intro v hv a
    change finiteClassInclusion K v a ∈ E
    obtain ⟨π, hπ⟩ := exists_uniformizer v
    have ha0 : Valued.v (a : FiniteCompletion K v) ≠ 0 := by simp
    set m := WithZero.log (Valued.v (a : FiniteCompletion K v))
    have hπ' : Valued.v ((a * π ^ (m + 1) : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) =
        WithZero.exp (-1 : ℤ) := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ,
        ← WithZero.exp_log ha0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      congr 1
      simp only [smul_eq_mul]
      ring
    have hdecomp : a = (a * π ^ (m + 1)) * π ^ (-(m + 1)) := by group
    rw [hdecomp, map_mul, map_zpow]
    exact E.mul_mem (h v hv _ hπ') (E.zpow_mem (h v hv π hπ) _)
  have htop := IdeleDensity.eq_top_of_isClosed H S hH hprin hloc
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (principalIdeles K) x
  have hy : y ∈ H := htop ▸ Subgroup.mem_top y
  exact hy

end Density

section Ramification

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- Only finitely many finite places of `L` are ramified over `K`: a ramified prime divides the
different ideal of `𝓞 L` over `𝓞 K`, which is nonzero. -/
theorem finite_setOf_not_isUnramifiedAt :
    {w : Langlands.Global.FinitePlace L | ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}.Finite := by
  have hne : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact differentIdeal_ne_bot
  refine (Ideal.finite_factors hne).subset fun w hw => ?_
  by_contra hdvd
  exact hw ((not_dvd_differentIdeal_iff (A := 𝓞 K) (P := w.asIdeal)).1 hdvd)

/-- Only finitely many finite places of `K` lie below a prime of `L` ramified over `K`. -/
theorem finite_setOf_ramified :
    {v : Langlands.Global.FinitePlace K | ∃ w : Langlands.Global.FinitePlace L,
      w.asIdeal.LiesOver v.asIdeal ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal}.Finite := by
  refine ((finite_setOf_not_isUnramifiedAt K L).biUnion fun w _ =>
    (show {v : Langlands.Global.FinitePlace K | w.asIdeal.LiesOver v.asIdeal}.Subsingleton from
      fun _ h₁ _ h₂ => IsDedekindDomain.HeightOneSpectrum.ext
        ((h₁ : w.asIdeal.LiesOver _).over.trans (h₂ : w.asIdeal.LiesOver _).over.symm)).finite).subset
    ?_
  rintro v ⟨w, hw, hram⟩
  exact Set.mem_biUnion hram hw

omit [NumberField K] [NumberField L] in
/-- Every finite place of `K` has a finite place of `L` above it. -/
theorem exists_liesOver (v : Langlands.Global.FinitePlace K) :
    ∃ w : Langlands.Global.FinitePlace L, w.asIdeal.LiesOver v.asIdeal := by
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal (𝓞 L)) (by rw [Ideal.under_bot]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [← hQP, h, Ideal.under_bot]
  exact ⟨⟨Q, hQ, hQ0⟩, ⟨hQP.symm⟩⟩

end Ramification

section Uniqueness

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] in
/-- An arithmetic Frobenius at a prime unramified over `K`, in the Library's form with
`RingOfIntegers.mapAlgHom`, is unique in `L ≃ₐ[K] L`. -/
theorem eq_of_isArithFrobAt_mapAlgHom {σ τ : L ≃ₐ[K] L} (w : Langlands.Global.FinitePlace L)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hσ : (NumberField.RingOfIntegers.mapAlgHom σ).IsArithFrobAt w.asIdeal)
    (hτ : (NumberField.RingOfIntegers.mapAlgHom τ).IsArithFrobAt w.asIdeal) : σ = τ := by
  have hmap := hσ.eq_of_isUnramifiedAt hτ (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  have ha : σ (algebraMap (𝓞 L) L a) = τ (algebraMap (𝓞 L) L a) :=
    congrArg (algebraMap (𝓞 L) L) (DFunLike.congr_fun hmap a)
  have hb : σ (algebraMap (𝓞 L) L b) = τ (algebraMap (𝓞 L) L b) :=
    congrArg (algebraMap (𝓞 L) L) (DFunLike.congr_fun hmap b)
  rw [map_div₀, map_div₀, ha, hb]

/-- Two continuous homomorphisms from the idèle classes to `L ≃ₐ[K] L` with the discrete
topology that both satisfy the Library's arithmetic normalization are equal. -/
theorem eq_of_hasArithmeticArtinNormalization :
    letI : TopologicalSpace (L ≃ₐ[K] L) := ⊥
    ∀ ρ₁ ρ₂ : IdeleClasses K →ₜ* (L ≃ₐ[K] L),
      HasArithmeticArtinNormalization ρ₁.toMonoidHom →
      HasArithmeticArtinNormalization ρ₂.toMonoidHom → ρ₁ = ρ₂ := by
  let : TopologicalSpace (L ≃ₐ[K] L) := ⊥
  have : DiscreteTopology (L ≃ₐ[K] L) := ⟨rfl⟩
  intro ρ₁ ρ₂ h₁ h₂
  classical
  apply ideleClass_hom_ext_of_uniformizers ρ₁ ρ₂ (finite_setOf_ramified K L).toFinset
  intro v hv π hπ
  obtain ⟨w, hw⟩ := exists_liesOver K L v
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
    by_contra hram
    exact hv ((finite_setOf_ramified K L).mem_toFinset.mpr ⟨w, hw, hram⟩)
  exact eq_of_isArithFrobAt_mapAlgHom w hunram (h₁ v w hw hunram π hπ) (h₂ v w hw hunram π hπ)

end Uniqueness

end Langlands.ClassFieldTheory.Global.Artin
