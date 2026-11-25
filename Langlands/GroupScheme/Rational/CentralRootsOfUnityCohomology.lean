import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction
import Langlands.ClassFieldTheory.Global.ReciprocityTower
import Langlands.ClassFieldTheory.Global.H1VanishingProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof

/-! # Hasse descent for unit-valued two-cocycles of finite order -/

noncomputable section

universe u

open Polynomial groupCohomology CategoryTheory

namespace Langlands.GroupScheme

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- A two-cocycle has an `n`-th-root-of-unity primitive after finite Galois refinement. -/
def RootsOfUnityPrimitiveAfterRefinement (n : ℕ) (c : Gal(L/F) × Gal(L/F) → Lˣ) : Prop :=
  ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
    (_ : Algebra L E) (_ : IsScalarTower F L E) (a : Gal(E/F) → Eˣ),
    (∀ σ, a σ ^ n = 1) ∧
      ∀ σ τ, σ • a τ / a (σ * τ) * a σ =
        Units.map (algebraMap L E) (c (σ.restrictNormal L, τ.restrictNormal L))

omit [IsGalois F L] in
private theorem exists_finite_galois_unit_root [CharZero F] (n : ℕ) (hn : n ≠ 0) (z : Lˣ) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (_ : IsGalois F E)
      (_ : Algebra L E) (_ : IsScalarTower F L E) (y : Eˣ),
      y ^ n = Units.map (algebraMap L E) z := by
  let f : L[X] := X ^ n - C (z : L)
  let M := f.SplittingField
  have hdeg : (f.map (algebraMap L M)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    rwa [natDegree_map, show f.natDegree = n from natDegree_X_pow_sub_C]
  obtain ⟨r, hr⟩ := (SplittingField.splits f).exists_eval_eq_zero hdeg
  have hr' : r ^ n = algebraMap L M (z : L) := by
    apply sub_eq_zero.mp
    simpa only [f, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      eval_sub, eval_pow, eval_X, eval_C] using hr
  have hr0 : r ≠ 0 := by
    intro hrz
    rw [hrz, zero_pow hn] at hr'
    exact z.ne_zero ((algebraMap L M).injective (hr'.symm.trans (map_zero _).symm))
  let w := Units.mk0 r hr0
  have hw : w ^ n = Units.map (algebraMap L M) z := Units.ext hr'
  let : FiniteDimensional F M := FiniteDimensional.trans F L M
  obtain ⟨E, hdim, hgal, ⟨φ⟩⟩ := exists_finite_galois_algHom F M
  let ι := φ.comp (IsScalarTower.toAlgHom F L M)
  let : Algebra L E := ι.toRingHom.toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨E, inferInstance, inferInstance, hdim, hgal, inferInstance, inferInstance,
    Units.map φ.toRingHom w, ?_⟩
  rw [← map_pow, hw]
  rfl

/-- If a finite-order two-cocycle has a unit primitive, a finite Galois refinement has a
primitive with the same finite-order bound. -/
theorem rootsOfUnityPrimitiveAfterRefinement_of_units [CharZero F]
    (n : ℕ) (hn : n ≠ 0) (c : Gal(L/F) × Gal(L/F) → Lˣ)
    (hc : ∀ q, c q ^ n = 1) (h : IsMulCoboundary₂ c) :
    RootsOfUnityPrimitiveAfterRefinement n c := by
  obtain ⟨b, hb⟩ := h
  have hpow : IsMulCocycle₁ (fun σ => b σ ^ n) := by
    intro σ τ
    have h' := congrArg (fun a : Lˣ => a ^ n) (hb σ τ)
    rw [hc, mul_pow, div_pow, ← smul_pow', div_mul_eq_mul_div] at h'
    exact (div_eq_one.mp h').symm
  obtain ⟨z, hz⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hpow
  obtain ⟨E, hE, hFE, hd, hg, hLE, hTower, y, hy⟩ := exists_finite_galois_unit_root (F := F) n hn z
  let j := Units.map (algebraMap L E).toMonoidHom
  change y ^ n = j z at hy
  let ρ : Gal(E/F) →* Gal(L/F) := AlgEquiv.restrictNormalHom L
  let e (σ : Gal(E/F)) := j (b (ρ σ))
  let d (σ : Gal(E/F)) := σ • y / y
  have hmap (σ : Gal(E/F)) (v : Lˣ) : σ • j v = j (ρ σ • v) := by
    apply Units.ext
    exact (σ.restrictNormal_commutes L (v : L)).symm
  have he (σ τ : Gal(E/F)) : σ • e τ / e (σ * τ) * e σ = j (c (ρ σ, ρ τ)) := by
    dsimp only [e]
    rw [hmap, map_mul ρ, ← _root_.map_div, ← map_mul, hb]
  have hd' (σ τ : Gal(E/F)) : d (σ * τ) = σ • d τ * d σ := by
    dsimp only [d]
    rw [mul_smul, smul_div', div_mul_div_cancel]
  refine ⟨E, hE, hFE, hd, hg, hLE, hTower, fun σ => e σ / d σ, ?_, ?_⟩
  · intro σ
    dsimp only [d, e]
    rw [div_pow, div_pow, ← smul_pow', hy, hmap, ← _root_.map_div, hz, map_pow, div_self']
  · intro σ τ
    rw [smul_div', div_div_div_comm, div_mul_div_comm, he, hd', div_mul_eq_mul_div,
      div_self', div_one]
    rfl

open Langlands.ClassFieldTheory.Local Langlands.ClassFieldTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- The relative multiplicative cohomology class of an actual unit-valued two-cocycle. -/
def relativeUnitsClass₂ (c : Gal(L/F) × Gal(L/F) → Lˣ) (hc : IsMulCocycle₂ c) :
    relativeCohomology F L 2 :=
  H2π (unitsRepresentation F L) ⟨fun q => Additive.ofMul (c q), by
    apply (mem_cocycles₂_iff _).mpr
    exact hc⟩

/-- Local vanishing of the unit class lets a roots-of-unity two-cocycle be killed on a
finite Galois refinement by a roots-of-unity cochain. -/
theorem rootsOfUnityPrimitiveAfterRefinement_of_local [NumberField F] [NumberField L]
    (n : ℕ) (hn : n ≠ 0) (c : Gal(L/F) × Gal(L/F) → Lˣ) (hc : IsMulCocycle₂ c)
    (hpow : ∀ q, c q ^ n = 1)
    (hfin : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 L))
      [w.asIdeal.LiesOver v.asIdeal],
      (unitsLocalMap v w 2).hom (relativeUnitsClass₂ c hc) = 0)
    (hinf : ∀ w : InfinitePlace L,
      Reciprocity.archimedeanInvariant w (relativeUnitsClass₂ c hc) = 0) :
    RootsOfUnityPrimitiveAfterRefinement n c := by
  have hzero := Reciprocity.eq_zero_of_local_eq_zero ideleClassH1Vanishing
    (fun p _ => localInvariantFamily unramifiedH2Exhaustion p)
    (fun p _ => localInvariantFamilyRelativeImages unramifiedH2Exhaustion p)
    (relativeUnitsClass₂ c hc) hfin hinf
  apply rootsOfUnityPrimitiveAfterRefinement_of_units n hn c hpow
  have h := (H2π_eq_zero_iff (A := unitsRepresentation F L) _).mp hzero
  obtain ⟨a, ha⟩ := h
  refine ⟨fun σ => (a σ).toMul, fun σ τ => ?_⟩
  have hστ := congrArg (fun f => (f (σ, τ)).toMul) ha
  rw [d₁₂_hom_apply] at hστ
  exact hστ

end Langlands.GroupScheme
