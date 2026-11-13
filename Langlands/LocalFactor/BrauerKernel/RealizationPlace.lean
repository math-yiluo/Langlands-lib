import Langlands.Global.CompletionPadicTower
import Langlands.ClassField.Global.LocalRelativeWeilMap

/-! # The distinguished place of a global realization of a p-adic field -/

noncomputable section

set_option autoImplicit false

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology
open Langlands.Global.CompletionPadic

universe u w

/-- A completion of a number field that is topologically isomorphic to a p-adic field lies
over `p`. -/
theorem residuePrime_eq_of_ringEquiv {p : ℕ} [Fact p.Prime] {K : Type w} [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (F : PadicField.{u} p)
    (φ : v.adicCompletion K ≃+* F.Carrier)
    (hφ : @Continuous _ _ F.canonicalTopology _ φ.symm) :
    residuePrime v = p := by
  have h1 : @Tendsto ℕ F.Carrier (fun n => (p : F.Carrier) ^ n) atTop
      (@nhds _ F.canonicalTopology 0) := by
    rw [← F.canonicalTopologicalData_topology, F.canonicalTopologicalData_normTopology]
    let _ := F.canonicalNormedField
    refine tendsto_pow_atTop_nhds_zero_of_norm_lt_one ?_
    change F.canonicalNorm (p : F.Carrier) < 1
    rw [F.canonicalNorm_prime]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have h2 : Tendsto (fun n => (p : v.adicCompletion K) ^ n) atTop (𝓝 0) := by
    have h := (@Continuous.tendsto _ _ F.canonicalTopology _ _ hφ 0).comp h1
    rw [map_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, map_pow, map_natCast]
  have h3 : Valued.v (p : v.adicCompletion K) < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp h2)
  have h4 : ((p : 𝓞 K)) ∈ v.asIdeal := by
    refine (v.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).mp ?_
    have hc : ∀ n : ℕ, (((n : K)) : v.adicCompletion K) = (n : v.adicCompletion K) := by
      intro n
      induction n with
      | zero =>
        simp only [Nat.cast_zero]
        exact adicCompletion.coe_zero (K := K) (v := v)
      | succ n ih =>
        simp only [Nat.cast_succ]
        rw [adicCompletion.coe_add, ih, adicCompletion.coe_one]
    have h : (((algebraMap (𝓞 K) K (p : 𝓞 K) : K) : v.adicCompletion K)) =
        (p : v.adicCompletion K) := by
      rw [map_natCast]
      exact hc p
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h]
    exact h3
  have h5 : residuePrime v ∣ p := by
    refine (Rat.HeightOneSpectrum.natGenerator_dvd_iff (rationalPlace v)).2 ?_
    refine (Ideal.mem_map_of_equiv _ _).2 ⟨(p : 𝓞 ℚ), ?_, map_natCast _ _⟩
    rw [Ideal.over_def v.asIdeal (rationalPlace v).asIdeal, Ideal.mem_comap, map_natCast]
    exact h4
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : (residuePrime v).Prime) Fact.out).mp h5

/-- A continuous ring homomorphism between topological `ℚ_p`-algebras with continuous
structure maps and Hausdorff target fixes `ℚ_p`. -/
theorem ringHom_algebraMap_of_continuous {p : ℕ} [Fact p.Prime] {A B : Type*}
    [DivisionRing A] [DivisionRing B] [Algebra (Padic p) A] [Algebra (Padic p) B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] (hA : Continuous (algebraMap (Padic p) A))
    (hB : Continuous (algebraMap (Padic p) B)) (g : A →+* B) (hg : Continuous g)
    (a : Padic p) : g (algebraMap (Padic p) A a) = algebraMap (Padic p) B a := by
  have h := (Padic.denseRange_ratCast p).equalizer (hg.comp hA) hB
    (funext fun q => by simp only [Function.comp_apply, map_ratCast])
  exact congrFun h a

/-- A continuous ring homomorphism between topological `ℚ_p`-algebras as an algebra
homomorphism. -/
def algHomOfContinuous {p : ℕ} [Fact p.Prime] {A B : Type*} [DivisionRing A] [DivisionRing B]
    [Algebra (Padic p) A] [Algebra (Padic p) B] [TopologicalSpace A] [TopologicalSpace B]
    [T2Space B] (hA : Continuous (algebraMap (Padic p) A))
    (hB : Continuous (algebraMap (Padic p) B)) (g : A →+* B) (hg : Continuous g) :
    A →ₐ[Padic p] B :=
  { g with commutes' := ringHom_algebraMap_of_continuous hA hB g hg }

@[simp]
theorem algHomOfContinuous_apply {p : ℕ} [Fact p.Prime] {A B : Type*} [DivisionRing A]
    [DivisionRing B] [Algebra (Padic p) A] [Algebra (Padic p) B] [TopologicalSpace A]
    [TopologicalSpace B] [T2Space B] (hA : Continuous (algebraMap (Padic p) A))
    (hB : Continuous (algebraMap (Padic p) B)) (g : A →+* B) (hg : Continuous g) (x : A) :
    algHomOfContinuous hA hB g hg x = g x := rfl

end Langlands.LocalFactor.NonabelianBrauer
