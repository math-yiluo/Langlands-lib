import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.Algebra.LocalUnitaryResidue

/-! # The exact marked vertex and quaternionic model in local rank-one type C -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Matrix

namespace Langlands.GroupScheme

namespace Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  {σ : FirstKindInvolution K D}

/-- A nondegenerate trace-valued antihermitian form of Witt index one in at least
three variables has a nonzero alternating value. -/
theorem exists_nonzero_alternating_of_wittIndex_one {m : ℕ} (hm : 3 ≤ m)
    {H : Matrix (Fin m) (Fin m) D} (hH : σ.IsAntihermitian H)
    (hu : IsUnit H) (hw : σ.wittIndex H = 1) :
    ∃ c : D, c ∈ σ.alternatingSubspace ∧ c ≠ 0 := by
  obtain ⟨e, he, hee⟩ := exists_isotropic_of_wittIndex_eq_one hw
  obtain ⟨f, hef, _hff⟩ := exists_hyperbolic_pair hH hu he hee
  obtain ⟨w, hw0, hwe, hwf⟩ : ∃ w : Fin m → D, w ≠ 0 ∧ σ.sesqForm H w e = 0 ∧
      σ.sesqForm H w f = 0 := by
    let φ : (Fin m → D) →ₗ[D] (Fin 2 → D) :=
      { toFun := fun x => ![σ.sesqForm H x e, σ.sesqForm H x f]
        map_add' := fun x y => by
          ext i
          fin_cases i <;> simp [sesqForm_add_left]
        map_smul' := fun a x => by
          ext i
          fin_cases i <;> simp [sesqForm_smul_left] }
    have h := LinearMap.finrank_range_add_finrank_ker φ
    have hr : Module.finrank D (LinearMap.range φ) ≤ 2 := by
      calc Module.finrank D (LinearMap.range φ) ≤ Module.finrank D (Fin 2 → D) :=
            Submodule.finrank_le _
        _ = 2 := Module.finrank_fin_fun D
    rw [Module.finrank_fin_fun] at h
    have hk : LinearMap.ker φ ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at h
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
    have hφ := LinearMap.mem_ker.1 hw
    exact ⟨w, hw0, by simpa [φ] using congrFun hφ 0, by simpa [φ] using congrFun hφ 1⟩
  have hew : σ.sesqForm H e w = 0 := by
    rw [IsAntihermitian.sesqForm_swap σ hH, hwe, map_zero, neg_zero]
  refine ⟨σ.sesqForm H w w, sesqForm_self_mem_alternatingSubspace hH w, ?_⟩
  intro hc
  have hli : LinearIndependent D ![e, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => σ.sesqForm H z f) hst
    simp only [sesqForm_add_left, sesqForm_smul_left, hef, hwf, mul_one, mul_zero,
      add_zero] at h1
    have h0 : σ.sesqForm H 0 f = 0 := by simp [sesqForm]
    rw [h0] at h1
    subst h1
    rw [zero_smul, zero_add, smul_eq_zero] at hst
    exact ⟨rfl, hst.resolve_right hw0⟩
  have hW : σ.IsTotallyIsotropic H (Submodule.span D (Set.range ![e, w])) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hx
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D).1 hy
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sesqForm_add_left, sesqForm_add_right, sesqForm_smul_left, sesqForm_smul_right,
      hee, hew, hwe, hc]
    simp
  have h2 := finrank_le_wittIndex σ hW
  rw [finrank_span_eq_card hli, hw] at h2
  simp at h2

end Quaternionic.FirstKindInvolution

/-- Actual quaternionic symplectic presentation data in `n` variables, including
the group-scheme isomorphism and the trace-valued condition in every characteristic. -/
structure LocalRankOneTypeCPresentation (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (n : ℕ) where
  divisionAlgebra : Type u
  [divisionRing : DivisionRing divisionAlgebra]
  [algebra : Algebra K divisionAlgebra]
  [finiteDimensional : FiniteDimensional K divisionAlgebra]
  [central : Algebra.IsCentral K divisionAlgebra]
  finrank_eq_four : Module.finrank K divisionAlgebra = 4
  involution : Quaternionic.FirstKindInvolution K divisionAlgebra
  symmetric_finrank : Module.finrank K involution.symmetricSubspace = 3
  [size_ne_zero : NeZero n]
  form : Matrix (Fin n) (Fin n) divisionAlgebra
  antihermitian : involution.IsAntihermitian form
  unit : IsUnit form
  wittIndex_eq_one : involution.wittIndex form = 1
  iso : G ≅ involution.symplecticGroup form

attribute [instance] LocalRankOneTypeCPresentation.divisionRing
  LocalRankOneTypeCPresentation.algebra LocalRankOneTypeCPresentation.finiteDimensional
  LocalRankOneTypeCPresentation.central

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- Over a nonarchimedean local field, a simply connected absolutely almost-simple
group of type `C_n`, `n ≥ 2`, and split rank one has a quaternionic symplectic
model in `n` variables, precisely vertex 2 marked, and trivial full star action.
This theorem does not bound `n` from above. -/
theorem localRankOneTypeC_presentation_and_marking
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (hrank : splitRank G = 1) :
    Nonempty (LocalRankOneTypeCPresentation K G n) ∧
      d.IsNumberingOf (CartanMatrix.C n) (fun i => i.val = 1) e ∧ d.StarIsTrivial := by
  obtain ⟨degree, m, hm, D, _, _, _, _, hdeg, hmd, hfin, σ, hsym, H, hH, hu,
      hw, hiso, hmarked⟩ :=
    typeCDivisionForm K G d n e hn hsc has hcartan
  have hw1 : σ.wittIndex H = 1 := by
    rw [hrank] at hw
    exact_mod_cast hw
  have hτ : Langlands.IsUnitaryInvolution (⇑(RingHom.id K)) (⇑σ) :=
    ⟨σ.map_add, σ.map_mul, σ.apply_apply, σ.map_algebraMap⟩
  have hbound : degree ∣ 2 := by
    have h := Langlands.UnitaryInvolution.reducedDegree_dvd_two
      (L := K) (D := D) (σ := RingHom.id K) (τ := ⇑σ) (fun _ => rfl) hτ
    simpa [Langlands.CentralSimple.reducedDegree, hfin, pow_two, Nat.sqrt_eq] using h
  have hd2 : degree = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hbound with hd1 | hd2
    · have hD1 : Module.finrank K D = 1 := by simpa [hd1] using hfin
      have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hD1).2
      have hσid : ∀ x : D, σ x = x := by
        intro x
        obtain ⟨c, rfl⟩ := hsurj x
        exact σ.map_algebraMap c
      have hm3 : 3 ≤ m := by
        rw [hd1, mul_one] at hmd
        omega
      obtain ⟨c, hc, hc0⟩ := σ.exists_nonzero_alternating_of_wittIndex_one hm3 hH hu hw1
      obtain ⟨a, ha⟩ := σ.mem_alternatingSubspace.mp hc
      rw [hσid, sub_self] at ha
      exact (hc0 ha.symm).elim
    · exact hd2
  have hmn : m = n := by
    rw [hd2] at hmd
    omega
  subst m
  have hD4 : Module.finrank K D = 4 := by simpa [hd2] using hfin
  have hσ3 : Module.finrank K σ.symmetricSubspace = 3 := by simpa [hd2] using hsym
  let : NeZero n := hm
  refine ⟨?_, ⟨hcartan, ?_⟩, ?_⟩
  · obtain ⟨iso⟩ := hiso
    exact ⟨{
      divisionAlgebra := D
      finrank_eq_four := hD4
      involution := σ
      symmetric_finrank := hσ3
      form := H
      antihermitian := hH
      unit := hu
      wittIndex_eq_one := hw1
      iso := iso }⟩
  · intro a
    rw [hmarked, hrank, hd2]
    constructor
    · rintro ⟨j, hj, hj1, heq⟩
      have hj' : j ≤ 1 := by exact_mod_cast hj1
      omega
    · intro ha
      exact ⟨1, by omega, le_rfl, by omega⟩
  · exact TypeCQuasiSplitInnerFormProof.star_eq_self d hn e hcartan

/-- Choose the actual quaternionic presentation supplied by the local type-C
rank-one theorem. No restriction to absolute ranks two and three is assumed. -/
def localRankOneTypeCPresentation
    (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n) (hn : 2 ≤ n)
    (hsc : IsSimplyConnected G) (has : IsAbsolutelyAlmostSimple G)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (hrank : splitRank G = 1) : LocalRankOneTypeCPresentation K G n :=
  Classical.choice (localRankOneTypeC_presentation_and_marking d e hn hsc has hcartan hrank).1

end Langlands.GroupScheme
