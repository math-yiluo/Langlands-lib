import Langlands.Analysis.Meromorphic.FredholmCriterionProof

/-! # A Fredholm envelope exact at its base point

This variant of the local construction in Bernstein–Lapid §3.4 uses the actual
kernel at the base point, rather than an auxiliary finite-dimensional range.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic.FredholmCriterion

open Set ContinuousLinearMap
open scoped Manifold

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

/-- For a left inverse modulo compact operators, correct the finite-rank remainder to
obtain exactly the orthogonal projection off the kernel. The codomain need not be Hilbert. -/
theorem exists_comp_eq_id_sub_starProjection (A : B →L[ℂ] C) (D : C →L[ℂ] B)
    (hD : IsCompactOperator (D ∘L A - ContinuousLinearMap.id ℂ B)) :
    letI : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    FiniteDimensional ℂ A.ker ∧
      ∃ L : C →L[ℂ] B, L ∘L A = ContinuousLinearMap.id ℂ B - A.ker.starProjection := by
  let : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
  obtain ⟨G, F, hF, hGF⟩ := RieszFredholm.exists_leftInverse_mod_finiteRank A D hD
  let W := F.range
  let : FiniteDimensional ℂ W := hF
  have hGA (x : B) : G (A x) = x - F x := congrArg (fun f : B →L[ℂ] B => f x) hGF
  have hKW : A.ker ≤ W := by
    intro x hx
    have hAx : A x = 0 := hx
    have h := hGA x
    rw [hAx, map_zero] at h
    exact ⟨x, (sub_eq_zero.mp h.symm).symm⟩
  refine ⟨Submodule.finiteDimensional_of_le hKW, ?_⟩
  let Q := W ⊓ A.kerᗮ
  let T := A ∘L Q.subtypeL
  have hbot : T.ker = ⊥ := by
    refine le_antisymm (fun y hy => ?_) bot_le
    have hK : (y : B) ∈ A.ker := hy
    have hO : (y : B) ∈ A.kerᗮ := y.2.2
    have h0 : (y : B) = 0 := inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hK hO)
    simpa only [Submodule.mem_bot] using (Subtype.ext h0 : y = 0)
  have hT : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
  have : FiniteDimensional ℂ T.range := LinearMap.finiteDimensional_range _
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional T.range
  have hTr : T.rangeRestrict.HasLeftInverse :=
    HasLeftInverse.of_injective_of_finiteDimensional (fun x y hxy => hT (congrArg Subtype.val hxy))
  have hJ : T.HasLeftInverse := by
    refine ⟨hTr.leftInverse ∘L p, fun x => ?_⟩
    change hTr.leftInverse (p (T.rangeRestrict x : C)) = x
    rw [hp, hTr.leftInverse_leftInverse]
  let J := hJ.leftInverse
  let P := A.kerᗮ.starProjection
  refine ⟨P ∘L G + Q.subtypeL ∘L J ∘L (ContinuousLinearMap.id ℂ C - A ∘L G), ?_⟩
  ext x
  have hP (y : B) : P y = y - A.ker.starProjection y := A.ker.starProjection_orthogonal_val y
  have hFP : P (F x) ∈ Q := by
    refine ⟨?_, A.kerᗮ.starProjection_apply_mem _⟩
    rw [hP]
    exact W.sub_mem (LinearMap.mem_range_self _ _) (hKW (A.ker.starProjection_apply_mem _))
  let y : Q := ⟨P (F x), hFP⟩
  have hAy : T y = A (F x) := by
    change A (P (F x)) = A (F x)
    have hzero : A (A.ker.starProjection (F x)) = 0 := A.ker.starProjection_apply_mem _
    simp [hP, hzero]
  have hC : (ContinuousLinearMap.id ℂ C - A ∘L G) (A x) = T y := by
    simp [hAy, hGA, map_sub]
  change P (G (A x)) + (J ((ContinuousLinearMap.id ℂ C - A ∘L G) (A x)) : B) =
    (ContinuousLinearMap.id ℂ B - A.ker.starProjection) x
  rw [hC, show J (T y) = y from hJ.leftInverse_leftInverse y, hGA, map_sub]
  change P x - P (F x) + P (F x) = x - A.ker.starProjection x
  rw [sub_add_cancel, hP]

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- An exact-at-the-base-point form of the Euclidean Fredholm envelope for a Hilbert domain.
Only containment of the kernels in the ranges at *other* points is asserted. -/
theorem exists_finiteType_euclidean_exact_fiber {A : E → B →L[ℂ] C} {S : Set E}
    (hS : IsOpen S) (hA : ∀ v (φ : StrongDual ℂ C), DifferentiableOn ℂ (fun z => φ (A z v)) S)
    {z₀ : E} (hz₀ : z₀ ∈ S) (D : C →L[ℂ] B)
    (hD : IsCompactOperator (D ∘L A z₀ - ContinuousLinearMap.id ℂ B)) :
    ∃ U ⊆ S, IsOpen U ∧ z₀ ∈ U ∧ ∃ (n : ℕ) (ℓ : E → (Fin n → ℂ) →L[ℂ] B),
      (∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun z => φ (ℓ z v)) U) ∧
      (∀ z ∈ U, Function.Injective (ℓ z)) ∧
      (∀ z ∈ U, ∀ v, A z v = 0 → v ∈ Set.range (ℓ z)) ∧
      Set.range (ℓ z₀) = (A z₀).ker := by
  let : CompleteSpace (A z₀).ker := (A z₀).isClosed_ker.completeSpace_coe
  obtain ⟨hker, L, hL⟩ := exists_comp_eq_id_sub_starProjection (A z₀) D hD
  let : FiniteDimensional ℂ (A z₀).ker := hker
  let b := Module.finBasis ℂ (A z₀).ker
  let ι := LinearMap.toContinuousLinearMap ((A z₀).ker.subtype ∘ₗ b.equivFun.symm.toLinearMap)
  have hι : Function.Injective ι := Subtype.val_injective.comp b.equivFun.symm.injective
  have hιran : Set.range ι = (A z₀).ker := by
    ext v
    exact ⟨fun ⟨c, hc⟩ => hc ▸ (b.equivFun.symm c).property,
      fun hv => ⟨b.equivFun ⟨v, hv⟩, by simp [ι]⟩⟩
  let X : E → B →L[ℂ] B := fun z => 1 + L ∘L (A z - A z₀)
  have hX : ∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun z => φ (X z v)) S := by
    intro v φ
    refine (((hA v (φ ∘L L)).sub
      (differentiableOn_const ((φ ∘L L) (A z₀ v)))).const_add (φ v)).congr fun z _ => ?_
    simp [X, map_sub]
  have hX₀ : X z₀ = 1 := by simp [X]
  have hXc : ContinuousOn X S := fun z hz =>
    (WeakHolomorphy.continuousAt_of_weak hS hX hz).continuousWithinAt
  let U := S ∩ X ⁻¹' {u | IsUnit u}
  have hUS : U ⊆ S := inter_subset_left
  have hU : IsOpen U := hXc.isOpen_inter_preimage hS Units.isOpen
  have hzU : z₀ ∈ U := ⟨hz₀, by simp [hX₀]⟩
  have hunit : ∀ z ∈ U, IsUnit (X z) := fun _ hz => hz.2
  have hleft (z : E) (hz : z ∈ U) (v : B) : Ring.inverse (X z) (X z v) = v := by
    obtain ⟨u, hu⟩ := hunit z hz
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  have hright (z : E) (hz : z ∈ U) (v : B) : X z (Ring.inverse (X z) v) = v := by
    obtain ⟨u, hu⟩ := hunit z hz
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
  refine ⟨U, hUS, hU, hzU, _, fun z => Ring.inverse (X z) ∘L ι, ?_, ?_, ?_, ?_⟩
  · intro v φ
    exact WeakHolomorphy.differentiableOn_inverse_apply hU
      (fun v φ => (hX v φ).mono hUS) hunit (ι v) φ
  · intro z hz
    have hinj : Function.Injective ⇑(Ring.inverse (X z) : B →L[ℂ] B) := fun a b hab => by
      rw [← hright z hz a, ← hright z hz b, hab]
    exact hinj.comp hι
  · intro z hz v hv
    have h1 : L (A z₀ v) = v - (A z₀).ker.starProjection v :=
      congrArg (fun f : B →L[ℂ] B => f v) hL
    have hXv : X z v = (A z₀).ker.starProjection v := by simp [X, hv, h1]
    have hmem : X z v ∈ Set.range ι := by rw [hιran, hXv]; exact Submodule.starProjection_apply_mem _ _
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by change Ring.inverse (X z) (ι c) = v; rw [hc, hleft z hz]⟩
  · change Set.range (Ring.inverse (X z₀) ∘L ι) = (A z₀).ker
    rwa [hX₀, Ring.inverse_one, show (1 : B →L[ℂ] B) ∘L ι = ι by ext v; rfl]

end Euclidean

end Langlands.Analysis.Meromorphic.FredholmCriterion

namespace Langlands.Analysis.Meromorphic

open Set
open scoped Manifold

universe uE uM uB uC

/-- Exact-base-fiber refinement of Fredholm's criterion for a Hilbert domain. On an
open neighbourhood contained in the parameter set, the weakly holomorphic injective
family contains the kernels, and its range at the base point equals the kernel there. -/
def ExactFiberFredholmCriterionStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    {B : Type uB} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {C : Type uC} [NormedAddCommGroup C] [NormedSpace ℂ C]
    {A : M → B →L[ℂ] C} {S : Set M}, IsOpen S →
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) A S →
    ∀ {s₀ : M}, s₀ ∈ S → ∀ D : C →L[ℂ] B,
      IsCompactOperator (D ∘L A s₀ - ContinuousLinearMap.id ℂ B) →
      ∃ U ⊆ S, IsOpen U ∧ s₀ ∈ U ∧ ∃ (n : ℕ) (ℓ : M → (Fin n → ℂ) →L[ℂ] B),
        IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ℓ U ∧
        (∀ s ∈ U, Function.Injective (ℓ s)) ∧
        (∀ s ∈ U, ∀ v, A s v = 0 → v ∈ Set.range (ℓ s)) ∧
        Set.range (ℓ s₀) = (A s₀).ker

/-- The exact-base-fiber criterion, on an arbitrary open subset of a complex manifold. -/
theorem exactFiberFredholmCriterion : ExactFiberFredholmCriterionStatement.{uE, uM, uB, uC} := by
  intro E _ _ _ M _ _ _ B _ _ _ C _ _ A S hS hA s₀ hs₀ D hD
  set e := extChartAt 𝓘(ℂ, E) s₀ with he
  let T := e.target ∩ e.symm ⁻¹' S
  have hT : IsOpen T :=
    (continuousOn_extChartAt_symm s₀).isOpen_inter_preimage (isOpen_extChartAt_target s₀) hS
  have hd : MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, E) e e.source := by
    rw [he, extChartAt_source]
    exact mdifferentiableOn_extChartAt
  have hA' (v : B) (φ : StrongDual ℂ C) :
      DifferentiableOn ℂ (fun z => φ (A (e.symm z) v)) T :=
    ((hA v φ).comp (mdifferentiableOn_extChartAt_symm.mono (inter_subset_left (t := e.symm ⁻¹' S)))
      (fun _ hz => hz.2)).differentiableOn
  have hs₀e : e.symm (e s₀) = s₀ := extChartAt_to_inv s₀
  have he₀ : e s₀ ∈ T := ⟨mem_extChartAt_target s₀, by simpa only [mem_preimage, hs₀e] using hs₀⟩
  have hD' : IsCompactOperator (D ∘L A (e.symm (e s₀)) - ContinuousLinearMap.id ℂ B) := by
    rwa [hs₀e]
  obtain ⟨U', hU'T, hU'o, he₀U', n, ℓ, hℓ, hℓi, hℓk, hℓ₀⟩ :=
    FredholmCriterion.exists_finiteType_euclidean_exact_fiber hT hA' he₀ D hD'
  refine ⟨e.source ∩ e ⁻¹' U', ?_, isOpen_extChartAt_preimage' s₀ hU'o,
    ⟨mem_extChartAt_source s₀, he₀U'⟩, n, fun s => ℓ (e s), ?_, ?_, ?_, ?_⟩
  · intro s hs
    have h : e.symm (e s) ∈ S := (hU'T hs.2).2
    rwa [e.left_inv hs.1] at h
  · intro v φ
    exact (hℓ v φ).mdifferentiableOn.comp (hd.mono inter_subset_left) (fun _ hs => hs.2)
  · intro s hs
    exact hℓi (e s) hs.2
  · intro s hs v hv
    apply hℓk (e s) hs.2 v
    rwa [e.left_inv hs.1]
  · simpa only [hs₀e] using hℓ₀

end Langlands.Analysis.Meromorphic
