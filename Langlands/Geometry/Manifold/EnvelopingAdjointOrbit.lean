import Langlands.Geometry.Manifold.LinearAdjointDifferential
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite scalar expansions for enveloping adjoint orbits -/

noncomputable section

open Filter Set
open scoped Classical ContDiff Manifold TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Manifold.EnvelopingAdjoint

open MatrixCoefficientLie

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]

local instance : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞) (by simp)
attribute [local instance 100] LieRing.ofAssociativeRing

local instance : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (contDiff_fst.mul contDiff_snd).contMDiff

local notation "MI" => 𝓘(ℝ, E)
local notation "LieAlg" => GroupLieAlgebra MI G
local notation "LC" => ℂ ⊗[ℝ] LieAlg
local notation "U" => UniversalEnvelopingAlgebra ℂ LC
local notation "gen" => UniversalEnvelopingAlgebra.ι ℂ (L := LC)

/-- The real generator of the complex enveloping algebra. -/
private def generator : LieAlg →ₗ[ℝ] U :=
  ((gen).toLinearMap.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ LieAlg 1)

private theorem generator_lie (X Y : LieAlg) :
    generator ⁅X, Y⁆ = generator X * generator Y - generator Y * generator X := by
  have h := (gen).map_lie ((1 : ℂ) ⊗ₜ[ℝ] X) ((1 : ℂ) ⊗ₜ[ℝ] Y)
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] at h
  exact h

private theorem gen_tmul (c : ℂ) (X : LieAlg) : gen (c ⊗ₜ[ℝ] X) = c • generator X := by
  change gen (c ⊗ₜ[ℝ] X) = c • gen ((1 : ℂ) ⊗ₜ[ℝ] X)
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable (S : Subalgebra ℝ (G → ℝ))

/-- A scalar expansion of an enveloping orbit and of its derivative at the identity. -/
private structure Expansion (α : G → U →ₐ[ℂ] U) (a : U) where
  index : Type
  finite : Fintype index
  coeff : index → G → ℝ
  term : index → U
  regular : ∀ i, coeff i ∈ S
  smooth : ∀ i, ContMDiff MI 𝓘(ℝ, ℝ) ∞ (coeff i)
  value : ∀ g, letI := finite; ∑ i, coeff i g • term i = α g a
  derivative : ∀ Y : LieAlg, letI := finite;
    ∑ i, mvfderiv MI (coeff i) 1 Y • term i = generator Y * a - a * generator Y

variable (α : G → UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G) →ₐ[ℂ]
  UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G))

private def Expansion.add {a b : U} (p : Expansion S α a) (q : Expansion S α b) :
    Expansion S α (a + b) := by
  letI := p.finite
  letI := q.finite
  refine ⟨p.index ⊕ q.index, inferInstance, Sum.elim p.coeff q.coeff,
    Sum.elim p.term q.term, ?_, ?_, ?_, ?_⟩
  · rintro (i | j)
    · exact p.regular i
    · exact q.regular j
  · rintro (i | j)
    · exact p.smooth i
    · exact q.smooth j
  · intro g
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, p.value, q.value, map_add]
  · intro Y
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, p.derivative, q.derivative,
      mul_add, add_mul, add_sub_add_comm]

private def Expansion.mul (hone : α 1 = AlgHom.id ℂ U)
    {a b : U} (p : Expansion S α a) (q : Expansion S α b) : Expansion S α (a * b) := by
  letI := p.finite
  letI := q.finite
  have hsum (s : p.index → ℝ) (t : q.index → ℝ) :
      ∑ ij : p.index × q.index, (s ij.1 * t ij.2) • (p.term ij.1 * q.term ij.2) =
        (∑ i, s i • p.term i) * (∑ j, t j • q.term j) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [smul_mul_smul_comm]
  refine ⟨p.index × q.index, inferInstance, fun ij => p.coeff ij.1 * q.coeff ij.2,
    fun ij => p.term ij.1 * q.term ij.2,
    fun ij => S.mul_mem (p.regular ij.1) (q.regular ij.2),
    fun ij => (p.smooth ij.1).mul (q.smooth ij.2), ?_, ?_⟩
  · intro g
    rw [map_mul, ← p.value g, ← q.value g]
    exact hsum (fun i => p.coeff i g) (fun j => q.coeff j g)
  · intro Y
    simp_rw [mvfderiv_mul ((p.smooth _).mdifferentiableAt (by simp))
      ((q.smooth _).mdifferentiableAt (by simp)), add_apply,
      smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
    have h₁ := hsum (fun i => p.coeff i 1) (fun j => mvfderiv MI (q.coeff j) 1 Y)
    have h₂ := hsum (fun i => mvfderiv MI (p.coeff i) 1 Y) (fun j => q.coeff j 1)
    simp only [p.value, q.value, p.derivative, q.derivative, hone, AlgHom.id_apply] at h₁ h₂
    simp only [mul_comm (q.coeff _ 1) (mvfderiv MI _ 1 Y)]
    rw [h₁, h₂]
    noncomm_ring

private def Expansion.scalar (c : ℂ) : Expansion S α (algebraMap ℂ U c) := by
  refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => algebraMap ℂ U c,
    fun _ => S.one_mem, fun _ => contMDiff_const, ?_, ?_⟩
  · intro g
    simp [AlgHom.commutes]
  · intro Y
    simp only [Finset.univ_unique, Finset.sum_singleton, mvfderiv_const, zero_apply, zero_smul]
    rw [Algebra.commutes, sub_self]

variable [FiniteDimensional ℝ E]

/-- A finite expansion through any scalar subalgebra that contains the adjoint coefficients. -/
private def Expansion.ofGenerator (X : LieAlg) (c : ℂ)
    (hα : ∀ g, α g (gen (c ⊗ₜ[ℝ] X)) = gen (c ⊗ₜ[ℝ] groupTangentConjugation MI g X))
    (hs : ContMDiff (M' := E) MI MI ∞ (fun g => groupTangentConjugation MI g X))
    (hd : ∀ Y : LieAlg, mvfderiv (F := E) MI (fun g => groupTangentConjugation MI g X) 1 Y = ⁅Y, X⁆)
    (hreg : ∀ l : E →ₗ[ℝ] ℝ, (fun g => l (groupTangentConjugation MI g X)) ∈ S) :
    Expansion S α (gen (c ⊗ₜ[ℝ] X)) := by
  let b := Module.finBasis ℝ E
  let k : E →ₗ[ℝ] U := (c • generator : LieAlg →ₗ[ℝ] U)
  let l (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
    { b.coord i with cont := (b.coord i).continuous_of_finiteDimensional }
  let f : G → E := fun g => groupTangentConjugation MI g X
  have hb (Y : E) : ∑ i, b.coord i Y • k (b i) = k Y := by
    simpa only [map_sum, map_smul, Module.Basis.coord_apply] using congrArg k (b.sum_repr Y)
  refine ⟨_, inferInstance, fun i g => l i (f g), fun i => k (b i),
    fun i => hreg (b.coord i), fun i => (l i).contDiff.contMDiff.comp hs, ?_, ?_⟩
  · intro g
    change ∑ i, b.coord i (f g) • k (b i) = _
    rw [hb, hα, gen_tmul]
    rfl
  · intro Y
    have hh (i : Fin (Module.finrank ℝ E)) :
        mvfderiv MI (fun g => l i (f g)) 1 Y = b.coord i (show E from (⁅Y, X⁆ : LieAlg)) := by
      rw [mvfderiv_clm_comp MI (hs.mdifferentiableAt (by simp)), hd]
      rfl
    simp_rw [hh]
    rw [hb, gen_tmul]
    change c • generator ⁅Y, X⁆ = _
    rw [generator_lie, smul_sub, mul_smul_comm, smul_mul_assoc]

private theorem exists_expansion (hone : α 1 = AlgHom.id ℂ U)
    (hα : ∀ (g : G) (c : ℂ) (X : LieAlg),
      α g (gen (c ⊗ₜ[ℝ] X)) = gen (c ⊗ₜ[ℝ] groupTangentConjugation MI g X))
    (hs : ∀ X : LieAlg, ContMDiff (M' := E) MI MI ∞ (fun g => groupTangentConjugation MI g X))
    (hd : ∀ X Y : LieAlg, mvfderiv (F := E) MI (fun g => groupTangentConjugation MI g X) 1 Y = ⁅Y, X⁆)
    (hreg : ∀ (X : LieAlg) (l : E →ₗ[ℝ] ℝ), (fun g => l (groupTangentConjugation MI g X)) ∈ S)
    (a : U) : Nonempty (Expansion S α a) := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ) (UniversalEnvelopingAlgebra.ringCon ℂ LC) a
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes]
    exact ⟨Expansion.scalar S α c⟩
  | «ι» T =>
    change Nonempty (Expansion S α (gen T))
    induction T using TensorProduct.inductionOn with
    | tmul c X => exact ⟨Expansion.ofGenerator S α X c (fun g => hα g c X) (hs X) (hd X) (hreg X)⟩
    | add X Y hX hY =>
      rw [map_add]
      exact ⟨hX.some.add S α hY.some⟩
  | add a b ha hb =>
    rw [map_add]
    exact ⟨ha.some.add S α hb.some⟩
  | mul a b ha hb =>
    rw [map_mul]
    exact ⟨ha.some.mul S α hone hb.some⟩

omit [FiniteDimensional ℝ E] in
/-- A real scalar test against any enveloping element belongs to the coefficient subalgebra. -/
private theorem Expansion.mem_test {a : U} (p : Expansion S α a) (l : U →ₗ[ℝ] ℝ) :
    (fun g => l (α g a)) ∈ S := by
  let := p.finite
  have he : (fun g => l (α g a)) = ∑ i, p.coeff i * algebraMap ℝ (G → ℝ) (l (p.term i)) := by
    funext g
    simp only [← p.value g, map_sum, map_smul, smul_eq_mul, Finset.sum_apply,
      Pi.mul_apply, Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [he]
  exact S.sum_mem fun i _ => S.mul_mem (p.regular i) (S.algebraMap_mem _)

omit [FiniteDimensional ℝ E] in
private theorem Expansion.smooth_test {a : U} (p : Expansion S α a) (l : U →ₗ[ℝ] ℝ) :
    ContMDiff MI 𝓘(ℝ, ℝ) ∞ (fun g => l (α g a)) := by
  let := p.finite
  have he : (fun g => l (α g a)) = fun g => ∑ i, p.coeff i g * l (p.term i) := by
    funext g
    simp [← p.value g, smul_eq_mul]
  rw [he]
  have h (t : Finset p.index) :
      ContMDiff MI 𝓘(ℝ, ℝ) ∞ (fun g => ∑ i ∈ t, p.coeff i g * l (p.term i)) := by
    induction t using Finset.induction_on with
    | empty => simpa using (contMDiff_const (c := (0 : ℝ)))
    | insert i t hi ht =>
      have hi' : ContMDiff MI 𝓘(ℝ, ℝ) ∞ (fun g => p.coeff i g * l (p.term i)) :=
        (p.smooth i).mul contMDiff_const
      convert hi'.add ht using 1
      ext g
      simp [Finset.sum_insert hi]
  exact h Finset.univ

omit [FiniteDimensional ℝ E] in
private theorem Expansion.derivative_test {a : U} (p : Expansion S α a) (l : U →ₗ[ℝ] ℝ)
    (Y : LieAlg) : mvfderiv MI (fun g => l (α g a)) 1 Y = l (generator Y * a - a * generator Y) := by
  let := p.finite
  have he : (fun g => l (α g a)) = fun g => ∑ i, p.coeff i g * l (p.term i) := by
    funext g
    simp [← p.value g, smul_eq_mul]
  rw [he, ← p.derivative Y, map_sum]
  have h (t : Finset p.index) : mvfderiv MI (fun g => ∑ i ∈ t, p.coeff i g * l (p.term i)) 1 Y =
      ∑ i ∈ t, l (mvfderiv MI (p.coeff i) 1 Y • p.term i) := by
    induction t using Finset.induction_on with
    | empty => simp [mvfderiv_const]
    | insert i t hi ht =>
      simp only [Finset.sum_insert hi]
      have hi' (j : p.index) : MDifferentiableAt MI 𝓘(ℝ, ℝ) (fun g => p.coeff j g * l (p.term j)) 1 := by
        have hsm : ContMDiff MI 𝓘(ℝ, ℝ) ∞ (fun g => p.coeff j g * l (p.term j)) :=
          (p.smooth j).mul contMDiff_const
        exact hsm.mdifferentiableAt (by simp)
      have hsum : MDifferentiableAt MI 𝓘(ℝ, ℝ) (fun g => ∑ j ∈ t, p.coeff j g * l (p.term j)) 1 := by
        have he : (∑ j ∈ t, fun g => p.coeff j g * l (p.term j)) =
            (fun g => ∑ j ∈ t, p.coeff j g * l (p.term j)) := by
          funext g
          simp only [Finset.sum_apply]
        rw [← he]
        exact MDifferentiableAt.sum (t := t) (fun j _ => hi' j)
      have hc : MDifferentiableAt MI 𝓘(ℝ, ℝ) (fun _ : G => l (p.term i)) 1 := mdifferentiableAt_const
      rw [mvfderiv_fun_add (hi' i) hsum, add_apply, ht,
        mvfderiv_fun_mul ((p.smooth i).mdifferentiableAt (by simp)) hc]
      simp [mvfderiv_const, mul_comm]
  exact h Finset.univ

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem eventuallyEq_of_zero_derivative (f : G → ℝ)
    (hs : ContMDiff MI 𝓘(ℝ, ℝ) ∞ f) (hd : ∀ x, mvfderiv MI f x = 0) :
    ∀ᶠ x in 𝓝 (1 : G), f x = f 1 := by
  let c := chartAt E (1 : G)
  have hc : (1 : G) ∈ c.source := mem_chart_source E 1
  have ht : c 1 ∈ c.target := c.map_source hc
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp c.open_target (c 1) ht
  let b := Metric.ball (c 1) r
  let f' := f ∘ c.symm
  have hsd (x : E) (hx : x ∈ b) : MDifferentiableAt MI MI c.symm x :=
    mdifferentiableAt_atlas_symm (I := MI) (chart_mem_atlas E (1 : G)) (hsub hx)
  have hfd (x : E) (hx : x ∈ b) : DifferentiableAt ℝ f' x :=
    ((hs.mdifferentiableAt (by simp)).comp x (hsd x hx)).differentiableAt
  have hD (x : E) (hx : x ∈ b) : fderiv ℝ f' x = 0 := by
    have he := mvfderiv_comp (I := MI) (I' := MI) x (hs.mdifferentiableAt (by simp)) (hsd x hx)
    change mvfderiv MI f' x = _ at he
    rw [hd, ContinuousLinearMap.zero_comp] at he
    ext v
    have hv := DFunLike.congr_fun he ((NormedSpace.fromTangentSpace x).symm v)
    simpa only [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using hv
  have hcst (x : E) (hx : x ∈ b) : f' x = f' (c 1) := by
    apply Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
      (fun y hy => (hfd y hy).differentiableWithinAt) hD hx (Metric.mem_ball_self hr)
  filter_upwards [c.open_source.mem_nhds hc,
    (c.continuousAt hc).preimage_mem_nhds (Metric.ball_mem_nhds _ hr)] with x hx hbx
  simpa only [f', Function.comp_apply, c.left_inv hx, c.left_inv hc] using hcst (c x) hbx

/-- Scalar central orbits lie in the coefficient algebra and are constant near the identity. -/
theorem center_test (hone : α 1 = AlgHom.id ℂ U)
    (hmul : ∀ g h, α (g * h) = (α g).comp (α h))
    (hα : ∀ (g : G) (c : ℂ) (X : LieAlg),
      α g (gen (c ⊗ₜ[ℝ] X)) = gen (c ⊗ₜ[ℝ] groupTangentConjugation MI g X))
    (hs : ∀ X : LieAlg, ContMDiff (M' := E) MI MI ∞ (fun g => groupTangentConjugation MI g X))
    (hd : ∀ X Y : LieAlg, mvfderiv (F := E) MI (fun g => groupTangentConjugation MI g X) 1 Y = ⁅Y, X⁆)
    (hreg : ∀ (X : LieAlg) (l : E →ₗ[ℝ] ℝ), (fun g => l (groupTangentConjugation MI g X)) ∈ S)
    (a : U) (ha : a ∈ Subalgebra.center ℂ U) (l : U →ₗ[ℝ] ℝ) :
    (fun g => l (α g a)) ∈ S ∧ ∀ᶠ g in 𝓝 (1 : G), l (α g a) = l a := by
  let p := (exists_expansion S α hone hα hs hd hreg a).some
  let f (g : G) := l (α g a)
  have hsm : ContMDiff MI 𝓘(ℝ, ℝ) ∞ f := p.smooth_test S α l
  have hzero (g : G) : mvfderiv MI f g = 0 := by
    ext V
    let lt : G → G := fun x => g * x
    let li : G → G := fun x => g⁻¹ * x
    have hL (g' : G) : ContMDiff MI MI ∞ (fun x : G => g' * x) := contMDiff_const.mul contMDiff_id
    have hlt : MDifferentiableAt MI MI lt (1 : G) := (hL g).mdifferentiableAt (by simp)
    have hli : MDifferentiableAt MI MI li g := (hL g⁻¹).mdifferentiableAt (by simp)
    let Y : LieAlg := mfderiv MI MI li g V
    have hsurj : mfderiv MI MI lt 1 Y = V := by
      have hcomp := mfderiv_comp_apply_of_eq (I := MI) (I' := MI) (I'' := MI)
        (f := li) (g := lt) g hlt hli (inv_mul_cancel g) V
      have he : lt ∘ li = id := by funext x; simp [lt, li]
      rw [he, mfderiv_id] at hcomp
      exact hcomp.symm
    let l' := l.comp ((α g).toLinearMap.restrictScalars ℝ)
    have hder := p.derivative_test S α l' Y
    have hcomm := Subalgebra.mem_center_iff.mp ha (generator Y)
    rw [hcomm, sub_self, map_zero] at hder
    have he : (fun x => l' (α x a)) = f ∘ lt := by
      funext x
      simp only [l', LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        AlgHom.toLinearMap_apply, f, lt, Function.comp_apply, hmul, AlgHom.comp_apply]
    rw [he, mvfderiv_comp_apply_of_eq (I := MI) (I' := MI) 1
      (hsm.mdifferentiableAt (by simp)) hlt (mul_one g), hsurj] at hder
    exact hder
  refine ⟨p.mem_test S α l, ?_⟩
  simpa only [f, hone, AlgHom.id_apply] using eventuallyEq_of_zero_derivative f hsm hzero

end Langlands.Geometry.Manifold.EnvelopingAdjoint
