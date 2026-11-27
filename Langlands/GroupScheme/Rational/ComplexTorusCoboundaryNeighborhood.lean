import Langlands.GroupScheme.AffinePointTopologicalGroup
import Langlands.GroupScheme.Torus.SplitPointTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Group.Units

/-! # Coboundaries near the identity of a complex torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

private def complexUnitSqrt (x : ℂˣ) : ℂˣ :=
  Units.mk0 ((x : ℂ) ^ (1 / 2 : ℂ)) (Complex.cpow_ne_zero_iff.mpr (Or.inl x.ne_zero))

private theorem complexUnitSqrt_one : complexUnitSqrt 1 = 1 := by
  apply Units.ext
  change (1 : ℂ) ^ (1 / 2 : ℂ) = 1
  exact Complex.one_cpow _

private theorem complexUnitSqrt_sq (x : ℂˣ) : complexUnitSqrt x ^ 2 = x := by
  apply Units.ext
  change (((x : ℂ) ^ (1 / 2 : ℂ)) ^ (2 : ℕ)) = (x : ℂ)
  rw [← Complex.cpow_mul_nat, show (1 / 2 : ℂ) * (2 : ℕ) = 1 by norm_num, Complex.cpow_one]

private theorem continuousAt_complexUnitSqrt_one : ContinuousAt complexUnitSqrt 1 := by
  apply Units.isEmbedding_val₀.isInducing.continuousAt_iff.mpr
  change ContinuousAt (fun x : ℂˣ => (x : ℂ) ^ (1 / 2 : ℂ)) 1
  have h : ContinuousAt (fun x : ℂ => x ^ (1 / 2 : ℂ)) 1 :=
    continuousAt_cpow_const (by simp [Complex.mem_slitPlane_iff])
  exact h.comp_of_eq (Units.isEmbedding_val₀.continuous.continuousAt (x := (1 : ℂˣ))) rfl

private theorem exists_open_complexUnits_coboundary {I : Type u} [Finite I]
    (σ : (I → ℂˣ) →* (I → ℂˣ)) (hσ : Continuous σ) :
    ∃ U : Set (I → ℂˣ), IsOpen U ∧ 1 ∈ U ∧
      ∀ x ∈ U, x * σ x = 1 → ∃ a, x = a * (σ a)⁻¹ := by
  let root (x : I → ℂˣ) (i : I) := complexUnitSqrt (x i)
  have hr₁ : root 1 = 1 := funext fun _ => complexUnitSqrt_one
  have hr₂ (x : I → ℂˣ) : root x ^ 2 = x := funext fun i => complexUnitSqrt_sq (x i)
  have hc : ContinuousAt root 1 :=
    continuousAt_pi.mpr fun i =>
      continuousAt_complexUnitSqrt_one.comp_of_eq
        ((continuous_apply i).continuousAt (x := (1 : I → ℂˣ))) rfl
  let normRoot (x : I → ℂˣ) := root x * σ (root x)
  have hnorm₁ : normRoot 1 = 1 := by simp only [normRoot, hr₁, map_one, mul_one]
  have hn : ContinuousAt normRoot 1 := hc.mul (hσ.continuousAt.comp hc)
  let W : Set (I → ℂˣ) := Set.pi Set.univ (fun _ => {(-1 : ℂˣ)}ᶜ)
  have hW : IsOpen W :=
    isOpen_set_pi Set.finite_univ fun _ _ => isClosed_singleton.isOpen_compl
  have hW₁ : (1 : I → ℂˣ) ∈ W := by
    intro i _
    change (1 : ℂˣ) ≠ -1
    intro h
    have hh := congrArg (fun z : ℂˣ => (z : ℂ)) h
    norm_num at hh
  have hsep (y : I → ℂˣ) (hy : y ∈ W) (h : y ^ 2 = 1) : y = 1 := by
    funext i
    apply Units.ext
    have hi := congrArg (fun z : I → ℂˣ => (z i : ℂ)) h
    change (y i : ℂ) ^ 2 = 1 at hi
    rcases sq_eq_one_iff.mp hi with h₁ | h₂
    · exact h₁
    · exact False.elim (hy i (Set.mem_univ _) (Units.ext h₂))
  have hm : normRoot ⁻¹' W ∈ 𝓝 (1 : I → ℂˣ) :=
    hn.preimage_mem_nhds (hW.mem_nhds (hnorm₁.symm ▸ hW₁))
  obtain ⟨U, hU, hUo, hU₁⟩ := mem_nhds_iff.mp hm
  refine ⟨U, hUo, hU₁, fun x hx h => ⟨root x, ?_⟩⟩
  have hn₂ : normRoot x ^ 2 = 1 := by
    change (root x * σ (root x)) ^ 2 = 1
    rw [mul_pow, ← map_pow, hr₂, h]
  have hh := hsep (normRoot x) (hU hx) hn₂
  change root x * σ (root x) = 1 at hh
  rw [← inv_eq_of_mul_eq_one_right hh, inv_inv, ← pow_two, hr₂]

section Torus

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  (T : CommGroupScheme (Spec (CommRingCat.of K)))

local instance coboundaryAffinePointTopology (G : GroupScheme (Spec (CommRingCat.of K))) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of K K)) :=
  G.affinePointsTopologicalSpace _

/-- A norm-one coefficient point sufficiently near the identity of a split
torus over a field topologically isomorphic to `ℂ` is a coboundary. -/
theorem exists_torusPoint_coboundaryNeighborhood (hT : IsSplitTorus T.toGrp)
    (e : K ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (σ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of K K) →*
      GroupScheme.affinePoints T.toGrp (CommAlgCat.of K K))
    (hσ : Continuous σ) :
    ∃ U : Set (GroupScheme.affinePoints T.toGrp (CommAlgCat.of K K)), IsOpen U ∧ 1 ∈ U ∧
      ∀ x ∈ U, x * σ x = 1 → ∃ a, x = a * (σ a)⁻¹ := by
  obtain ⟨I, hI, ⟨s⟩⟩ := hT
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let A := CommAlgCat.of K K
  let f : K ≃ₜ* ℂ := ⟨e.toMulEquiv, he, he'⟩
  let g := Units.mapContinuousMulEquiv f
  let gI : (I → Kˣ) ≃ₜ* (I → ℂˣ) :=
    { toMulEquiv := MulEquiv.piCongrRight fun _ => g.toMulEquiv
      continuous_toFun := continuous_pi fun i => g.continuous.comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i => g.symm.continuous.comp (continuous_apply i) }
  let s₀ : GroupScheme.affinePoints T.toGrp A ≃ₜ*
      GroupScheme.affinePoints (splitTorus (Spec (CommRingCat.of K)) I) A :=
    { toEquiv := (affinePointsIsoHomeomorph s A).toEquiv
      map_mul' := affinePointsIsoHomeomorph_map_mul s A
      continuous_toFun := (affinePointsIsoHomeomorph s A).continuous
      continuous_invFun := (affinePointsIsoHomeomorph s A).symm.continuous }
  let h := s₀.trans ((splitTorus.affinePointsHomeomorph I (CommRingCat.of K) A).trans gI)
  let θ := h.toMulEquiv.toMonoidHom.comp (σ.comp h.symm.toMulEquiv.toMonoidHom)
  have hθ : Continuous θ := h.continuous.comp (hσ.comp h.symm.continuous)
  obtain ⟨V, hV, hV₁, hc⟩ := exists_open_complexUnits_coboundary θ hθ
  refine ⟨h ⁻¹' V, hV.preimage h.continuous, ?_, fun x hx hxnorm => ?_⟩
  · change h 1 ∈ V
    rwa [map_one h]
  have hnat (a : GroupScheme.affinePoints T.toGrp A) : θ (h a) = h (σ a) := by
    change h (σ (h.symm (h a))) = h (σ a)
    rw [h.symm_apply_apply]
  have hxθ : h x * θ (h x) = 1 := by rw [hnat, ← map_mul h, hxnorm, map_one h]
  obtain ⟨v, hv⟩ := hc (h x) hx hxθ
  obtain ⟨a, rfl⟩ := h.surjective v
  refine ⟨a, h.injective ?_⟩
  rw [hv, hnat, map_mul, map_inv]

end Torus

end Langlands.GroupScheme
