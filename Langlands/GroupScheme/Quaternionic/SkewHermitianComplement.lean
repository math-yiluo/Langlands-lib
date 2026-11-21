import Langlands.GroupScheme.Quaternionic.SkewHermitianInducedHermitian
import Langlands.LinearAlgebra.RankSixHyperbolicity

/-! # Complementary subspaces for the rank-three skew-hermitian reduction -/

noncomputable section

universe u v

namespace Langlands.SymmetricBilinear

variable {E : Type u} [Field E] {V : Type v} [AddCommGroup V] [Module E V]

private def isotropicCoordinates : (Fin 3 → E) →ₗ[E] (E × E) × (E × E) × (E × E) where
  toFun x := ((x 0, 0), (x 1, 0), (x 2, 0))
  map_add' x y := by simp
  map_smul' a x := by simp

/-- Three hyperbolic planes contain a three-dimensional totally isotropic subspace. -/
theorem exists_rankThree_totallyIsotropic (C : LinearMap.BilinForm E V)
    (hS : C.IsSymm) (h2 : (2 : E) ≠ 0)
    (hC : (threeHyperbolicPlanes E).Equivalent C.toQuadraticMap) :
    ∃ W : Submodule E V, Module.finrank E W = 3 ∧ ∀ x ∈ W, ∀ y ∈ W, C x y = 0 := by
  obtain ⟨e⟩ := hC
  let f := e.toLinearEquiv.toLinearMap.comp (isotropicCoordinates (E := E))
  have hf : Function.Injective f := by
    intro x y h
    have hxy := e.toLinearEquiv.injective h
    funext i
    fin_cases i
    · exact congrArg (fun z : (E × E) × (E × E) × (E × E) => z.1.1) hxy
    · exact congrArg (fun z : (E × E) × (E × E) × (E × E) => z.2.1.1) hxy
    · exact congrArg (fun z : (E × E) × (E × E) × (E × E) => z.2.2.1) hxy
  refine ⟨LinearMap.range f, (LinearMap.finrank_range_of_inj hf).trans (Module.finrank_fin_fun E), ?_⟩
  have hzero (x : V) (hx : x ∈ LinearMap.range f) : C.toQuadraticMap x = 0 := by
    obtain ⟨a, rfl⟩ := hx
    change C.toQuadraticMap (e (isotropicCoordinates a)) = 0
    rw [e.map_app]
    simp [threeHyperbolicPlanes, QuadraticMap.prod_apply, isotropicCoordinates]
  intro x hx y hy
  have hp : QuadraticMap.polar C.toQuadraticMap x y = 0 := by
    simp only [QuadraticMap.polar, hzero _ ((LinearMap.range f).add_mem hx hy), hzero _ hx,
      hzero _ hy, sub_zero]
  rw [LinearMap.BilinMap.polar_toQuadraticMap, hS.eq y x, ← two_mul] at hp
  exact (mul_eq_zero.mp hp).resolve_left h2

end Langlands.SymmetricBilinear

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  {V : Type v} [AddCommGroup V] [Module D V]

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E

/-- The image of a quadratic-field subspace under the semilinear quaternion generator. -/
def jImage :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    Submodule E V → Submodule E V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : RingHomSurjective (κ).toRingHom := ⟨(κ).surjective⟩
  exact fun W => W.map Q.jAction

/-- Membership in the semilinear image has a preimage in the original subspace. -/
theorem mem_jImage_iff :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ (W : Submodule E V) (x : V), x ∈ Q.jImage W ↔ ∃ y ∈ W, Q.jAction y = x := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : RingHomSurjective (κ).toRingHom := ⟨(κ).surjective⟩
  intro W x
  exact Submodule.mem_map

/-- Semilinear translation preserves dimension. -/
theorem finrank_jImage :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ W : Submodule E V, Module.finrank E (Q.jImage W) = Module.finrank E W := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : RingHomSurjective (κ).toRingHom := ⟨(κ).surjective⟩
  intro W
  let g : W →ₛₗ[(κ).toRingHom] Q.jImage W := Q.jAction.submoduleMap W
  have hg : Function.Bijective g :=
    ⟨LinearMap.submoduleMap_injective (Q.jAction_bijective (V := V)).1 W,
      Q.jAction.submoduleMap_surjective W⟩
  let e := AddEquiv.ofBijective g.toAddMonoidHom hg
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv κ e (κ).bijective g.map_smulₛₗ).symm

/-- Complementarity gives paired coordinates for every vector. -/
theorem exists_add_jAction_of_isCompl :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∀ (W : Submodule E V), IsCompl W (Q.jImage W) →
      ∀ x : V, ∃ u ∈ W, ∃ v ∈ W, x = u + Q.jAction v := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro W h x
  have hx : x ∈ W ⊔ Q.jImage W := by rw [h.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v, hv, rfl⟩ := (Q.mem_jImage_iff W z).mp hz
  exact ⟨u, hu, v, hv, rfl⟩

variable {τ : FirstKindInvolution F D} [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

/-- If the six-dimensional symmetric component is hyperbolic, the skew form is
  isotropic or has a complementary pair of totally isotropic subspaces for that component. -/
theorem exists_skewIsotropic_or_complement (h2 : (2 : E) ≠ 0) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    (threeHyperbolicPlanes E).Equivalent (Q.symmetricComponent B hbar).toQuadraticMap →
    (∃ x : V, x ≠ 0 ∧ B x x = 0) ∨
    ∃ W : Submodule E V, Module.finrank E W = 3 ∧
      (∀ x ∈ W, ∀ y ∈ W, Q.symmetricComponent B hbar x y = 0) ∧ IsCompl W (Q.jImage W) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  intro hC
  obtain ⟨W, hdim, hW⟩ := exists_rankThree_totallyIsotropic (Q.symmetricComponent B hbar)
    ⟨fun x y => Q.symmetricComponent_swap B hbar y x⟩ h2 hC
  by_cases hdisj : Disjoint W (Q.jImage W)
  · obtain ⟨e⟩ := hC
    let : FiniteDimensional E V := e.toLinearEquiv.finiteDimensional
    have hV : Module.finrank E V = 6 := by
      rw [← e.toLinearEquiv.finrank_eq]
      simp [Module.finrank_prod]
    have hsum : Module.finrank E V ≤ Module.finrank E W + Module.finrank E (Q.jImage W) := by
      rw [hV, Q.finrank_jImage, hdim]
    exact Or.inr ⟨W, hdim, hW, (Submodule.isCompl_iff_disjoint _ _ hsum).mpr hdisj⟩
  · left
    rw [disjoint_iff_inf_le] at hdisj
    change ¬ (∀ x : V, x ∈ W ⊓ Q.jImage W → x ∈ (⊥ : Submodule E V)) at hdisj
    push Not at hdisj
    obtain ⟨x, hx, hx0⟩ := hdisj
    exact ⟨x, fun h => hx0 ((Submodule.mem_bot E).mpr h),
      Q.skew_self_eq_zero_of_subspace_intersection B hbar W hW x hx.1
        ((Q.mem_jImage_iff W x).mp hx.2)⟩

end Langlands.GroupScheme.KneserThree.QuatData
