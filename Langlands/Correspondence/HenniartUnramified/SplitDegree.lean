import Langlands.Weil.Local.DegreeCharacters
import Langlands.Weil.Representation.InductionContinuity
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Weil.Representation.Twist
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.Invariants

/-! # Representations across a split integer quotient -/

noncomputable section

namespace Langlands.FiniteRepresentation

universe uG uV uU

/-- A continuous integer degree with a lift of the positive generator. -/
structure SplitDegree (G : Type uG) [Group G] [TopologicalSpace G] where
  degree : G →ₜ* Multiplicative ℤ
  lift : G
  lift_degree : degree lift = Multiplicative.ofAdd (1 : ℤ)

namespace SplitDegree

open Representation LinearMap

variable {G : Type uG} [Group G] [TopologicalSpace G] (D : SplitDegree G)

abbrev inertia : Subgroup G := D.degree.toMonoidHom.ker

abbrev intDegree (g : G) : ℤ := (D.degree g).toAdd

theorem degree_zpow_lift (m : ℤ) : D.degree (D.lift ^ m) = Multiplicative.ofAdd m := by
  rw [map_zpow, D.lift_degree, ← ofAdd_zsmul, zsmul_eq_mul, mul_one, Int.cast_id]

/-- The degree-zero factor in the normal form `g = n * lift^deg(g)`. -/
def factor (g : G) : D.inertia :=
  ⟨g * (D.lift ^ D.intDegree g)⁻¹, by
    change D.degree (g * (D.lift ^ D.intDegree g)⁻¹) = 1
    rw [map_mul, map_inv, D.degree_zpow_lift, ofAdd_toAdd, mul_inv_cancel]⟩

@[simp] theorem factor_mul (g : G) : (D.factor g : G) * D.lift ^ D.intDegree g = g := by
  change g * (D.lift ^ D.intDegree g)⁻¹ * D.lift ^ D.intDegree g = g
  group

/-- Conjugation on inertia by powers of the chosen lift. -/
def conjugation : Multiplicative ℤ →* MulAut D.inertia :=
  MulAut.conjNormal.comp (zpowersHom G D.lift)

/-- The normal form as an isomorphism from the semidirect product. -/
def mulEquiv : (D.inertia ⋊[D.conjugation] (Multiplicative ℤ)) ≃* G := by
  let L : (D.inertia ⋊[D.conjugation] (Multiplicative ℤ)) →* G :=
    SemidirectProduct.lift D.inertia.subtype (zpowersHom G D.lift) (fun m => by
      ext n
      rfl)
  have hL (x : D.inertia ⋊[D.conjugation] (Multiplicative ℤ)) :
      D.degree (L x) = x.right := by
    change D.degree (x.left.val * D.lift ^ x.right.toAdd) = _
    rw [map_mul, D.degree_zpow_lift, show D.degree x.left.val = 1 from x.left.property, one_mul,
      ofAdd_toAdd]
  refine MulEquiv.ofBijective L ⟨?_, fun g => ⟨⟨D.factor g, D.degree g⟩, D.factor_mul g⟩⟩
  intro x y h
  have hr : x.right = y.right := (hL x).symm.trans ((congrArg D.degree h).trans (hL y))
  apply SemidirectProduct.ext _ hr
  apply Subtype.ext
  change x.left.val * D.lift ^ x.right.toAdd = y.left.val * D.lift ^ y.right.toAdd at h
  rw [hr] at h
  exact mul_right_cancel h

@[simp] theorem mulEquiv_symm_left (g : G) : (D.mulEquiv.symm g).left = D.factor g := by
  have h : D.mulEquiv ⟨D.factor g, D.degree g⟩ = g := D.factor_mul g
  exact congrArg SemidirectProduct.left ((D.mulEquiv.symm_apply_eq).mpr h.symm)

@[simp] theorem mulEquiv_symm_right (g : G) : (D.mulEquiv.symm g).right = D.degree g := by
  have h : D.mulEquiv ⟨D.factor g, D.degree g⟩ = g := D.factor_mul g
  exact congrArg SemidirectProduct.right ((D.mulEquiv.symm_apply_eq).mpr h.symm)

section Extend

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ D.inertia V)

private def compatibleConjugations : Subgroup (MulAut D.inertia × (Module.End ℂ V)ˣ) where
  carrier := {a | ∀ n : D.inertia, ρ.asGroupHom (a.1 n) =
    a.2 * ρ.asGroupHom n * a.2⁻¹}
  one_mem' := by intro n; simp
  mul_mem' {a b} ha hb := by
    intro n
    change ρ.asGroupHom (a.1 (b.1 n)) = (a.2 * b.2) * ρ.asGroupHom n * (a.2 * b.2)⁻¹
    have h₁ := ha (b.1 n)
    have h₂ := hb n
    rw [h₁, h₂]
    group
  inv_mem' {a} ha := by
    intro n
    have h : ρ.asGroupHom (a.1 (a.1⁻¹ n)) = a.2 * ρ.asGroupHom (a.1⁻¹ n) * a.2⁻¹ := ha (a.1⁻¹ n)
    rw [MulAut.apply_inv_self] at h
    change ρ.asGroupHom (a.1⁻¹ n) = a.2⁻¹ * ρ.asGroupHom n * a.2⁻¹⁻¹
    rw [h]
    group

/-- Extend an actual inertia representation from an invertible intertwiner for the lift. -/
def extend (U : (Module.End ℂ V)ˣ)
    (hU : ∀ n : D.inertia, ρ.asGroupHom (MulAut.conjNormal D.lift n) =
      U * ρ.asGroupHom n * U⁻¹) : Representation ℂ G V := by
  let f : (D.inertia ⋊[D.conjugation] (Multiplicative ℤ)) →* (Module.End ℂ V)ˣ :=
    SemidirectProduct.lift ρ.asGroupHom (zpowersHom _ U) (fun m => by
      ext n : 1
      have hp := (compatibleConjugations D ρ).zpow_mem
        (show (MulAut.conjNormal D.lift, U) ∈ compatibleConjugations D ρ from hU) m.toAdd
      have h := hp n
      change ρ.asGroupHom ((MulAut.conjNormal D.lift ^ m.toAdd) n) =
        U ^ m.toAdd * ρ.asGroupHom n * (U ^ m.toAdd)⁻¹ at h
      change ρ.asGroupHom (MulAut.conjNormal (D.lift ^ m.toAdd) n) = _
      rw [map_zpow]
      exact h)
  exact (Units.coeHom _).comp (f.comp D.mulEquiv.symm.toMonoidHom)

@[simp] theorem extend_apply (U : (Module.End ℂ V)ˣ) (hU) (g : G) :
    D.extend ρ U hU g = ρ (D.factor g) * ((U ^ D.intDegree g : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
  change (ρ.asGroupHom (D.mulEquiv.symm g).left * U ^ (D.mulEquiv.symm g).right.toAdd :
    (Module.End ℂ V)ˣ).val = _
  rw [mulEquiv_symm_left, mulEquiv_symm_right]
  rfl

@[simp] theorem extend_on_inertia (U : (Module.End ℂ V)ˣ) (hU) (n : D.inertia) :
    D.extend ρ U hU n = ρ n := by
  have h0 : D.intDegree n = 0 := congrArg Multiplicative.toAdd n.property
  have hf : D.factor n = n := Subtype.ext (by simp [factor, h0])
  simp [h0, hf]

/-- On an open inertia subgroup, a continuous action extends continuously. -/
theorem continuous_extend [IsTopologicalGroup G] [FiniteDimensional ℂ V]
    (hρ : (FiniteRepresentation.of ρ).IsContinuous) (U : (Module.End ℂ V)ˣ) (hU) :
    (FiniteRepresentation.of (D.extend ρ U hU)).IsContinuous := by
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  have : IsModuleTopology ℂ (Module.End ℂ V) := ⟨rfl⟩
  have : IsTopologicalRing (Module.End ℂ V) := IsModuleTopology.isTopologicalRing ℂ _
  have ht : Continuous (fun g : G => D.lift ^ D.intDegree g) :=
    (continuous_of_discreteTopology (f := fun m : Multiplicative ℤ => D.lift ^ m.toAdd)).comp
      D.degree.continuous
  have hn : Continuous D.factor := (continuous_id.mul ht.inv).subtype_mk _
  have hU' : Continuous (fun g : G => ((U ^ D.intDegree g : (Module.End ℂ V)ˣ) : Module.End ℂ V)) :=
    (continuous_of_discreteTopology (f := fun m : Multiplicative ℤ =>
      ((U ^ m.toAdd : (Module.End ℂ V)ˣ) : Module.End ℂ V))).comp D.degree.continuous
  change Continuous (D.extend ρ U hU)
  exact (((show Continuous ρ from hρ).comp hn).mul hU').congr (fun g => (D.extend_apply ρ U hU g).symm)

/-- An isomorphism to the Frobenius-conjugate action supplies the extension operator. -/
theorem exists_compatibleOperator
    (e : ρ.Equiv (ρ.comp (MulAut.conjNormal D.lift).toMonoidHom)) :
    ∃ U : (Module.End ℂ V)ˣ, ∀ n : D.inertia, ρ.asGroupHom (MulAut.conjNormal D.lift n) =
      U * ρ.asGroupHom n * U⁻¹ := by
  let U := GeneralLinearGroup.ofLinearEquiv e.toLinearEquiv
  refine ⟨U, fun n => ?_⟩
  apply Units.ext
  have h := e.isIntertwining' n
  change U.val * ρ n = ρ (MulAut.conjNormal D.lift n) * U.val at h
  change ρ (MulAut.conjNormal D.lift n) = U.val * ρ n * U.inv
  rw [h, mul_assoc, U.val_inv, mul_one]

end Extend

section Hom

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G U)

private def fixing (f : V →ₗ[ℂ] U) : Subgroup G where
  carrier := {g | linHom ρ σ g f = f}
  one_mem' := by
    change linHom ρ σ 1 f = f
    rw [map_one, Module.End.one_apply]
  mul_mem' {g h} hg hh := by
    change linHom ρ σ (g * h) f = f
    rw [map_mul, Module.End.mul_apply, show linHom ρ σ h f = f from hh]
    exact hg
  inv_mem' {g} hg := by
    change linHom ρ σ g⁻¹ f = f
    rw [← show linHom ρ σ g f = f from hg, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
    exact (show linHom ρ σ g f = f from hg).symm

/-- Intertwining on inertia and on the chosen lift implies intertwining on the whole group. -/
theorem intertwines_of_inertia_and_lift (f : V →ₗ[ℂ] U)
    (hN : ∀ n : D.inertia, f ∘ₗ ρ n = σ n ∘ₗ f)
    (hT : f ∘ₗ ρ D.lift = σ D.lift ∘ₗ f) :
    ∀ g : G, f ∘ₗ ρ g = σ g ∘ₗ f := by
  have iff_fix (g : G) : g ∈ fixing ρ σ f ↔ f ∘ₗ ρ g = σ g ∘ₗ f := by
    change linHom ρ σ g f = f ↔ _
    rw [linHom_apply]
    constructor
    · intro h
      ext v
      have hv := LinearMap.congr_fun h (ρ g v)
      simp only [LinearMap.comp_apply, Representation.inv_self_apply] at hv
      exact hv.symm
    · intro h
      ext v
      have hv := LinearMap.congr_fun h (ρ g⁻¹ v)
      simp only [LinearMap.comp_apply, Representation.self_inv_apply] at hv
      simp only [LinearMap.comp_apply]
      exact hv.symm
  intro g
  apply (iff_fix g).mp
  rw [← D.factor_mul g]
  exact (fixing ρ σ f).mul_mem ((iff_fix _).mpr (hN (D.factor g)))
    ((fixing ρ σ f).zpow_mem ((iff_fix _).mpr hT) _)

/-- A nonzero inertia intertwiner yields a nonzero whole-group intertwiner
from an unramified twist. No irreducibility of either representation is needed here. -/
theorem exists_twisted_intertwiner [FiniteDimensional ℂ V] [FiniteDimensional ℂ U]
    (h : ∃ f : Representation.IntertwiningMap (ρ.comp D.inertia.subtype)
      (σ.comp D.inertia.subtype), f ≠ 0) :
    ∃ z : ℂˣ, ∃ f : Representation.IntertwiningMap
        (Langlands.twist (Weil.Local.unramifiedCharacter D.degree z).toMonoidHom ρ) σ,
        f ≠ 0 := by
  let S := Representation.invariants ((linHom ρ σ).comp D.inertia.subtype)
  obtain ⟨F, hF⟩ := h
  let f : S := ⟨F.toLinearMap, (mem_linHom_invariants_iff_isIntertwining F.toLinearMap).mpr
    ⟨F.isIntertwining⟩⟩
  have hf : f ≠ 0 := fun h => hF (IntertwiningMap.ext (congrArg Subtype.val h))
  let : Nontrivial S := ⟨⟨f, 0, hf⟩⟩
  let C : Module.End ℂ S := (linHom ρ σ D.lift).restrict (fun l hl => by
    intro n
    change linHom ρ σ n (linHom ρ σ D.lift l) = linHom ρ σ D.lift l
    have hl' : linHom ρ σ (MulAut.conjNormal D.lift⁻¹ n : D.inertia) l = l :=
      hl (MulAut.conjNormal D.lift⁻¹ n)
    have heq : (n : G) * D.lift = D.lift * (MulAut.conjNormal D.lift⁻¹ n : D.inertia) := by
      rw [MulAut.conjNormal_apply, inv_inv]
      group
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply, hl'])
  obtain ⟨c, hc⟩ := C.exists_eigenvalue
  obtain ⟨l, hl⟩ := hc.exists_hasEigenvector
  have hl0 : l.val ≠ 0 := fun h0 => hl.2 (Subtype.ext h0)
  have hcl : linHom ρ σ D.lift l.val = c • l.val := congrArg Subtype.val hl.apply_eq_smul
  have hc0 : c ≠ 0 := by
    intro hz
    apply hl0
    have hf' := congrArg (linHom ρ σ D.lift⁻¹) hcl
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, hz, zero_smul, map_zero] at hf'
  let z := Units.mk0 c hc0
  let χ := (Weil.Local.unramifiedCharacter D.degree z).toMonoidHom
  have hχN (n : D.inertia) : χ n = 1 := Weil.Local.unramifiedCharacter_on_kernel _ _ n.property
  have hχT : χ D.lift = z := Weil.Local.unramifiedCharacter_degree_one _ _ D.lift_degree
  let ρ' := Langlands.twist χ ρ
  have hlI : ∀ n : D.inertia, l.val ∘ₗ ρ n = σ n ∘ₗ l.val := by
    intro n
    have h : linHom ρ σ (n : G) l.val = l.val := l.property n
    ext v
    have hv := LinearMap.congr_fun h (ρ n v)
    rw [linHom_apply] at hv
    simp only [LinearMap.comp_apply, Representation.inv_self_apply] at hv
    simp only [LinearMap.comp_apply]
    exact hv.symm
  refine ⟨z, ⟨l.val, D.intertwines_of_inertia_and_lift ρ' σ l.val ?_ ?_⟩,
    fun h0 => hl0 (congrArg IntertwiningMap.toLinearMap h0)⟩
  · intro n
    change l.val ∘ₗ ((χ n : ℂ) • ρ n) = σ n ∘ₗ l.val
    rw [hχN, Units.val_one, one_smul]
    exact hlI n
  · ext v
    have hv := LinearMap.congr_fun hcl (ρ D.lift v)
    rw [linHom_apply] at hv
    simp only [LinearMap.comp_apply, Representation.inv_self_apply, LinearMap.smul_apply] at hv
    change l.val ((χ D.lift : ℂ) • ρ D.lift v) = σ D.lift (l.val v)
    rw [hχT, map_smul, hv]
    rfl

end Hom

end SplitDegree
end Langlands.FiniteRepresentation
