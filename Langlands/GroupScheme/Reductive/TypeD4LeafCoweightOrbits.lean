import Langlands.LinearAlgebra.TypeD4CorootCoordinates
import Langlands.GroupScheme.Reductive.BasedRootDatumProjection

/-! # Based automorphisms permute the Weyl orbits of the D4 leaf coweights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open Langlands.LinearAlgebra

namespace Langlands.LinearAlgebra

/-- The four numbered simple vectors of type `D₄` detect integral vectors by dot products. -/
theorem eq_of_dotProduct_simple_D4 {v v' : Fin 4 → ℤ}
    (h : ∀ m : Fin 4, TypeDNumberedVectors.simple (by decide : 2 ≤ 4) m ⬝ᵥ v =
      TypeDNumberedVectors.simple (by decide : 2 ≤ 4) m ⬝ᵥ v') : v = v' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [TypeDNumberedVectors.simple, dotProduct, Fin.sum_univ_four] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  funext j
  fin_cases j <;> simp <;> omega

section BasedRootDatum

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum I X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (e : b.support ≃ Fin 4)
    (hD : ∀ i j : b.support, P.pairing i.val j.val = CartanMatrix.D 4 (e i) (e j))
    [Finite I] [P.IsReduced]

include hspan hD in
/-- In a simply connected `D₄` datum, the pairings with the simple roots determine a
cocharacter. -/
theorem eq_of_root'_simple_eq_D4 {y y' : Y}
    (h : ∀ j : b.support, P.root' j.val y = P.root' j.val y') : y = y' := by
  apply d4CorootCoordinates_injective P b hspan e
  apply eq_of_dotProduct_simple_D4
  intro m
  have hm := h (e.symm m)
  rw [← d4CorootCoordinates_dotProduct_coroot P b hspan e hD,
    ← d4CorootCoordinates_dotProduct_coroot P b hspan e hD,
    d4CorootCoordinates_simple, Equiv.apply_symm_apply] at hm
  exact hm

omit [Finite I] [P.IsReduced] in
/-- Pairing a root with the coweight transform of an automorphism. -/
theorem root'_coweightEquiv (x : P.Aut) (i : I) (y : Y) :
    P.root' i (x.coweightEquiv y) = P.root' (x.indexEquiv i) y := by
  have h1 := LinearMap.congr_fun
    (RootPairing.Hom.weight_coweight_transpose_apply P P y x.toHom) (P.root i)
  simp only [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap,
    LinearMap.flip_apply, RootPairing.Hom.root_weightMap_apply] at h1
  exact h1.symm

omit [Finite I] [P.IsReduced] in
theorem coweightEquiv_mul_apply (x y : P.Aut) (v : Y) :
    (x * y).coweightEquiv v = y.coweightEquiv (x.coweightEquiv v) := by
  simp

omit [Finite I] [P.IsReduced] in
/-- Conjugating a reflection by an automorphism gives the reflection at the transported root. -/
theorem conjugate_reflection_aut (δ : P.Aut) (i : I) :
    δ * RootPairing.Equiv.reflection P i * δ⁻¹ =
      RootPairing.Equiv.reflection P (δ.indexEquiv i) := by
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  change δ.weightEquiv (P.reflection i (δ.weightEquiv.symm x)) = P.reflection (δ.indexEquiv i) x
  rw [δ.weightEquiv_reflection, LinearEquiv.apply_symm_apply]

omit [Finite I] [P.IsReduced] in
/-- The integral Weyl group is normal in the automorphism group. -/
theorem conjugate_mem_weylGroup_aut (δ w : P.Aut) (hw : w ∈ P.weylGroup) :
    δ * w * δ⁻¹ ∈ P.weylGroup := by
  induction hw using RootPairing.weylGroup.induction with
  | mem i =>
    rw [conjugate_reflection_aut]
    exact P.reflection_mem_weylGroup _
  | one => simp
  | mul a b ha hb ia ib =>
    have he : δ * (a * b) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹) := by group
    rw [he]
    exact P.weylGroup.mul_mem ia ib

include hspan hD in
/-- A based automorphism carrying the leaf of one parabolic cocharacter to the leaf of
another carries the Weyl orbit of the first onto the Weyl orbit of the second, through the
inverse coweight action. -/
theorem exists_weyl_inv_coweightEquiv_leafParabolicCoweights (x : P.Aut)
    (hx : ∀ a, a ∈ b.support ↔ x.indexEquiv a ∈ b.support) (k k' : Fin 3)
    (hk : x.indexEquiv (e.symm (d4LeafParabolicVertex k)).val =
      (e.symm (d4LeafParabolicVertex k')).val) :
    ∃ w : P.Aut, w ∈ P.weylGroup ∧
      (x⁻¹).coweightEquiv (d4LeafParabolicCoweights P b e k) =
        w.coweightEquiv (d4LeafParabolicCoweights P b e k') := by
  obtain ⟨θ, hθ, hθp⟩ := exists_weyl_d4LeafParabolicCoweights_pairing P b hspan e hD k
  obtain ⟨θ', hθ', hθ'p⟩ := exists_weyl_d4LeafParabolicCoweights_pairing P b hspan e hD k'
  set μ := θ.coweightEquiv (d4LeafParabolicCoweights P b e k) with hμdef
  set μ' := θ'.coweightEquiv (d4LeafParabolicCoweights P b e k') with hμ'def
  have hμ : (x⁻¹).coweightEquiv μ = μ' := by
    apply eq_of_root'_simple_eq_D4 P b hspan e hD
    intro j
    rw [root'_coweightEquiv, hθ'p j]
    have hj : (x⁻¹).indexEquiv j.val ∈ b.support := by
      rw [hx]
      change x.indexEquiv (x.indexEquiv.symm j.val) ∈ b.support
      rw [Equiv.apply_symm_apply]
      exact j.property
    rw [show (x⁻¹).indexEquiv j.val = (⟨(x⁻¹).indexEquiv j.val, hj⟩ : b.support).val from rfl,
      hθp]
    congr 1
    apply propext
    constructor
    · intro h
      have h' : (⟨(x⁻¹).indexEquiv j.val, hj⟩ : b.support) = e.symm (d4LeafParabolicVertex k) :=
        (Equiv.eq_symm_apply e).mpr h
      have h'' := congrArg Subtype.val h'
      change x.indexEquiv.symm j.val = _ at h''
      have h3 : j.val = (e.symm (d4LeafParabolicVertex k')).val := by
        rw [← hk, ← h'', Equiv.apply_symm_apply]
      rw [show j = e.symm (d4LeafParabolicVertex k') from Subtype.ext h3, Equiv.apply_symm_apply]
    · intro h
      have h' : j = e.symm (d4LeafParabolicVertex k') := (Equiv.eq_symm_apply e).mpr h
      have h3 : (⟨(x⁻¹).indexEquiv j.val, hj⟩ : b.support) = e.symm (d4LeafParabolicVertex k) := by
        apply Subtype.ext
        change x.indexEquiv.symm j.val = _
        rw [h', ← hk, Equiv.symm_apply_apply]
      rw [h3, Equiv.apply_symm_apply]
  have hθinv : d4LeafParabolicCoweights P b e k = (θ⁻¹).coweightEquiv μ := by
    rw [hμdef, ← coweightEquiv_mul_apply, mul_inv_cancel]
    rfl
  refine ⟨θ' * (x * θ⁻¹ * x⁻¹), P.weylGroup.mul_mem hθ'
    (conjugate_mem_weylGroup_aut P x θ⁻¹ (P.weylGroup.inv_mem hθ)), ?_⟩
  rw [coweightEquiv_mul_apply, ← hμ'def, ← hμ, ← coweightEquiv_mul_apply, hθinv,
    ← coweightEquiv_mul_apply]
  congr 2
  group

end BasedRootDatum

end Langlands.LinearAlgebra
