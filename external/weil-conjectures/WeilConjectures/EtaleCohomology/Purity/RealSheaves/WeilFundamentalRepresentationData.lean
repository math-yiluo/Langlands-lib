/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric

/-!
# The Weil group data of base point data

For base point data `B` of a Weil group `W` (`AlgebraicGeometry.WeilGroup.BasePointData`), the
homotopy exact sequence identifies `π₁(C, t)` with the geometric part of `W`
(`AlgebraicGeometry.WeilGroup.BasePointData.geomEquiv`), and the path `β : F_t ≅ F_{t ≫ Fr}`
gives a lift of the Frobenius of degree one
(`AlgebraicGeometry.WeilGroup.BasePointData.frobLift`) whose conjugation is the transport of
loops along `Fr` and `β`. These are the input
`AlgebraicGeometry.WeilGroup.WeilMonodromyData` of the Weil fundamental representation
(`AlgebraicGeometry.WeilGroup.BasePointData.weilMonodromyData`). Moreover the local Frobenius
loops at closed points give elements of `W` conjugate to the local Frobenius elements
(`AlgebraicGeometry.WeilGroup.BasePointData.isConj_frobenius`).
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup.BasePointData

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))} (B : BasePointData W)

/-- The lift of the Frobenius in the Weil group attached to the path `β : F_t ≅ F_{t ≫ Fr}`. -/
noncomputable def frobLift : W.carrier :=
  haveI := W.geometricallyConnected
  W.weilGroupEquiv.symm ⟨(B.frobAut, Multiplicative.ofAdd 1), B.mem_weilGroup_frobAut⟩

/-- The image of the Frobenius lift in `π₁(C₀, s) × ℤ` is `(frobAut, 1)`. -/
lemma weilGroupEquiv_frobLift :
    haveI := W.geometricallyConnected
    (W.weilGroupEquiv B.frobLift : W.fundamentalGroup × Multiplicative ℤ) =
      (B.frobAut, Multiplicative.ofAdd 1) := by
  simp [frobLift]

/-- The lift of the Frobenius has degree one. -/
lemma deg_frobLift : W.deg B.frobLift = Multiplicative.ofAdd 1 := by
  rw [W.deg_eq]
  exact congrArg Prod.snd (B.weilGroupEquiv_frobLift)

/-- An element of the Weil group is determined by its image in `π₁(C₀, s) × ℤ`. -/
lemma weilGroupEquiv_injective {a b : W.carrier}
    (h : haveI := W.geometricallyConnected
      (W.weilGroupEquiv a : W.fundamentalGroup × Multiplicative ℤ) = W.weilGroupEquiv b) :
    a = b :=
  W.weilGroupEquiv.injective (Subtype.ext h)

/-- The data of the Weil fundamental representation at the base point data `B`. -/
noncomputable def weilMonodromyData : WeilMonodromyData B where
  geomEquiv := B.geomEquiv
  frobLift := B.frobLift
  deg_frobLift := B.deg_frobLift
  geomEquiv_conj g := by
    have := W.geometricallyConnected
    apply weilGroupEquiv_injective
    simp only [geomEquiv_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      weilGroupEquiv_geomHom, weilGroupEquiv_frobLift, Prod.mk_mul_mk, Prod.inv_mk,
      B.geomAut_frobConj]
    simp

/-- **The local Frobenius loop gives a local Frobenius element.** For a closed point `x` of degree
`m` and a path `π : F_x̄ ≅ F_t`, the element `γᵐ θ(h)` of the Weil group, `h` the loop
`frobeniusLoop x π` followed by `β_m⁻¹`, is conjugate to the local Frobenius `W.frobenius x`:
both are Frobenius elements at `x`. -/
theorem isConj_frobenius (x : C.finitePoints)
    (π : fiber ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    IsConj (W.frobenius x) (B.frobLift ^ (C ↘ Spec (.of K)).degreeOver x.1 *
      B.geomHom (.of (B.frobeniusLoop x π ≪≫ (B.frobPathPow _).symm))) := by
  have := W.geometricallyConnected
  have := W.connectedSpace
  have : Finite (C.residueField x.1) := x.2
  have hg : (W.weilGroupEquiv (B.frobLift ^ (C ↘ Spec (.of K)).degreeOver x.1 *
      B.geomHom (.of (B.frobeniusLoop x π ≪≫ (B.frobPathPow _).symm))) :
        W.fundamentalGroup × Multiplicative ℤ) =
      (B.downAut (B.frobeniusLoop x π) (B.frobeniusLoop_comp_geometricFiberProj x),
        Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ)) := by
    rw [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, weilGroupEquiv_frobLift,
      weilGroupEquiv_geomHom, B.downAut_eq_mul_geomAut _ (B.frobPathPow _), B.downAut_frobPathPow]
    ext
    · simp
    · simp only [Prod.pow_mk, Prod.mk_mul_mk, mul_one]
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  obtain ⟨c, n, hc, hconj⟩ := (W.isFrobeniusElement_frobenius x).exists_mem_weilGroup_conj
    (C ↘ Spec (.of K)) W.basePoint W.fundamentalGroup (B.isFrobeniusElement_downAut x π)
  refine isConj_iff.2 ⟨W.weilGroupEquiv.symm ⟨(c, n), hc⟩, weilGroupEquiv_injective ?_⟩
  rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv]
  have hdeg := W.deg_frobenius x
  rw [W.deg_eq] at hdeg
  have hdeg' : (W.weilGroupEquiv (W.frobenius x) : W.fundamentalGroup × Multiplicative ℤ).2 =
      Multiplicative.ofAdd ((C ↘ Spec (.of K)).degreeOver x.1 : ℤ) := hdeg
  ext
  · rw [← hconj]
    rfl
  · simp only [Prod.snd_mul, Prod.snd_inv, hdeg']
    rw [mul_comm n, mul_assoc, mul_inv_cancel, mul_one]

end AlgebraicGeometry.WeilGroup.BasePointData
