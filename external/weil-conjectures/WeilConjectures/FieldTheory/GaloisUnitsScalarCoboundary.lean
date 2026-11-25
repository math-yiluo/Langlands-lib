/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect

/-!
# Scalar coboundaries of equal homogeneous classes

Source: Stacks Project, Tag 03R7, injectivity argument; Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct
open CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem exists_homogeneous_boundary (K : Type u) [Field K]
    (z w : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2)
    (hzw : (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z =
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom w) :
    ∃ F : (TopRep.homogeneousCochains (galoisUnitsTopRep K)).X 1,
      ((TopRep.homogeneousCochains (galoisUnitsTopRep K)).d 1 2).hom F =
        ((TopRep.homogeneousCochains (galoisUnitsTopRep K)).iCycles 2).hom z -
        ((TopRep.homogeneousCochains (galoisUnitsTopRep K)).iCycles 2).hom w := by
  let C := TopRep.homogeneousCochains (galoisUnitsTopRep K)
  let S := C.sc' 1 2 3
  let D : S.LeftHomologyData :=
    ⟨_, _, _, _, _, TopModuleCat.isLimitKer S.g, by simp, TopModuleCat.isColimitCoker _⟩
  let eZ := C.cyclesIsoSc' 1 2 3 (by simp) (by simp) ≪≫ D.cyclesIso
  let eH := C.homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫ D.homologyIso
  have hπ : C.homologyπ 2 ≫ eH.hom = eZ.hom ≫ D.π := by
    simp only [eH, eZ, Iso.trans_hom, ← Category.assoc,
      C.π_homologyIsoSc'_hom 1 2 3 (by simp) (by simp)]
    rw [Category.assoc, D.homologyπ_comp_homologyIso_hom]
    simp only [Category.assoc]
  have hq : D.π.hom (eZ.hom.hom z) = D.π.hom (eZ.hom.hom w) := by
    have hh := congrArg (fun t ↦ eH.hom.hom t) hzw
    change (C.homologyπ 2 ≫ eH.hom).hom z = (C.homologyπ 2 ≫ eH.hom).hom w at hh
    rw [hπ] at hh
    exact hh
  change Submodule.mkQ D.f'.hom.range (eZ.hom.hom z) =
    Submodule.mkQ D.f'.hom.range (eZ.hom.hom w) at hq
  have hm : eZ.hom.hom z - eZ.hom.hom w ∈ D.f'.hom.range := by
    exact (Submodule.Quotient.eq _).mp hq
  obtain ⟨F, hF⟩ := hm
  refine ⟨F, ?_⟩
  have hi : eZ.hom ≫ D.i = C.iCycles 2 := by
    simp only [eZ, Iso.trans_hom, Category.assoc, D.cyclesIso_hom_comp_i]
    exact C.cyclesIsoSc'_hom_iCycles 1 2 3 (by simp) (by simp)
  have hh := congrArg D.i.hom hF
  simp only [map_sub] at hh
  change (D.f' ≫ D.i).hom F = (eZ.hom ≫ D.i).hom z - (eZ.hom ≫ D.i).hom w at hh
  rw [D.f'_i, hi] at hh
  exact hh


set_option backward.isDefEq.respectTransparency false in
/-- Equal homogeneous classes have a locally constant multiplicative coboundary ratio.

Proof: the homogeneous cohomology is the kernel of d2 modulo the image of d1.
Equality of the projections therefore supplies an invariant continuous homogeneous
one-cochain F whose differential is z-w. Evaluate at (1,g) and put a(g)=F(1,g).toMul.
The coefficient topology is discrete, so continuity makes a locally constant.
Homogeneous equivariance gives F(g,g*h)=g(F(1,h)), while the degree-one differential
at (1,g,g*h) is F(g,g*h)-F(1,g*h)+F(1,g). Translating this additive equality to units
gives c_z/c_w=a(g)*g(a(h))/a(g*h), with precisely the sign shown below.
No normalization of either representative is required.
Source: Stacks Project, Section 0DVG, degree-one differential.
(blueprint: lem-sc-galois-units-scalar-coboundary). -/
theorem exists_scalar_cochain_of_galoisUnits_class_eq (K : Type u) [Field K]
    (z w : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2)
    (hzw : (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z =
      (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom w) :
    ∃ a : Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ,
      IsLocallyConstant a ∧ ∀ g h,
        galoisUnitsCocycleValue K z g h / galoisUnitsCocycleValue K w g h =
          a g * Units.map g.toRingHom (a h) / a (g * h) := by
  obtain ⟨F, hF⟩ := exists_homogeneous_boundary K z w hzw
  let a : Gal(SeparableClosure K/K) → (SeparableClosure K)ˣ :=
    fun g ↦ (F.val 1 g).toMul
  have hcont : Continuous (fun g ↦ F.val 1 g) := (F.val 1).continuous
  have : DiscreteTopology (galoisUnitsTopRep K) := ⟨rfl⟩
  refine ⟨a, ((IsLocallyConstant.iff_continuous _).mpr hcont).comp Additive.toMul, ?_⟩
  intro g h
  have he : (galoisUnitsTopRep K).ρ g (F.val 1 h) = F.val g (g * h) := by
    have hi := DFunLike.congr_fun (DFunLike.congr_fun
      ((ContRepresentation.mem_invariants _).mp F.property g) (g * 1)) (g * h)
    simpa using hi
  have hh := congrArg (fun f :
      (TopRep.homogeneousCochains (galoisUnitsTopRep K)).X 2 ↦ f.val 1 g (g * h)) hF
  rw [TopRep.homogeneousCochains.d_apply] at hh
  change F.val g (g * h) - (F.val 1 (g * h) - F.val 1 g) =
    (((TopRep.homogeneousCochains (galoisUnitsTopRep K)).iCycles 2).hom z).val
      1 g (g * h) -
    (((TopRep.homogeneousCochains (galoisUnitsTopRep K)).iCycles 2).hom w).val
      1 g (g * h) at hh
  rw [← he] at hh
  have hm := congrArg (fun t : Additive ((SeparableClosure K)ˣ) ↦ t.toMul) hh
  change Units.map g.toRingHom (a h) / (a (g * h) / a g) =
    galoisUnitsCocycleValue K z g h / galoisUnitsCocycleValue K w g h at hm
  have hunit (r s t : (SeparableClosure K)ˣ) : s / (t / r) = r * s / t := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ac_rfl
  exact hm.symm.trans (hunit (a g) (Units.map g.toRingHom (a h)) (a (g * h)))

end Field
