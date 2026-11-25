/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace LinearMap

/-- Products of scalar quasi-inverses annihilate kernel and cokernel.
Source: Stacks Project, Remark 0888, final scalar-composite argument.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-criterion)
-/
theorem annihilated_of_scalar_composites
    {A : Type u} [CommRing A] (K : Ideal A) (t : ℕ)
    {P : Type v} {R : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup R] [Module A R] (v : P →ₗ[A] R)
    (hv : ∀ (f g : A), f ∈ K ^ t → g ∈ K ^ t →
      ∃ k : R →ₗ[A] P,
        k.comp v = (f * g) • LinearMap.id ∧
        v.comp k = (f * g) • LinearMap.id) :
    K ^ (2 * t) ≤ Module.annihilator A (LinearMap.ker v) ∧
      K ^ (2 * t) ≤ Module.annihilator A (R ⧸ LinearMap.range v) := by
  rw [two_mul, pow_add]
  constructor
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, hk, _⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    have h := congrArg (fun l : P →ₗ[A] P ↦ l x) hk
    simpa [LinearMap.mem_ker.mp x.property] using h.symm
  · refine Ideal.mul_le.mpr fun f hf g hg ↦ ?_
    obtain ⟨k, _, hk⟩ := hv f g hf hg
    apply Module.mem_annihilator.mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      change (LinearMap.range v).mkQ ((f * g) • y) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨k y, ?_⟩
      exact congrArg (fun l : R →ₗ[A] R ↦ l y) hk

end LinearMap

/-- The scalar reverse maps on the affine inverse limit.
Source: Stacks Project, Remark 0888, final paragraph, implication (1) to (2).
The componentwise annihilation hypotheses give the canonical lift maps at every
level. Their compatibility with transition maps makes them a map on inverse
limits; the two scalar composite identities are then checked by the limit
projections. This is the intermediate scalar-composite assertion used by the
annihilation criterion.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-scalar)
-/
abbrev affineLimitModule (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModule X I)
    (U : X.affineOpens) := ↥(limit (F.obj ⋙
      SheafOfModules.evaluation X.ringCatSheaf (op U.1)) : ModuleCat Γ(X, U.1))

-- Projectionwise verification avoids unfolding the concrete inverse limit.
private theorem limit_scalar_composites {A : Type u} [CommRing A]
    {P Q : ℕᵒᵖ ⥤ ModuleCat.{u} A} (δ : P ⟶ Q) (β : Q ⟶ P) (r : A)
    (hl : ∀ j, δ.app j ≫ β.app j = r • 𝟙 (P.obj j))
    (hr : ∀ j, β.app j ≫ δ.app j = r • 𝟙 (Q.obj j)) :
    lim.map δ ≫ lim.map β = r • 𝟙 (limit P) ∧
      lim.map β ≫ lim.map δ = r • 𝟙 (limit Q) := by
  constructor
  · apply limit.hom_ext
    intro j
    rw [← limMap_eq δ, ← limMap_eq β, Category.assoc, limMap_π β j,
      ← Category.assoc, limMap_π δ j, Category.assoc, hl j]
    apply ModuleCat.hom_ext
    ext x
    simp
  · apply limit.hom_ext
    intro j
    rw [← limMap_eq δ, ← limMap_eq β, Category.assoc, limMap_π δ j,
      ← Category.assoc, limMap_π β j, Category.assoc, hr j]
    apply ModuleCat.hom_ext
    ext x
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem affine_section_annihilation {X : Scheme.{u}} (K : X.IdealSheafData)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) (t : ℕ)
    (hk : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a)))
    (hc : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a))) (U : X.affineOpens) :
    K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker (a.val.app (op U.1)).hom) ∧
    K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
      (Γ(N, U.1) ⧸ LinearMap.range (a.val.app (op U.1)).hom) := by
  have := Scheme.Modules.isQuasicoherent_kernel a
  have := Scheme.Modules.isQuasicoherent_cokernel a
  have cover : ∀ x : X, ∃ V ∈ (Set.univ : Set X.affineOpens), x ∈ V.1 := by
    intro x
    obtain ⟨V, hV, hx, _⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
    exact ⟨⟨V, hV⟩, Set.mem_univ _, hx⟩
  have hks := (Scheme.idealPowerProduct_isZero_iff_affine_cover X (kernel a) K
    Set.univ cover t).mp hk U (Set.mem_univ _)
  have hcs := (Scheme.idealPowerProduct_isZero_iff_affine_cover X (cokernel a) K
    Set.univ cover t).mp hc U (Set.mem_univ _)
  constructor
  · intro f hf
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp (Scheme.Modules.range_map_kernelι U.1 a) x.val).mpr
      (LinearMap.mem_ker.mp x.property)
    apply Subtype.ext
    change f • x.val = 0
    rw [← hy]
    change f • ((kernel.ι a).val.app (op U.1)).hom y = 0
    rw [← map_smul, Module.mem_annihilator.mp (hks hf) y, map_zero]
  · obtain ⟨e, he⟩ := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 U
      |>.2.2.2
    intro f hf
    apply Module.mem_annihilator.mpr
    intro x
    apply e.injective
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp (hcs hf) (e x)

/-- For scalars in the affine ideal power, construct compatible reverse maps on all
levels and pass them to the inverse limit. At each level, annihilation of the
kernel makes the map independent of the chosen lift, while annihilation of the
cokernel provides a lift. Naturality of the transition maps gives compatibility.
The two composite identities follow by checking every limit projection.
Source: Stacks Project, Remark 0888, final paragraph.
(blueprint: lem-weil-pbc-formal-annihilation-affine-limit-scalar)
-/
theorem coherentFormalModule_affine_limit_scalar_composites
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G) (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) (U : X.affineOpens) :
    ∀ (f g : Γ(X, U.1)), f ∈ K.ideal U ^ t → g ∈ K.ideal U ^ t →
      ∃ k : affineLimitModule X I G U →ₗ[Γ(X, U.1)] affineLimitModule X I F U,
        k.comp (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom =
          (f * g) • (LinearMap.id : affineLimitModule X I F U →ₗ[Γ(X, U.1)]
            affineLimitModule X I F U) ∧
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom.comp k =
          (f * g) • (LinearMap.id : affineLimitModule X I G U →ₗ[Γ(X, U.1)]
            affineLimitModule X I G U) := by
  classical
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let P : ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U.1) := F.obj ⋙ E
  let Q : ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U.1) := G.obj ⋙ E
  let δ : P ⟶ Q := Functor.whiskerRight α.hom E
  have hann (n : ℕ) :
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (LinearMap.ker (δ.app (op n)).hom) ∧
      K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (Q.obj (op n) ⧸ LinearMap.range (δ.app (op n)).hom) := by
    let : (F.obj.obj (op n)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 n)).1
    let : (G.obj.obj (op n)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (G.property.1 n)).1
    exact affine_section_annihilation K (α.hom.app (op n)) t (h n).1 (h n).2 U
  intro f g hf hg
  have maps (j : ℕᵒᵖ) :=
    (_root_.LinearMap.ker_coker_annihilated_mod_ideal.{u, u, u, u, u, u, u}
      (K.ideal U) t ht (δ.app j).hom (hann j.unop).1 (hann j.unop).2).1 f g hf hg
  choose k formula left right natural using fun j ↦ (maps j).2.2
  let β : Q ⟶ P :=
    { app := fun j ↦ ModuleCat.ofHom (k j)
      naturality := by
        intro i j q
        apply ModuleCat.hom_ext
        exact (natural i (P.obj j) (Q.obj j) (δ.app j).hom
          (hann j.unop).1 (hann j.unop).2 (P.map q).hom (Q.map q).hom (k j)
          (congrArg ModuleCat.Hom.hom (δ.naturality q)) (formula j)).symm }
  have composites := limit_scalar_composites δ β (f * g)
    (fun j ↦ ModuleCat.hom_ext (left j)) (fun j ↦ ModuleCat.hom_ext (right j))
  exact ⟨(lim.map β).hom, congrArg ModuleCat.Hom.hom composites.1,
    congrArg ModuleCat.Hom.hom composites.2⟩

end AlgebraicGeometry
