/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Reflection of constancy for cyclic module coefficients

Source: Stacks Project, Tags 03RU and 03RW(2),(3), with cyclic coefficients.
(blueprint: theorem-cohomology-curves).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Forgetting cyclic coefficients reflects constancy on a localized small etale site.
Source: Stacks Project, Definitions 03RU and 03RW(2),(3), and the cyclic coefficient
identification used in Theorem 03SC.
(blueprint: theorem-cohomology-curves)

Proof: Let E be a constant abelian value of the underlying sheaf. The quotient
E/nE is canonically a Z/n-module; lift its scalar action to ULift (ZMod n).
The underlying sheaf is annihilated by n. Since constant sheaves preserve cokernels,
the constant sheaf of E/nE is isomorphic to that of E: the cokernel of multiplication
by n on this latter sheaf is the sheaf itself. Constants commute with forgetting.
Every additive map between cyclic modules is linear, so the resulting abelian
isomorphism and its inverse lift sectionwise to a module-sheaf isomorphism.
This proves constancy, without choosing a point or assuming the scheme nonempty.
For n=1 the quotient is zero. On the empty site the same cokernel argument applies.
-/
theorem cyclic_module_isConstant_of_forget {Y : Scheme.{u}}
    (n : ℕ) [NeZero n] (U : Y.Etale)
    (F : Sheaf (Y.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    (h : ((sheafCompose (Y.smallEtaleTopology.over U)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj F).IsConstant (Y.smallEtaleTopology.over U)) :
    F.IsConstant (Y.smallEtaleTopology.over U) := by
  classical
  let R := ULift.{u + 1} (ZMod n)
  let V := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  have hscalar {P Q : ModuleCat.{u + 1} R} (f : P →+ Q) (r : R) (x : P) :
      f (r • x) = r • f x := by
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective r.down
    have hr : r = (a : R) := by
      apply ULift.ext
      exact ha.symm
    rw [hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
  have : V.Full := by
    constructor
    intro P Q f
    refine ⟨ModuleCat.ofHom { f.hom with map_smul' := fun r x ↦ hscalar f.hom r x }, ?_⟩
    rfl
  let J := Y.smallEtaleTopology.over U
  let G := (sheafCompose J V).obj F
  let L := constantSheaf J AddCommGrpCat.{u + 1}
  obtain ⟨E, ⟨e⟩⟩ := h.mem_essImage
  let f : E ⟶ E := n • 𝟙 E
  let Q := Limits.cokernel f
  have hQ : ∀ x : Q, n • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (Limits.cokernel.π f)).1
      inferInstance x
    have hc := ConcreteCategory.congr_hom (Limits.cokernel.condition f) y
    change (Limits.cokernel.π f).hom (n • y) = 0 at hc
    rw [map_nsmul] at hc
    exact hc
  let : Module (ZMod n) Q := AddCommGroup.zmodModule hQ
  let : Module R Q := Module.compHom Q ULift.ringEquiv.toRingHom
  let N := ModuleCat.of R Q
  have hkill (P : ModuleCat.{u + 1} R) (x : P) : n • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul R]
    have hn : (n : R) = 0 := by
      apply ULift.ext
      exact ZMod.natCast_self n
    rw [hn, zero_smul]
  have hnG : n • (𝟙 G) = 0 := by
    ext W x
    exact hkill (F.obj.obj W) x
  have hf : L.map f = 0 := by
    apply (cancel_mono e.hom).1
    rw [Limits.zero_comp]
    calc
      L.map f ≫ e.hom = n • e.hom := by simp [f]
      _ = e.hom ≫ (n • 𝟙 G) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [hnG, Limits.comp_zero]
  have hq : IsIso (L.map (Limits.cokernel.π f)) := by
    have : IsIso (Limits.cokernel.π (L.map f)) := Limits.cokernel.π_of_zero hf
    have hcomp := Limits.PreservesCokernel.π_iso_hom L f
    have : IsIso (L.map (Limits.cokernel.π f) ≫
        (Limits.PreservesCokernel.iso L f).hom) := hcomp ▸ inferInstance
    exact (isIso_comp_right_iff _ (Limits.PreservesCokernel.iso L f).hom).1 this
  have : J.PreservesSheafification V := by
    apply GrothendieckTopology.instPreservesSheafification
  let eG : G ≅ (sheafCompose J V).obj ((constantSheaf J (ModuleCat.{u + 1} R)).obj N) :=
    e.symm ≪≫ asIso (L.map (Limits.cokernel.π f)) ≪≫
      ((constantCommuteCompose J V).app N).symm
  exact Sheaf.isConstant_of_iso J ((sheafCompose J V).preimageIso eG)

end AlgebraicGeometry.Scheme
