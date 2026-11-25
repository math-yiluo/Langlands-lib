/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Normalized sections of an associated affine chart

Source: Stacks Project, Tags 01I7, 01HV, 01I9, 0096 and 0097.
(blueprint: new-p4-self-tor-affine-chart-sections). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The chart restriction scalar structures require extra elaboration fuel.
/-- The chart-associated module has its original module as sections on the chart.
Source: Stacks Project, Tag 01I7, lemma-compare-constructions; Tag 01HV,
lemma-spec-sheaves; Tag 0096, lemma-adjoint-pullback-pushforward-modules.
(blueprint: new-p4-self-tor-affine-chart-sections).
Proof: The tilde adjunction unit is an isomorphism from M to the global sections
on Spec A. The chart isomorphism sends the whole chart onto Spec A. The inverse
restriction section isomorphism identifies its sections with those of the chart
restriction; the open pushforward evaluates on U at the whole chart. These
isomorphisms compose to e. Their scalar maps compose to the identity of A, since
the chart isomorphism is induced by the identity on A. Thus e is A-linear.
Evaluating the composite is precisely the displayed restriction of the tilde
unit. The chart restriction is quasi-coherent by restriction of tilde; the open
pushforward followed by restriction is that same sheaf by the open counit.
For M=0 or U empty the same isomorphisms and formulas apply. -/
theorem exists_selfTor_affine_chart_sections
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) :
    let L := (tilde.functor Γ(Y, U.1)).obj M
    let C := (Scheme.Modules.pushforward U.1.ι).obj
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj L)
    ∃ e : M ≃ₗ[Γ(Y, U.1)] C.val.obj (op U.1),
      (C.restrict U.1.ι).IsQuasicoherent ∧ ∀ m : M,
        e m = (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L
          (U.1.ι ⁻¹ᵁ U.1)).inv
          (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) m)) := by
  classical
  dsimp only
  let L := (tilde.functor Γ(Y, U.1)).obj M
  let W := U.1.ι ⁻¹ᵁ U.1
  let B := (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj L
  let C := (Scheme.Modules.pushforward U.1.ι).obj B
  let q (m : M) : C.val.obj (op U.1) :=
    (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L W).inv
      (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) m))
  have hqadd (m n : M) : q (m + n) = q m + q n := by
    dsimp only [q]
    simp only [map_add]
  have hscalar (a : Γ(Y, U.1)) :
      (U.2.isoSpec.hom.appIso W).hom
        ((Spec Γ(Y, U.1)).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso Γ(Y, U.1)).inv a)) = (U.1.ι.app U.1).hom a := by
    change ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      (Spec Γ(Y, U.1)).presheaf.map (homOfLE le_top).op ≫
      (U.2.isoSpec.hom.appIso W).hom).hom a = _
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    change ((Scheme.ΓSpecIso Γ(Y, U.1)).inv ≫
      U.2.isoSpec.hom.appTop ≫ U.1.toScheme.presheaf.map (homOfLE le_top).op).hom a = _
    rw [U.2.isoSpec_hom_appTop, ← Category.assoc, Iso.inv_hom_id_assoc]
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map,
      ← Functor.map_comp]
    rfl
  have hqsmul (a : Γ(Y, U.1)) (m : M) : q (a • m) = a • q m := by
    dsimp only [q]
    rw [(tilde.adjunction.unit.app M).hom.map_smul]
    erw [Scheme.Modules.map_smul_Spec (M := L)]
    rw [Scheme.Modules.smul_Spec_def]
    have hs := Scheme.Modules.smul_restrictAppIso_inv_apply U.2.isoSpec.hom L W
      ((Spec Γ(Y, U.1)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso Γ(Y, U.1)).inv a))
      (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) m))
    refine hs.trans ?_
    rw [hscalar]
    rfl
  have hqbij : Function.Bijective q := by
    have hW : W = ⊤ := by simp [W]
    have htop : U.2.isoSpec.hom ''ᵁ W = ⊤ := by simp [hW, Scheme.Hom.opensRange_of_isIso]
    let hi : IsIso (homOfLE (show U.2.isoSpec.hom ''ᵁ W ≤ ⊤ from le_top)) := by
      rw [htop]
      exact ⟨⟨𝟙 _, by rfl, by rfl⟩⟩
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L W).inv).comp
      ((ConcreteCategory.bijective_of_isIso
        (L.presheaf.map (homOfLE (show U.2.isoSpec.hom ''ᵁ W ≤ ⊤ from le_top)).op)).comp
        (ConcreteCategory.bijective_of_isIso (tilde.adjunction.unit.app M)))
  let e := LinearEquiv.ofBijective
    (show M →ₗ[Γ(Y, U.1)] C.val.obj (op U.1) from
      { toFun := q, map_add' := hqadd, map_smul' := hqsmul }) hqbij
  refine ⟨e, ?_, fun _ ↦ rfl⟩
  have : L.IsQuasicoherent := inferInstanceAs
    (((tilde.functor Γ(Y, U.1)).obj M).IsQuasicoherent)
  have : B.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.2.isoSpec.hom L
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso U.1.ι).app B).symm
    (show B.IsQuasicoherent from ‹B.IsQuasicoherent›)

end AlgebraicGeometry
