/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance

/-! # The canonical frame off a Cartier divisor
Source: blueprint Cartier proof (G1), local inverse equations.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem divisorSection_eq {D T : Scheme.{u}} (i : D ⟶ T) :
    supportedDivisorSection i =
      (SheafOfModules.homObjUnitIso (Scheme.Modules.unit T)).inv ≫
        Scheme.Modules.dualMap i.ker.toModulesι := by
  ext U x : 3
  change @Eq
    ((PresheafOfModules.restrictOver T.sheaf.obj U).obj i.ker.toModules.val ⟶
      (PresheafOfModules.restrictOver T.sheaf.obj U).obj (Scheme.Modules.unit T).val) _ _
  ext V : 2
  ext y
  change T.presheaf.map V.unop.hom.op x *
      (show Γ(T, V.unop.left) from (i.ker.toModulesι.val.app (op V.unop.left)) y) =
    (show Γ(T, V.unop.left) from (i.ker.toModulesι.val.app (op V.unop.left)) y) *
      T.presheaf.map V.unop.hom.op x
  exact mul_comm _ _

private theorem pullbackSection_eq {D T : Scheme.{u}} (i : D ⟶ T) (W : T.Opens) :
    supportedDivisorSectionPullback i W =
      (Scheme.Modules.pullback W.ι).map (supportedDivisorSection i) := by
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction W.ι)
  change (e.app _).inv ≫ (Scheme.Modules.tensorPullback W.ι).map
    (supportedDivisorSection i) ≫ (e.app _).hom = _
  erw [e.hom.naturality, e.inv_hom_id_app_assoc]

/-- The canonical divisor section is invertible on the complementary open.
Source: Stacks Project, Tag 0A45, and blueprint Cartier proof (G1).
(auxiliary; not a blueprint node)
Proof: off the closed divisor the ideal inclusion is an isomorphism. Open restriction
commutes with internal Hom, so its dual is an isomorphism too. The canonical divisor
section is the dual inclusion composed with the unit internal-Hom isomorphism.
Transport to ordinary pullback by uniqueness of left adjoints. The argument also
applies to the empty complementary open. -/
theorem cartierDivisorSectionPullback_isIso {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (W : T.Opens)
    (hW : (W : Set T) = (Set.range i.base)ᶜ) :
    IsIso (supportedDivisorSectionPullback i W) := by
  let F := Scheme.Modules.restrictFunctor W.ι
  have hU : (W : Set T) ⊆ (i.ker.support : Set T)ᶜ := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    exact hW.le
  have hi : IsIso (F.map i.ker.toModulesι) :=
    Scheme.IdealSheafData.isIso_restrictFunctor_map_toModulesι i.ker hU
  obtain ⟨s, hs⟩ := internalHom_restrict_scheme W
  have hk : IsIso (SheafOfModules.homObjMap (R := W.toScheme.sheaf)
      (F.map i.ker.toModulesι) (F.map (𝟙 (Scheme.Modules.unit T)))) := by
    rw [F.map_id]
    exact inferInstanceAs (IsIso (((SheafOfModules.homFunctor W.toScheme.sheaf).flip.obj
      (F.obj (Scheme.Modules.unit T))).map (F.map i.ker.toModulesι).op))
  have hc : IsIso (F.map (Scheme.Modules.dualMap i.ker.toModulesι) ≫
      (s i.ker.toModules (Scheme.Modules.unit T)).hom) := by
    rw [hs i.ker.toModulesι (𝟙 (Scheme.Modules.unit T))]
    infer_instance
  have : IsIso (F.map (Scheme.Modules.dualMap i.ker.toModulesι)) :=
    IsIso.of_isIso_comp_right _ (s i.ker.toModules (Scheme.Modules.unit T)).hom
  have : IsIso (F.map (supportedDivisorSection i)) := by
    rw [divisorSection_eq, Functor.map_comp]
    infer_instance
  rw [pullbackSection_eq]
  rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι)]
  infer_instance

end AlgebraicGeometry.Etale
