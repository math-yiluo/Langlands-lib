/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardScalarAffineSectionsExact
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Scalar sections transported along a scheme isomorphism

Source: Stacks Project, Sheaves on Spaces, Tags 00A0 and 0097.
(blueprint: lem-sc-scalar-sections-iso-transport).
-/

@[expose] public section
universe w
open CategoryTheory Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along an isomorphism transports sections on corresponding opens,
including the scalar action from the composite structure morphism.
Source: Stacks Project, Sheaves on Spaces, Tags 00A0 and 0097.
(blueprint: lem-sc-scalar-sections-iso-transport).

Proof: Let a be the isomorphism's forward morphism and adj the tensor
pullback/pushforward adjunction. Pushforward along a is fully faithful because
a is an open immersion (restriction has an invertible counit). Every module
on Q is in its essential image: composing pushforward along the inverse with
pushforward along a is the identity, by pushforward composition and the
inverse-hom identity. Thus adj's unit at every module is an isomorphism.
Evaluate this unit on U. It maps sections of M on U to sections of a* M on
a inverse-image U and is bijective. The structure-ring map carries scalarMap
for s on U to scalarMap for a followed by s on the inverse-image open:
rewrite both through appLE and use appLE_comp_appLE. Hence the evaluated
unit is k-linear. Its naturality in M is adj.unit's naturality evaluated at U.
Apply the concrete-category bijectivity criterion and assemble the resulting
component isomorphisms with NatIso.ofComponents; invert to get the displayed
orientation. This argument includes empty opens and zero modules and uses no
quasi-coherence hypothesis. -/
theorem scalarSections_iso_transport
    {k : Type w} [Field k] {P Q : Scheme.{w}} (e : P ≅ Q)
    (s : Q ⟶ Spec (CommRingCat.of k)) (U : Q.Opens) :
    Nonempty (tensorPullback e.hom ⋙
      picardScalarSectionsFunctor (e.hom ≫ s) (e.hom ⁻¹ᵁ U) ≅
      picardScalarSectionsFunctor s U) := by
  classical
  let a := e.hom
  let adj := Classical.choose (exists_tensorPullbackAdjunction a)
  have hη (M : Q.Modules) : IsIso (adj.unit.app M) := by
    let c : pushforward e.inv ⋙ pushforward a ≅ 𝟭 Q.Modules :=
      pushforwardComp e.inv a ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Q
    exact adj.isIso_unit_app_of_iso (c.app M).symm
  have hscalar (r : k) :
      (a.app U).hom (scalarMap s U r) = scalarMap (a ≫ s) (a ⁻¹ᵁ U) r := by
    have h : scalarMap (a ≫ s) (a ⁻¹ᵁ U) =
        (a.app U).hom.comp (scalarMap s U) := by
      change ((ΓSpecIso (.of k)).inv ≫ (a ≫ s).appLE ⊤ (a ⁻¹ᵁ U) (by simp)).hom =
        ((ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U (by simp) ≫ a.app U).hom
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact (congrArg (fun t : k →+* Γ(P, a ⁻¹ᵁ U) ↦ t r) h).symm
  let b (M : Q.Modules) :
      (picardScalarSectionsFunctor s U).obj M ⟶
      (tensorPullback a ⋙ picardScalarSectionsFunctor (a ≫ s) (a ⁻¹ᵁ U)).obj M :=
    letI : Module k (M.val.obj (op U)) := Module.compHom _ (scalarMap s U)
    letI : Module k (((tensorPullback a).obj M).val.obj (op (a ⁻¹ᵁ U))) :=
      Module.compHom _ (scalarMap (a ≫ s) (a ⁻¹ᵁ U))
    ModuleCat.ofHom
      { toFun := fun x : scalarObj s M (op U) ↦
          ((adj.unit.app M).val.app (op U) x :
            scalarObj (a ≫ s) ((tensorPullback a).obj M) (op (a ⁻¹ᵁ U)))
        map_add' := fun x y ↦ ((adj.unit.app M).val.app (op U)).hom.map_add x y
        map_smul' := by
          intro r x
          change (adj.unit.app M).val.app (op U) ((scalarMap s U r) • x) =
            (scalarMap (a ≫ s) (a ⁻¹ᵁ U) r) •
              (show ((tensorPullback a).obj M).val.obj (op (a ⁻¹ᵁ U)) from
                (adj.unit.app M).val.app (op U) x)
          rw [((adj.unit.app M).val.app (op U)).hom.map_smul]
          change ((a.app U).hom (scalarMap s U r)) •
            (show ((tensorPullback a).obj M).val.obj (op (a ⁻¹ᵁ U)) from
              (adj.unit.app M).val.app (op U) x) = _
          rw [hscalar] }
  have hb (M : Q.Modules) : IsIso (b M) := by
    have := hη M
    have : IsIso ((adj.unit.app M).app U) := inferInstance
    apply (ConcreteCategory.isIso_iff_bijective (b M)).mpr
    exact ConcreteCategory.bijective_of_isIso ((adj.unit.app M).app U)
  let := hb
  refine ⟨(NatIso.ofComponents (fun M ↦ asIso (b M)) ?_).symm⟩
  intro M N φ
  ext x
  have h := NatTrans.naturality adj.unit φ
  have h' := congrArg (fun ψ : M ⟶ (pushforward a).obj ((tensorPullback a).obj N) ↦
    ψ.app U) h
  have hx := ConcreteCategory.congr_hom h' x
  exact hx


end AlgebraicGeometry.Scheme.Modules
