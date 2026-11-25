/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # Tensor sections under an open pullback

Source: Stacks Project, Tags 0096, 0097 and 01CD.
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pull a section over U to the whole source of a morphism whose image lies in U.
Source: Stacks Project, Tag 0096. This is the specified adjunction unit followed
by restriction, with no choice of a section.
(blueprint: lem-sc-scalar-open-tensor-transport). -/
def tensorPullbackOpenSection {X Y : Scheme.{w}} (a : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (hTop : ⊤ ≤ a ⁻¹ᵁ U) (s : M.val.obj (op U)) :
    ((tensorPullback a).obj M).val.obj (op ⊤) :=
  ((tensorPullback a).obj M).val.map (homOfLE hTop).op
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app (op U) s)

/-- On an open immersion, tensor pullback transports all tensor sections, also
when its two coefficients are identified with other modules.
Source: Stacks Project, Tags 0096, 0097 and 01CD.
(blueprint: lem-sc-scalar-open-tensor-transport).

Proof: The unit of the restriction adjunction on an open contained in the
image is an isomorphism. Uniqueness of left adjoints identifies this unit
with the specified tensor-pullback unit. Since the inverse image of U is
the whole source, restricting its component to the top open is still an
isomorphism. Restrict scalars along the structure morphisms; the equality
of structure morphisms makes these section maps k-linear. Apply this to
M tensor N and then the tensor-pullback comparison of Tag 01CD. Finally
apply the tensor product of the supplied coefficient isomorphisms. The
unit formula of the comparison sends a tensor section to the tensor of
the two unit sections; restriction and the coefficient maps preserve
this formula. This constructs eT and proves the equality for arbitrary
sections of M and N, including zero modules and empty opens. -/
theorem exists_scalarOpenTensorTransport
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (a : Y ⟶ X) [IsOpenImmersion a] (h : a ≫ f = g)
    (U : X.Opens) (hTop : ⊤ ≤ a ⁻¹ᵁ U) (hRange : U ≤ a.opensRange)
    (M N : X.Modules) (M' N' : Y.Modules)
    (eM : (tensorPullback a).obj M ≅ M')
    (eN : (tensorPullback a).obj N ≅ N') :
    ∃ eT : scalarObj f (show X.Modules from M ⊗ N) (op U) ≅
        scalarObj g (show Y.Modules from M' ⊗ N') (op ⊤),
      ∀ (s : scalarObj f M (op U)) (t : scalarObj f N (op U)),
        eT.hom (tmulSection s t) =
          tmulSection (eM.hom.app ⊤ (tensorPullbackOpenSection a M U hTop s))
            (eN.hom.app ⊤ (tensorPullbackOpenSection a N U hTop t))  := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction a)
  have hbij (P : X.Modules) : Function.Bijective
      ((adj.unit.app P).app U) := by
    have hu := (pullbackPushforwardAdjunction a).unit_leftAdjointUniq_hom_app adj P
    have hu' := congrArg (fun φ ↦ φ.app U) hu
    rw [← hu', Hom.comp_app]
    exact (ConcreteCategory.bijective_of_isIso
      (((pushforward a).map
        (((pullbackPushforwardAdjunction a).leftAdjointUniq adj).hom.app P)).app U)).comp
      (bijective_pullbackUnit_app_of_isOpenImmersion a P hRange)
  have hres : IsIso (homOfLE hTop) := by
    exact ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  let β := ((((TopologicalSpace.Opens.map a.base).sheafAdjunctionContinuous
    (ModuleCat.{w} k) _ _).homEquiv _ _)
      (Classical.choose (exists_scalarPullbackCoefficient f g a h
        (show X.Modules from M ⊗ N)))).hom
  let u : scalarObj f (show X.Modules from M ⊗ N) (op U) ⟶
      scalarObj g ((tensorPullback a).obj (show X.Modules from M ⊗ N)) (op ⊤) :=
    β.app (op U) ≫ (scalarPresheaf g ((tensorPullback a).obj (show X.Modules from M ⊗ N))).map
      (homOfLE hTop).op
  have hu (z : scalarObj f (show X.Modules from M ⊗ N) (op U)) :
      u z = tensorPullbackOpenSection a (show X.Modules from M ⊗ N) U hTop z := by
    change ((tensorPullback a).obj (show X.Modules from M ⊗ N)).val.map _ (β.app (op U) z) = _
    exact congrArg (((tensorPullback a).obj (M ⊗ N)).val.map (homOfLE hTop).op)
      (Classical.choose_spec (exists_scalarPullbackCoefficient f g a h
        (show X.Modules from M ⊗ N)) U z)
  have huBij : Function.Bijective u := by
    have hb : Function.Bijective (β.app (op U)) := by
      have hβ (z : scalarObj f (show X.Modules from M ⊗ N) (op U)) :
          β.app (op U) z = (adj.unit.app (show X.Modules from M ⊗ N)).app U z :=
        Classical.choose_spec (exists_scalarPullbackCoefficient f g a h
          (show X.Modules from M ⊗ N)) U z
      have hfun : (fun z ↦ β.app (op U) z) =
          (fun z ↦ (adj.unit.app (show X.Modules from M ⊗ N)).app U z) := funext hβ
      change Function.Bijective (fun z ↦ β.app (op U) z)
      rw [hfun]
      exact hbij (show X.Modules from M ⊗ N)
    exact (ConcreteCategory.bijective_of_isIso
      ((scalarPresheaf g ((tensorPullback a).obj (show X.Modules from M ⊗ N))).map
        (homOfLE hTop).op)).comp hb
  let : IsIso u := (ConcreteCategory.isIso_iff_bijective u).mpr huBij
  obtain ⟨e, _, he⟩ := module_pullback_tensor a
  let ec := e M N ≪≫ tensorIso eM eN
  let es : scalarObj g ((tensorPullback a).obj (show X.Modules from M ⊗ N)) (op ⊤) ≅
      scalarObj g (show Y.Modules from M' ⊗ N') (op ⊤) :=
    { hom := scalarHomApp g ec.hom (op ⊤)
      inv := scalarHomApp g ec.inv (op ⊤)
      hom_inv_id := by
        ext z
        exact congrArg (fun φ ↦ φ.app ⊤ z) ec.hom_inv_id
      inv_hom_id := by
        ext z
        exact congrArg (fun φ ↦ φ.app ⊤ z) ec.inv_hom_id }
  refine ⟨asIso u ≪≫ es, ?_⟩
  intro s t
  change ec.hom.app ⊤ (u (tmulSection s t)) = _
  rw [hu]
  have hn := Hom.app_presheaf_map (e M N).hom (homOfLE hTop)
    ((adj.unit.app (show X.Modules from M ⊗ N)).app U (tmulSection s t))
  change ((tensorIso eM eN).hom.app ⊤)
    ((e M N).hom.app ⊤
      (((tensorPullback a).obj (show X.Modules from M ⊗ N)).presheaf.map (homOfLE hTop).op
        ((adj.unit.app (show X.Modules from M ⊗ N)).app U (tmulSection s t)))) = _
  rw [hn]
  have ht := he M N U (show Γ(M, U) from s) (show Γ(N, U) from t)
  change (e M N).hom.app (a ⁻¹ᵁ U)
    ((adj.unit.app (M ⊗ N)).app U (tmulSection s t)) = _ at ht
  rw [ht, tmulSection_map]
  exact tensorHom_app_tmulSection eM.hom eN.hom
    (tensorPullbackOpenSection a M U hTop s) (tensorPullbackOpenSection a N U hTop t)

end
end AlgebraicGeometry.Scheme.Modules
