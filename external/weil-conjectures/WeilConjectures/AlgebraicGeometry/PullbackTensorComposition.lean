/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection

/-! # Tensor compatibility of ordinary pullback composition

Source: Stacks Project, Tags 0095 and 0096.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_hom_ext {X : Scheme.{u}} {M N P : X.Modules}
    {a b : M ⊗ N ⟶ P}
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) P).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComp_tensor_inv
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (M N : X.Modules) :
    (pullbackComp k l).inv.app (M ⊗ N) ≫
        (pullback k).map (Functor.OplaxMonoidal.δ (pullback l) M N) ≫
        Functor.OplaxMonoidal.δ (pullback k) _ _ =
      Functor.OplaxMonoidal.δ (pullback (k ≫ l)) M N ≫
        ((pullbackComp k l).inv.app M ⊗ₘ (pullbackComp k l).inv.app N) := by
  apply ((pullbackPushforwardAdjunction (k ≫ l)).homEquiv _ _).injective
  apply tensor_hom_ext
  intro U s t
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply]
  change (Functor.OplaxMonoidal.δ (pullback k) _ _).app (k ⁻¹ᵁ (l ⁻¹ᵁ U))
      (((pullback k).map (Functor.OplaxMonoidal.δ (pullback l) M N)).app
        (k ⁻¹ᵁ (l ⁻¹ᵁ U))
        (((pullbackComp k l).inv.app (M ⊗ N)).app ((k ≫ l) ⁻¹ᵁ U)
          (pullbackUnitApp (k ≫ l) (M ⊗ N) U (tmulSection s t)))) =
    ((pullbackComp k l).inv.app M ⊗ₘ (pullbackComp k l).inv.app N).app
      ((k ≫ l) ⁻¹ᵁ U)
      ((Functor.OplaxMonoidal.δ (pullback (k ≫ l)) M N).app ((k ≫ l) ⁻¹ᵁ U)
        (pullbackUnitApp (k ≫ l) (M ⊗ N) U (tmulSection s t)))
  let a := (Functor.OplaxMonoidal.δ (pullback k) ((pullback l).obj M)
    ((pullback l).obj N)).app (k ⁻¹ᵁ (l ⁻¹ᵁ U))
  let b := ((pullback k).map (Functor.OplaxMonoidal.δ (pullback l) M N)).app
    (k ⁻¹ᵁ (l ⁻¹ᵁ U))
  have hu := pullbackUnit_comp_app_apply k l (M ⊗ N) U (tmulSection s t)
  have hn := pullbackUnit_naturality_apply k (Functor.OplaxMonoidal.δ (pullback l) M N)
    (l ⁻¹ᵁ U) (pullbackUnitApp l (M ⊗ N) U (tmulSection s t))
  have hl := pullback_δ_app_unit_tmulSection l M N U s t
  have hk := pullback_δ_app_unit_tmulSection k ((pullback l).obj M) ((pullback l).obj N)
    (l ⁻¹ᵁ U) (pullbackUnitApp l M U s) (pullbackUnitApp l N U t)
  have hc := pullback_δ_app_unit_tmulSection (k ≫ l) M N U s t
  have ht := tensorHom_app_tmulSection ((pullbackComp k l).inv.app M)
    ((pullbackComp k l).inv.app N) (pullbackUnitApp (k ≫ l) M U s)
    (pullbackUnitApp (k ≫ l) N U t)
  have hm := pullbackUnit_comp_app_apply k l M U s
  have hnt := pullbackUnit_comp_app_apply k l N U t
  exact (congrArg (fun z ↦ a (b z)) hu).trans
    ((congrArg (fun z ↦ a z) hn).trans
      ((congrArg (fun z ↦ a (pullbackUnitApp k
          ((pullback l).obj M ⊗ (pullback l).obj N) (l ⁻¹ᵁ U) z)) hl).trans
        (hk.trans ((congrArg₂ (fun m n ↦ tmulSection (M := (pullback k).obj ((pullback l).obj M))
            (N := (pullback k).obj ((pullback l).obj N)) (U := k ⁻¹ᵁ (l ⁻¹ᵁ U)) m n)
            hm hnt).symm.trans
          (ht.symm.trans (congrArg
            (fun z ↦ ((pullbackComp k l).inv.app M ⊗ₘ
              (pullbackComp k l).inv.app N).app ((k ≫ l) ⁻¹ᵁ U) z) hc).symm)))))

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary pullback composition isomorphism preserves the tensorator.
Source: Stacks Project, Definition 6.26.1(2), Tag 0095; Lemma 6.26.2, Tag 0096.
(blueprint: lem-sc-pullback-tensor-composition)

Proof: The presheaf pullback is extension of scalars after the inverse-image
construction. Its tensorator multiplies scalar coefficients. Its canonical
composition comparison sends r tensor (s tensor m) to r*k-sharp(s) tensor m:
this map has the composite adjunction unit, hence equals the unique composition
comparison normalized by the pullback/pushforward adjunction. On the pure tensors
(r tensor (s tensor m)) tensor (r-prime tensor (s-prime tensor n)), the left
route produces r*r-prime*k-sharp(s*s-prime) tensor (m tensor n). The right
route produces (r*k-sharp(s))*(r-prime*k-sharp(s-prime)) tensor (m tensor n).
Commutativity and preservation of multiplication by k-sharp identify them.
Here generators carry representatives on neighbourhoods in the inverse-image
colimit; two representatives can be restricted to a common neighbourhood.
The formula commutes with these restrictions and with the balancing relations,
so the tensor and colimit universal properties extend the equality to the
presheaf maps. After sheafification, arbitrary sections are locally represented
by these finite sums of generators; equality on them gives equality of sheaf
maps by the uniqueness part of the sheaf condition. The fixed pullback monoidal
structure descends these tensorators along sheafification via the monoidal
lifting comparison sheafificationCompPullback. The descended composition map
has the composite adjunction unit: on each generator the unit inserts scalar 1
at both stages, and the formula sends 1 tensor (1 tensor m) to 1 tensor m.
Injectivity of the adjunction Hom bijection therefore identifies this map with
the specified pullbackComp, rather than an arbitrary composition isomorphism.
Thus localization gives exactly the displayed equation.
The generator argument also covers zero modules, zero rings, empty schemes
and identity arrows; there are no finiteness or invertibility assumptions. -/
@[reassoc]
theorem pullbackComp_tensor
    {X Y Z : Scheme.{u}} (k : Z ⟶ Y) (l : Y ⟶ X) (M N : X.Modules) :
    (Functor.Monoidal.μIso (pullback k) ((pullback l).obj M)
      ((pullback l).obj N)).hom ≫
      (pullback k).map (Functor.Monoidal.μIso (pullback l) M N).hom ≫
        (pullbackComp k l).hom.app (M ⊗ N) =
    ((pullbackComp k l).hom.app M ⊗ₘ (pullbackComp k l).hom.app N) ≫
      (Functor.Monoidal.μIso (pullback (k ≫ l)) M N).hom := by
  simp only [Functor.Monoidal.μIso_hom]
  rw [← cancel_epi (Functor.OplaxMonoidal.δ (pullback k) _ _)]
  rw [Functor.Monoidal.δ_μ_assoc]
  rw [← cancel_epi ((pullback k).map (Functor.OplaxMonoidal.δ (pullback l) M N))]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.δ_μ,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_epi ((pullbackComp k l).inv.app (M ⊗ N))]
  rw [Iso.inv_hom_id_app]
  rw [reassoc_of% (pullbackComp_tensor_inv k l M N)]
  simp [tensorHom_comp_tensorHom_assoc]

end AlgebraicGeometry.Scheme.Modules
