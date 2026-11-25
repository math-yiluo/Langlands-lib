/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Extensionality of internal dual sections of exterior sheaves
Source: Stacks Project, Tag 03CY, uniqueness in module sheafification.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Internal functionals on an exterior sheaf agree if they agree on pure wedges
on every subopen, rather than only on wedges over the largest open.
Source: Stacks Project, Tag 03CY, uniqueness in the sheafification adjunction.
(blueprint: lem-sc-exterior-sheaf-dual-ext).

Proof: restrict the exterior presheaf and its sheafification to Over U. Open
restriction commutes with sheafification: a covering in Over U is precisely a
covering by subopens, so the sheafification unit remains locally bijective.
Precomposition with this unit is injective on maps into the structure sheaf,
by its sheaf property (equivalently the sheafification adjunction). The two
precomposed morphisms have equal components: each component is linear and the
pure wedges span the sectionwise exterior power. The hypothesis gives equality
on these spanning generators. Injectivity gives equality of the internal
functionals. Empty opens, zero rings and degree zero satisfy the same spanning
and adjunction statements. -/
theorem exteriorSheaf_dual_ext (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens)
    (q r : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U))
    (h : ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
      q.app (op (Over.mk g)) (Scheme.Modules.wedge (M := M) (r := n) (U := V) a) =
        r.app (op (Over.mk g)) (Scheme.Modules.wedge (M := M) (r := n) (U := V) a)) :
    q = r := by
  let P := (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  have heq (V : X.Opens) (g : V ⟶ U) :
      (η.app (op V)) ≫ q.app (op (Over.mk g)) =
        (η.app (op V)) ≫ r.app (op (Over.mk g)) := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext (R := X.presheaf.obj (op V))
    ext a
    exact h V g a
  let e := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify _ P.presheaf)
    infer_instance
  have hO := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology X) _ (forget _)
      (SheafOfModules.unit X.ringCatSheaf).isSheaf)
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  refine (hO.isSeparated _ (Presheaf.imageSieve_mem _ e x)).ext ?_
  intro V g hg
  obtain ⟨y, hy⟩ := hg
  have hq := PresheafOfModules.naturality_apply q
    (Over.homMk g : Over.mk (g ≫ W.unop.hom) ⟶ W.unop).op x
  have hr := PresheafOfModules.naturality_apply r
    (Over.homMk g : Over.mk (g ≫ W.unop.hom) ⟶ W.unop).op x
  have hy' : η.app (op V) y = (Scheme.Modules.exteriorPower M n).val.map g.op x := hy
  have he := CategoryTheory.congr_fun (heq V (g ≫ W.unop.hom)) y
  change q.app (op (Over.mk (g ≫ W.unop.hom))) (η.app (op V) y) =
    r.app (op (Over.mk (g ≫ W.unop.hom))) (η.app (op V) y) at he
  rw [hy'] at he
  exact hq.symm.trans (he.trans hr)


end AlgebraicGeometry
