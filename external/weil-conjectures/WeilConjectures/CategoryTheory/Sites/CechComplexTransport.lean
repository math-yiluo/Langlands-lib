/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Sites.CechComplex

/-!
# Transport of Čech complexes along a functor

Let `G : C ⥤ D` be a functor, `V` an object of `C` and `U : ι → Over V` a family of objects
over `V`. If `Over.post G : Over V ⥤ Over (G.obj V)` preserves finite products, then for every
presheaf `P` of abelian groups on `D` the Čech complex of `U` with values in `G.op ⋙ P` is
isomorphic to the Čech complex of the family `fun i ↦ (Over.post G).obj (U i)` with values in
`P`: the members of the Čech nerves correspond under the comparison isomorphisms
`G(U (y 0) ×_V ⋯ ×_V U (y k)) ≅ G(U (y 0)) ×_{G V} ⋯ ×_{G V} G(U (y k))`.

## Main definitions

- `CategoryTheory.Presheaf.cechComplexCompIso`: the isomorphism of Čech complexes.

## Main statements

- `CategoryTheory.Presheaf.exactAt_cechComplex_comp_iff`: exactness of the two Čech complexes
  in positive degrees is equivalent.
-/

@[expose] public section

universe t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {D : Type w} [Category.{v} D] (G : C ⥤ D) {V : C}
  [HasFiniteProducts (Over V)] [HasFiniteProducts (Over (G.obj V))]
  [PreservesFiniteProducts (Over.post G (X := V))] {ι : Type t} (U : ι → Over V)

/-- The comparison isomorphism between the image under `Over.post G` of a member of the Čech
nerve of `U` and the corresponding member of the Čech nerve of the image family. -/
noncomputable abbrev cechNerveObjPostIso {k : ℕ} (y : Fin (k + 1) → ι) :
    (Over.post G).obj (cechNerveObj U y) ≅
      cechNerveObj (fun i ↦ (Over.post G).obj (U i)) y :=
  PreservesProduct.iso (Over.post G) _

/-- The comparison isomorphisms of `CategoryTheory.Presheaf.cechNerveObjPostIso` are compatible
with the maps of the Čech nerves. -/
@[reassoc]
lemma cechNerveObjPostIso_hom_cechNerveMap {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    (Over.post G).map (cechNerveMap U y θ) ≫ (cechNerveObjPostIso G U (y ∘ θ)).hom =
      (cechNerveObjPostIso G U y).hom ≫
        cechNerveMap (fun i ↦ (Over.post G).obj (U i)) y θ :=
  Pi.hom_ext _ _ fun l ↦ by
    rw [Category.assoc, Category.assoc, PreservesProduct.iso_hom, PreservesProduct.iso_hom,
      piComparison_comp_π, ← Functor.map_comp]
    simp only [Function.comp_apply, cechNerveMap_π, piComparison_comp_π]

/-- The inverses of the comparison isomorphisms of
`CategoryTheory.Presheaf.cechNerveObjPostIso` are compatible with the maps of the Čech nerves. -/
@[reassoc]
lemma cechNerveObjPostIso_inv_cechNerveMap {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) :
    (cechNerveObjPostIso G U y).inv ≫ (Over.post G).map (cechNerveMap U y θ) =
      cechNerveMap (fun i ↦ (Over.post G).obj (U i)) y θ ≫
        (cechNerveObjPostIso G U (y ∘ θ)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, cechNerveObjPostIso_hom_cechNerveMap]

variable (P : Dᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The isomorphism between the Čech cochains of degree `k` of `U` with values in `G.op ⋙ P`
and those of the image family `fun i ↦ (Over.post G).obj (U i)` with values in `P`, given by
restriction along the inverses of the comparison isomorphisms. -/
noncomputable def cechCochainCompAddEquiv (k : ℕ) :
    CechCochain U (G.op ⋙ P) k ≃+ CechCochain (fun i ↦ (Over.post G).obj (U i)) P k :=
  AddEquiv.piCongrRight fun y ↦ (P.mapIso
    ((Over.forget _).mapIso (cechNerveObjPostIso G U y)).op).symm.addCommGroupIsoToAddEquiv

/-- `CategoryTheory.Presheaf.cechCochainCompAddEquiv` restricts each component. -/
lemma cechCochainCompAddEquiv_apply (k : ℕ) (c : CechCochain U (G.op ⋙ P) k)
    (y : Fin (k + 1) → ι) :
    cechCochainCompAddEquiv G U P k c y = P.map (cechNerveObjPostIso G U y).inv.left.op (c y) :=
  rfl


/-- The isomorphism between the Čech cosimplicial abelian group of `U` with values in
`G.op ⋙ P` and that of the image family `fun i ↦ (Over.post G).obj (U i)` with values in
`P`. -/
noncomputable def cechCosimplicialObjectCompIso :
    (cechCosimplicialObject U).obj (G.op ⋙ P) ≅
      (cechCosimplicialObject fun i ↦ (Over.post G).obj (U i)).obj P :=
  NatIso.ofComponents (fun k ↦ (cechCochainCompAddEquiv G U P k.len).toAddCommGrpIso)
    fun {k m} θ ↦ AddCommGrpCat.ext fun c ↦ funext fun y ↦ by
      change P.map (cechNerveObjPostIso G U y).inv.left.op
          (P.map ((Over.post G).map (cechNerveMap U y θ.toOrderHom)).left.op
            (c (y ∘ θ.toOrderHom))) =
        P.map (cechNerveMap _ y θ.toOrderHom).left.op
          (P.map (cechNerveObjPostIso G U (y ∘ θ.toOrderHom)).inv.left.op
            (c (y ∘ θ.toOrderHom)))
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← P.map_comp,
        ← P.map_comp, ← op_comp, ← op_comp, ← Over.comp_left, ← Over.comp_left,
        cechNerveObjPostIso_inv_cechNerveMap]

/-- The Čech complex of `U` with values in `G.op ⋙ P` is isomorphic to the Čech complex of the
image family `fun i ↦ (Over.post G).obj (U i)` with values in `P`. -/
noncomputable def cechComplexCompIso :
    (cechComplex U).obj (G.op ⋙ P) ≅
      (cechComplex fun i ↦ (Over.post G).obj (U i)).obj P :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
    (cechCosimplicialObjectCompIso G U P)

/-- Exactness of Čech complexes in positive degrees transports along a functor `G` such that
`Over.post G` preserves finite products. -/
theorem exactAt_cechComplex_comp_iff (q : ℕ) :
    ((cechComplex U).obj (G.op ⋙ P)).ExactAt (q + 1) ↔
      ((cechComplex fun i ↦ (Over.post G).obj (U i)).obj P).ExactAt (q + 1) :=
  ⟨fun h ↦ h.of_iso (cechComplexCompIso G U P),
    fun h ↦ h.of_iso (cechComplexCompIso G U P).symm⟩

end CategoryTheory.Presheaf
