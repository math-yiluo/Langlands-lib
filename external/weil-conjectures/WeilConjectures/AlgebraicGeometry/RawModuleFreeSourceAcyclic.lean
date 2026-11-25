/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso
import all WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison

/-! # Acyclicity for the pulled-back free abelian source

Source: Stacks Project, Tag 03FD, second paragraph of its proof.
(blueprint: lem-sbc-raw-module-free-source-acyclic).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def rawSourceSectionsEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawModuleScalarComparison.freeAbelian S U) ⟶ G) ≃+
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) where
  toEquiv := RawRestrictedComparison.representedEquiv f U G
  map_add' g h := by
    change RawRestrictedComparison.representedEquiv f U G (g + h) =
      RawRestrictedComparison.representedEquiv f U G g +
        RawRestrictedComparison.representedEquiv f U G h
    erw [RawRestrictedComparison.representedEquiv_apply,
      RawRestrictedComparison.representedEquiv_apply,
      RawRestrictedComparison.representedEquiv_apply]
    rw [Functor.map_add]
    let W := (MorphismProperty.Over.pullback @Etale ⊤ f).obj U
    change (RawRestrictedComparison.sectionsIso W G).hom.hom
      (((RawRestrictedComparison.underivedSections W).map g).hom
        (RawRestrictedComparison.generator f U) +
       ((RawRestrictedComparison.underivedSections W).map h).hom
        (RawRestrictedComparison.generator f U)) = _
    exact map_add _ _ _

private noncomputable def rawSourceSectionsIso
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) :
    preadditiveCoyoneda.obj (op ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawModuleScalarComparison.freeAbelian S U))) ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) :=
  NatIso.ofComponents (fun G ↦ (rawSourceSectionsEquiv f U G).toAddCommGrpIso) (by
    intro G H φ
    ext g
    change RawRestrictedComparison.representedEquiv f U H (g ≫ φ) =
      φ.hom.app _ (RawRestrictedComparison.representedEquiv f U G g)
    dsimp only [RawRestrictedComparison.representedEquiv, Equiv.trans_apply]
    erw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right]
    rfl)

/-- Forgotten injective modules are acyclic for sections corepresented by this source.
Source: Stacks Project, Tag 03FD, second proof paragraph and the sections adjunction.
(blueprint: lem-sbc-raw-module-free-source-acyclic).

Proof: Pullback of the represented sheaf U is represented by X times_S U.
Pullback commutes with free abelian sheafification. Thus the source in the
statement is the free abelian sheaf of that etale object of X. Sheafification,
free abelian and Yoneda adjunctions give a natural additive isomorphism from
Hom(source,-) to evaluation at X times_S U. Right derived functors respect this
isomorphism. Tag 03FD gives zero positive right derived evaluation on the
underlying abelian sheaf of every injective module sheaf. One may transport
ModuleCat-valued sheaves to modules over the constant ring sheaf without
changing underlying sections or injectivity. Therefore the rightAcyclic
condition holds in every positive degree. The empty object and zero ring give
the same conclusion; the underlying abelian sheaf need not be injective. -/
theorem rawModuleFreeSource_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Injective I] :
    (preadditiveCoyoneda.obj (op
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawModuleScalarComparison.freeAbelian S U)))).rightAcyclic
      ((moduleAbelianForget Λ X).obj I) := by
  let s := rawSourceSectionsIso f U
  intro n
  let d : (preadditiveCoyoneda.obj (op
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawModuleScalarComparison.freeAbelian S U)))).rightDerived (n + 1) ≅
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))).rightDerived (n + 1) :=
    { hom := NatTrans.rightDerived s.hom (n + 1)
      inv := NatTrans.rightDerived s.inv (n + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, s.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, s.inv_hom_id,
        NatTrans.rightDerived_id] }
  exact (moduleAbelianForget_injective_evaluation_acyclic Λ X I
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) n).of_iso
      (d.app ((moduleAbelianForget Λ X).obj I))


end AlgebraicGeometry.Etale
