/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackUnitGenerators
import WeilConjectures.AlgebraicGeometry.EtaleSetConstantPullbackComposition

/-! # Composition transport on constant generators

Source: Stacks Project, Tags 03CB, 03CC, 03P5, and 0A3H, final proof paragraph.
(blueprint: lem-weil-pbc-etale-set-constant-transport-generators).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Maps out of constant sheaves transport compatibly with the chosen composition
comparison on every constant generator. No invertibility of the map is required.

Source: Stacks Project, Tags 03CB, 03CC, 03P5, and 0A3H, final proof paragraph.
(blueprint: lem-weil-pbc-etale-set-constant-transport-generators).

Proof: the unit equation for the left-adjoint comparison defining
etaleSetConstantPullbackComparison identifies the pullback of each constant generator
with the constant generator of the same value. First check this at the terminal etale
object, where both adjunctions have right adjoint global sections; restrict along the
unique map from any etale W and use naturality of both units to obtain it on W.
For v after h, the two constant comparisons have the same composite unit equation.
The universal property of sheafification and the inverse-image adjunction makes them
equal. Whisker this equality by the map tau; unit naturality moves tau past the unit.
Associativity of the chosen inverse-image comparisons, the final clause of
etaleSetInverseImageCompositionUnits, then pastes the comparison for s and h with
that for h composed with s and v. Evaluate the resulting equality of sheaf morphisms
at the pullback of W and at its constant generator e. The associativity transport is
from (v composed with h) composed with s to v composed with (h composed with s),
which gives the eqToHom in the displayed direction. The argument uses no smallness,
nonemptiness, connectedness, or field hypothesis on A or the schemes. -/
theorem etaleSetConstantTransportGenerators
    (S P U V : Scheme.{u}) (s : P ⟶ S) (h : U ⟶ P) (v : V ⟶ U)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (A : Type (u + 1))
    (τ : (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A ⟶
      (Scheme.etaleSetPullback s).obj F) (W : U.Etale) (e : A) :
    (((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
      S U V (h ≫ s) v).hom.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W))
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ v) (Type (u + 1))
        (U.smallGrothendieckTopology @Etale)
        (V.smallGrothendieckTopology @Etale)).unit.app
          ((Scheme.etaleSetPullback (h ≫ s)).obj F)).hom.app (op W)
        (((etaleSetConstantPullbackComparison h).inv.app A ≫
          (Scheme.etaleSetPullback h).map τ ≫
          ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
            S P U s h).hom.app F).hom.app (op W)
          ((toSheafify U.smallEtaleTopology
            ((Functor.const U.Etaleᵒᵖ).obj A)).app (op W) e))) =
      (((etaleSetConstantPullbackComparison (v ≫ h)).inv.app A ≫
        (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg
          (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s))).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
        ((toSheafify V.smallEtaleTopology
          ((Functor.const V.Etaleᵒᵖ).obj A)).app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e)  := by
  let c := Classical.choose etaleSetInverseImageCompositionUnits.2.2
  let x := (etaleSetConstantPullbackComparison h).inv.app A ≫
    (Scheme.etaleSetPullback h).map τ ≫ (c S P U s h).hom.app F
  have hn := etaleSetInverseImageCompositionUnits.2.1 U V v
    ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj A)
    ((Scheme.etaleSetPullback (h ≫ s)).obj F) x W
    ((toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj A)).app (op W) e)
  rw [hn, etaleSetConstantPullbackUnitGenerators U V v A W e]
  have hc : (etaleSetConstantPullbackComparison v).inv.app A ≫
      (Scheme.etaleSetPullback v).map x ≫ (c S U V (h ≫ s) v).hom.app F =
      (etaleSetConstantPullbackComparison (v ≫ h)).inv.app A ≫
        (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        (c S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s)) := by
    dsimp only [x]
    simp only [Functor.map_comp, Category.assoc]
    rw [(Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
      S P U V s h v F]
    rw [← Category.assoc ((Scheme.etaleSetPullback v).map
      ((Scheme.etaleSetPullback h).map τ))]
    rw [show (Scheme.etaleSetPullback v).map ((Scheme.etaleSetPullback h).map τ) ≫
      (c P U V h v).hom.app ((Scheme.etaleSetPullback s).obj F) =
      (c P U V h v).hom.app _ ≫ (Scheme.etaleSetPullback (v ≫ h)).map τ from
        (c P U V h v).hom.naturality τ]
    simpa only [Category.assoc] using congrArg
      (fun q ↦ q ≫ (Scheme.etaleSetPullback (v ≫ h)).map τ ≫
        (c S P V s (v ≫ h)).hom.app F ≫
        eqToHom (congrArg (fun k : V ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
          (Category.assoc v h s)))
      (etaleSetConstantPullbackComposition P U V h v A)
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun k ↦ k.hom) hc)
    (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)))
      ((toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj A)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj W)) e)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at he
  convert he using 1
  simp only [c, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]

end AlgebraicGeometry
