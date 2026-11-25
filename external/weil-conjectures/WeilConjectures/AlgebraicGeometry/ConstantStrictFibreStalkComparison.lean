/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import all WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality

/-! # Degree-zero strict-local stalk comparison for constant coefficients

Source: Stacks Project, Tag 03Q9, applied in Tag 09Z5.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_two_pullbacks
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {Y X Z : Scheme.{u}} (f : X ⟶ Y) (p : Z ⟶ X) (V : Y.Etale)
    (T : Z.Etale) (σ : T ⟶ p.Etale.obj (f.Etale.obj V)) :
    let A := ModuleCat.{u + 1} Λ
    let CY := (constantSheaf Y.smallEtaleTopology A).obj M
    let F := (upperStar A f).obj CY
    let H := (upperStar A p).obj F
    let ec := (upperStar A p).mapIso ((Scheme.upperStarConstantSheafIso A f).app M) ≪≫
      (Scheme.upperStarConstantSheafIso A p).app M
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V) ≫
      ((upperStarLowerStarAdjunction A f).unit.app CY).hom.app (op V) ≫
      ((upperStarLowerStarAdjunction A p).unit.app F).hom.app (op (f.Etale.obj V)) ≫
      H.obj.map σ.op ≫ ec.hom.hom.app (op T) =
    (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app (op T) := by
  let A := ModuleCat.{u + 1} Λ
  let CY := (constantSheaf Y.smallEtaleTopology A).obj M
  let CX := (constantSheaf X.smallEtaleTopology A).obj M
  let CZ := (constantSheaf Z.smallEtaleTopology A).obj M
  let F := (upperStar A f).obj CY
  let H := (upperStar A p).obj F
  let cf := ((Scheme.upperStarConstantSheafIso A f).app M).hom
  let cp := ((Scheme.upperStarConstantSheafIso A p).app M).hom
  let ηf := (upperStarLowerStarAdjunction A f).unit.app CY
  let ηp := (upperStarLowerStarAdjunction A p).unit.app F
  let ηp' := (upperStarLowerStarAdjunction A p).unit.app CX
  have hn := ((upperStar A p).map cf).hom.naturality σ.op
  have hu := (upperStarLowerStarAdjunction A p).unit.naturality cf
  have hf := constantModuleTransition_generators Λ M f (op V)
  have hp := constantModuleTransition_generators Λ M p (op (f.Etale.obj V))
  change (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V) ≫
    ηf.hom.app (op V) ≫ cf.hom.app (op (f.Etale.obj V)) = _ at hf
  change (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
    (op (f.Etale.obj V)) ≫ ηp'.hom.app _ ≫ cp.hom.app _ = _ at hp
  change (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app (op V) ≫
    ηf.hom.app (op V) ≫ ηp.hom.app (op (f.Etale.obj V)) ≫
      H.obj.map σ.op ≫ ((upperStar A p).map cf).hom.app (op T) ≫ cp.hom.app (op T) = _
  erw [reassoc_of% hn]
  have huV := NatTrans.congr_app (congrArg (fun k ↦ k.hom) hu) (op (f.Etale.obj V))
  change cf.hom.app (op (f.Etale.obj V)) ≫ ηp'.hom.app _ =
    ηp.hom.app _ ≫ ((upperStar A p).map cf).hom.app _ at huV
  erw [← reassoc_of% huV]
  erw [reassoc_of% hf]
  erw [cp.hom.naturality σ.op]
  erw [reassoc_of% hp]
  dsimp only [A, constantSheaf, Functor.comp_obj, Functor.op_obj]
  simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp] using
    ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj M)).naturality σ.op).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical degree-zero strict-local stalk comparison for constant coefficients
carries the unit applied to a coefficient to the same constant section on the strict fibre.
Source: Stacks Project, Tag 03Q9, degree zero and its restriction construction,
as used in the first assertion of Tag 09Z5.
(blueprint: lem-weil-pbc-constant-strict-fibre-stalk-comparison)

Proof: Apply the existing qcqs strict-local module comparison to f^* M_Y.
Its target is global sections of p^* f^* M_Y, where p is the projection from the
strict fibre to X. Apply twice the canonical inverse-image/constant-sheaf
isomorphism, then evaluate global sections at the identity etale object.
This composite is invertible because each factor is invertible.
For the coefficient equation, choose any representative affine pointed
neighbourhood. Its map to the terminal object carries its marked point to t,
since the terminal object's point fibre has exactly one element. Naturality of
the constant-presheaf sheafification map and the stalk germ maps therefore
express the terminal coefficient germ on this neighbourhood. Naturality of
the unit and the comparison's defining germ formula give first the unit for f,
then the unit for p, followed by restriction along the strict-local limit leg.
The canonical constant-pullback comparisons preserve constant generators.
Move these comparisons through the restrictions and through the second unit
by naturality. Applying the generator equation first for f and then for p
leaves the constant generator on the iterated pullback. Naturality of
sheafification along the limit leg gives the required constant section on
the strict fibre. These are equations of module morphisms throughout.

Edge cases: no normality or connectedness hypothesis is used. If the strict fibre
is empty, the stalk and the section module both vanish and the coefficient map
is zero. Arbitrary modules and the zero coefficient ring are allowed. -/
theorem constant_strict_fibre_stalk_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (M : ModuleCat.{u + 1} Λ)
    (t : (Scheme.pointSmallEtale s).fiber.obj
      (Scheme.Etale.mk (𝟙 Y))) :
    let Φ := Scheme.pointSmallEtale s
    let Z := pullback f (Scheme.strictLocalizationToBase s)
    let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
    let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F
    ∃ r : Φ.sheafFiber.obj ((lowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj F)) ⟶
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj
        (op (Scheme.Etale.mk (𝟙 Z))),
      IsIso r ∧
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Y))) ≫
          Φ.toPresheafFiber (Scheme.Etale.mk (𝟙 Y)) t F.obj ≫ Φ.sheafFiber.map η ≫ r =
          (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
            (op (Scheme.Etale.mk (𝟙 Z))) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let Φ := Scheme.pointSmallEtale s
  let Z := pullback f (Scheme.strictLocalizationToBase s)
  let p := pullback.fst f (Scheme.strictLocalizationToBase s)
  let CY := (constantSheaf Y.smallEtaleTopology A).obj M
  let F := (upperStar A f).obj CY
  let H := (upperStar A p).obj F
  obtain ⟨Θ, hΘ⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  let ec : H ≅ (constantSheaf Z.smallEtaleTopology A).obj M :=
    (upperStar A p).mapIso ((Scheme.upperStarConstantSheafIso A f).app M) ≪≫
      (Scheme.upperStarConstantSheafIso A p).app M
  let T := Scheme.Etale.mk (𝟙 Z)
  let hT := IsTerminal.isTerminalOfObj
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ Z) T Over.mkIdTerminal
  let es := (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology A hT).app
    ((constantSheaf Z.smallEtaleTopology A).obj M)
  let r := Θ.hom ≫ (Sheaf.Γ Z.smallEtaleTopology A).map ec.hom ≫ es.hom
  refine ⟨r, inferInstance, ?_⟩
  let TY := Scheme.Etale.mk (𝟙 Y)
  have hTY : IsTerminal TY := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let := Φ.uniqueFiberObj TY hTY
  let := (Scheme.strictHenselizationAffineProperties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty
    (C := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)))
  let n := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j
  let V := (Scheme.AffineEtale.Spec Y).obj n.1
  let v := n.2
  let g : V ⟶ TY := hTY.from V
  have ht : Φ.fiber.map g v = t := Subsingleton.elim _ _
  let eY := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  have hgerm : eY.app (op TY) ≫ Φ.toPresheafFiber TY t CY.obj =
      eY.app (op V) ≫ Φ.toPresheafFiber V v CY.obj := by
    have hw := Φ.toPresheafFiber_w g v CY.obj
    rw [ht] at hw
    have he := eY.naturality g.op
    dsimp only [Functor.const_obj_map, Functor.const_obj_obj] at he
    rw [Category.id_comp] at he
    change eY.app (op V) = eY.app (op TY) ≫ CY.obj.map g.op at he
    erw [← hw, ← Category.assoc, ← he]
  let ηf := (upperStarLowerStarAdjunction A f).unit.app CY
  let ηp := (upperStarLowerStarAdjunction A p).unit.app F
  let σ := qcqsStrictLocalNeighbourhoodSection f s j
  have hΓ := (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology A hT).hom.naturality ec.hom
  change (Sheaf.Γ Z.smallEtaleTopology A).map ec.hom ≫ es.hom =
    (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology A hT).hom.app H ≫
      ec.hom.hom.app (op T) at hΓ
  have hj := hΘ j
  change Φ.toPresheafFiber V v ((lowerStar A f).obj F).obj ≫ Θ.hom =
    ηp.hom.app (op (f.Etale.obj V)) ≫ H.obj.map σ.op ≫
      (Sheaf.ΓNatIsoSheafSections Z.smallEtaleTopology A hT).inv.app H at hj
  change eY.app (op TY) ≫ Φ.toPresheafFiber TY t CY.obj ≫ Φ.sheafFiber.map ηf ≫ r = _
  erw [← Category.assoc, hgerm]
  change eY.app (op V) ≫ Φ.toPresheafFiber V v CY.obj ≫ Φ.presheafFiber.map ηf.hom ≫
    Θ.hom ≫ (Sheaf.Γ Z.smallEtaleTopology A).map ec.hom ≫ es.hom = _
  rw [Φ.toPresheafFiber_naturality_assoc]
  erw [hΓ]
  erw [reassoc_of% hj]
  simp only [Iso.inv_hom_id_app_assoc]
  exact coefficient_two_pullbacks Λ M f p V T σ

end AlgebraicGeometry.Etale
