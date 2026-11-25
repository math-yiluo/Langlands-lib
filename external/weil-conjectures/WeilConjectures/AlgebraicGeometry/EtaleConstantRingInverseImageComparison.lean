/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant-ring comparison for etale inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 03D6, 03D7, 04JC;
Sites and Sheaves, Example 0H7J
(blueprint: lem-weil-pbc-constant-ring-inverse-image-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- Constant rings commute with the ring inverse image, with the compatible abelian lift.
Source: Stacks Project, Sites and Sheaves, Example 0H7J; Modules on Sites, 03D2.
(blueprint: lem-weil-pbc-constant-ring-inverse-image-comparison).

Proof: Choose the compatible ring and abelian lifts of
`etaleInverseImageAlgebraicStructures`. For any ring sheaf F on U, the ring
adjunction and the constant-sheaf adjunction identify maps from Lr(RV) to F
with maps from R to F(U): the direct image has the same global sections.
The constant-sheaf adjunction on U identifies these with maps from RU to F.
Yoneda gives c. Define gamma as the adjunct of c.hom. Evaluating the composite
bijection on the identity of RU shows that gamma sends every constant section
r to the constant section r after base change. The two compatibility equations
are the hom-equivalence equations of the chosen algebraic lifts. -/
theorem etaleConstantRingInverseImageComparison (U V : Scheme.{u}) (f : U ⟶ V)
    (R : CommRingCat.{u + 1}) :
    (fun (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (etaV : ((Functor.const V.Etaleᵒᵖ).obj R) ⟶ RV.obj)
      (etaU : ((Functor.const U.Etaleᵒᵖ).obj R) ⟶ RU.obj) =>
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (er : Lr ⋙ sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology ≅ sheafForget (D :=
        CommRingCat.{u + 1}) V.smallEtaleTopology ⋙ Scheme.etaleSetPullback f)
      (ea : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ sheafForget (D := AddCommGrpCat.{u + 1})
        U.smallEtaleTopology ≅ sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology ⋙
        Scheme.etaleSetPullback f)
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU),
    ar.homEquiv RV RU c.hom = gamma ∧
    (∀ (W : V.Etaleᵒᵖ) (r : R),
      gamma.hom.app W ((etaV).app W r) =
        (etaU).app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) ∧
    (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
      (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).map (ar.homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          CommRingCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := CommRingCat.{u +
          1}) U.smallEtaleTopology).obj F)
          (er.inv.app G ≫ (sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).map h)) ∧
    (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : (Etale.upperStar
        AddCommGrpCat.{u + 1} f).obj G ⟶ F),
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := AddCommGrpCat.{u
          + 1}) U.smallEtaleTopology).obj F)
          (ea.inv.app G ≫ (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).map h)) )
      ((constantSheaf V.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      (toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj R))
      (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj R)) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  obtain ⟨_, ea, da, Lr, ar, er, dr, hda, hdr, ha, _, hr, _, _, _⟩ :=
    etaleInverseImageAlgebraicStructures U V f
  -- Both composite left adjoints represent maps from R to sections over b(T).
  let T := ⊤_ V.Etale
  let hT : IsTerminal T := terminalIsTerminal
  let hGT : IsTerminal (b.obj T) := hT.isTerminalObj b T
  let av := constantSheafAdj V.smallEtaleTopology CommRingCat.{u + 1} hT
  let au := constantSheafAdj U.smallEtaleTopology CommRingCat.{u + 1} hGT
  let d := b.sheafPushforwardContinuousCompSheafSectionsObjIso CommRingCat.{u + 1}
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    (Opposite.op T)
  let ac := (av.comp ar).ofNatIsoRight d
  let c := (ac.leftAdjointUniq au).app R
  let gamma := ar.homEquiv _ _ c.hom
  refine ⟨Lr, ar, er, ea, gamma, c, rfl, ?_, ?_, ?_⟩
  · have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app ac au R
    have hv : av.homEquiv R _ gamma = au.unit.app R := by
      change ac.homEquiv R _ c.hom = _ at ht
      dsimp only [ac] at ht
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at ht
      change av.homEquiv R _ (ar.homEquiv _ _ c.hom) ≫ 𝟙 _ = au.unit.app R at ht
      simpa only [Category.comp_id] using ht
    let etaV := toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj R)
    let etaU := toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj R)
    have hv' : etaV.app (Opposite.op T) ≫ gamma.hom.app (Opposite.op T) =
        etaU.app (Opposite.op (b.obj T)) := by
      change etaV.app (Opposite.op T) ≫ gamma.hom.app (Opposite.op T) =
        etaU.app (Opposite.op (b.obj T)) at hv
      exact hv
    -- Naturality propagates the equation at the terminal object to every object.
    intro W r
    have hn := (etaV ≫ gamma.hom).naturality (hT.from W.unop).op
    have hu := etaU.naturality (b.map (hT.from W.unop)).op
    have hw : etaV.app W ≫ gamma.hom.app W = etaU.app (b.op.obj W) := by
      calc
        etaV.app W ≫ gamma.hom.app W =
            (etaV.app (Opposite.op T) ≫ gamma.hom.app (Opposite.op T)) ≫
              ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R).obj.map
                (b.map (hT.from W.unop)).op := by
          change 𝟙 R ≫ (etaV.app W ≫ gamma.hom.app W) = _ at hn
          exact (Category.id_comp _).symm.trans hn
        _ = etaU.app (Opposite.op (b.obj T)) ≫
              ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R).obj.map
                (b.map (hT.from W.unop)).op := by rw [hv']
        _ = etaU.app (b.op.obj W) := by
          change 𝟙 R ≫ etaU.app (b.op.obj W) = _ at hu
          exact hu.symm.trans (Category.id_comp _)
    exact congrArg (fun k ↦ k r) hw
  · intro G F h
    have hh := hr G F h
    apply Sheaf.hom_ext
    ext W x
    have hx := congrArg (fun k ↦ k.hom.app W x) hh
    change (dr.hom.app F).hom.app W
      (((sheafForget V.smallEtaleTopology).map (ar.homEquiv G F h)).hom.app W x) = _ at hx
    exact (hdr F W _).symm.trans hx
  · intro G F h
    have hh := ha G F h
    apply Sheaf.hom_ext
    ext W x
    have hx := congrArg (fun k ↦ k.hom.app W x) hh
    change (da.hom.app F).hom.app W
      (((sheafForget V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          G F h)).hom.app W x) = _ at hx
    exact (hda F W _).symm.trans hx

end AlgebraicGeometry
