/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone


public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalBaseChangeCone

/-! # Strict-local module restriction: one step of the comparison

Source: Stacks Project, Tag 03Q9, degree zero and canonical restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The canonical linear restriction maps are compatible with pointed affine refinement.
Source: Stacks Project, Tag 03Q9, proof, canonical restriction maps.
(blueprint: lem-weil-pbc-strict-local-module-restriction-naturality).

Proof: Write p for the projection to X and B for the neighbourhood base-change diagram.
The strict-henselization cone legs commute with every refinement. After pullback symmetry,
pullback extensionality therefore gives δ_j ≫ p.Etale.map (B.map a) = δ_k.
Naturality of the module adjunction unit at B.map a identifies restriction before the unit
with restriction after the unit. Contravariant functoriality of p⁻¹F and the preceding
identity then identify restriction along the two graphs. Postcompose with the same inverse
terminal-section/global-section isomorphism. This yields the displayed equation. It needs
no qcqs hypothesis and holds for empty schemes and the zero ring. -/
theorem qcqsStrictLocalRestriction_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (r : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      F.obj.obj (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (hr : ∀ j, r j =
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    (pullback.fst f (Scheme.strictLocalizationToBase s))).unit.app F).hom.app
      (op (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))) ≫
    ((upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F).obj.map
        (MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)).op ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (pullback f (Scheme.strictLocalizationToBase s)))
        (Scheme.Etale.mk (𝟙 _)) Over.mkIdTerminal)).inv.app _) :
    ∀ {j k : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)} (a : j ⟶ k),
      F.obj.map ((Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale).map a).op ≫
        r j = r k := by
  classical
  intro j k a
  let B := Scheme.strictHenselizationEtaleDiagram s ⋙ f.Etale
  let p := pullback.fst f (Scheme.strictLocalizationToBase s)
  let H := (upperStar (ModuleCat.{u + 1} Λ) p).obj F
  let δ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (pullback f (Scheme.strictLocalizationToBase s))) ⟶
      (pullback.fst f (Scheme.strictLocalizationToBase s)).Etale.obj
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
        Scheme.strictHenselizationBaseChangeMap f s j)
      (𝟙 _)
      (by
        change (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
          Scheme.strictHenselizationBaseChangeMap f s j ≫ pullback.snd _ f = _
        simp only [Scheme.strictHenselizationBaseChangeMap, pullback.lift_snd,
          pullbackSymmetry_hom_comp_snd, Category.id_comp]))
    (pullback.lift_snd _ _ _)
  obtain ⟨π, _, hp, hf⟩ := Scheme.strictHenselizationAffineBaseChangeCone_exists f s
  have hπ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
      π.app j = Scheme.strictHenselizationBaseChangeMap f s j := by
    unfold Scheme.strictHenselizationBaseChangeMap
    apply pullback.hom_ext
    · exact (hf j).trans (pullback.lift_fst _ _ _).symm
    · exact (hp j).trans (pullback.lift_snd _ _ _).symm
  have hn : Scheme.strictHenselizationBaseChangeMap f s j ≫ (B.map a).left =
      Scheme.strictHenselizationBaseChangeMap f s k := by
    have h := π.naturality a
    change π.app k = π.app j ≫ (B.map a).left at h
    simpa only [hπ] using h.symm
  have hδ : δ j ≫ p.Etale.map (B.map a) = δ k := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ p =
        pullback.lift _ _ _ ≫ pullback.fst _ p
      simp only [Category.assoc, pullback.lift_fst]
      rw [pullback.lift_fst_assoc]
      simpa only [Category.assoc] using congrArg
        (fun g ↦ (pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫ g)
        hn
    · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ p =
        pullback.lift _ _ _ ≫ pullback.snd _ p
      simp only [Category.assoc, pullback.lift_snd]
      exact pullback.lift_snd _ _ _
  rw [hr j, hr k]
  change F.obj.map (B.map a).op ≫
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
        (op (B.obj j)) ≫ H.obj.map (δ j).op ≫ _) =
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
      (op (B.obj k)) ≫ H.obj.map (δ k).op ≫ _
  rw [← Category.assoc, ← Category.assoc]
  have hu := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.naturality
    (B.map a).op
  change F.obj.map (B.map a).op ≫
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
        (op (B.obj j)) =
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app F).hom.app
      (op (B.obj k)) ≫ H.obj.map (p.Etale.map (B.map a)).op at hu
  rw [hu]
  simp only [Category.assoc]
  rw [← H.obj.map_comp_assoc]
  rw [← op_comp, hδ]


end AlgebraicGeometry.Etale
