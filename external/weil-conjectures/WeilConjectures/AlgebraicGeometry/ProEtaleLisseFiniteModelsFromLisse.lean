/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # ProEtaleLisseFiniteModelsFromLisse

Source: Stacks Project, Tag 099Y, proof of lemma-compare-locally-constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- A fixed-coefficient lisse pro-étale sheaf admits finite constant models.
Source: Stacks Project, Tag 099Y, proof of `lemma-compare-locally-constant`.
On each member of a trivializing cover, the constant model is identified with a
geometric stalk; the stalk finiteness therefore makes the model finite.
(auxiliary; not a blueprint node) -/
theorem finite_models_of_fixed_lisse
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hF : IsLocallyConstantProEtaleFixedModuleSheaf X Λ F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricFixedModuleStalk x Λ F)) :
    ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} Λ) (g i)).obj F) ≅
            (constantSheaf (Scheme.ProEt.topology (W i))
              (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  obtain ⟨⟨I, U, f, hf, hmodels⟩, hstalks⟩ := hF
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  let E : PreZeroHypercover X := ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩
  have : QuasiCompactCover E := presieve₀_mem_qcPrecoverage_iff.mp hg.1
  let E' : PreZeroHypercover X :=
    ⟨{i : I // Nonempty (U i).left}, fun i ↦ (U i.1).left, fun i ↦ (U i.1).hom⟩
  have : QuasiCompactCover E' := by
    constructor
    intro V hV
    obtain ⟨n, a, W, hW, hcov⟩ :=
      QuasiCompactCover.exists_isAffineOpen_of_isCompact E hV.isCompact
    refine IsCompactOpenCovered.of_finite
      (fun j : {j : Fin n // Nonempty (U (a j)).left} ↦ ⟨a j.1, j.2⟩)
      (fun j ↦ W j.1) (fun j ↦ (hW j.1).isCompact) ?_
    rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      exact ⟨j.1, y, hy, rfl⟩
    · rintro ⟨j, y, hy, rfl⟩
      exact ⟨⟨j, ⟨y⟩⟩, y, hy, rfl⟩
  refine ⟨E'.I₀, E'.X, E'.f,
    ⟨presieve₀_mem_qcPrecoverage_iff.mpr ‹QuasiCompactCover E'›, ?_⟩, ?_⟩
  · rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ by
      have hweak := hg.2
      rw [Scheme.ofArrows_mem_precoverage_iff] at hweak
      obtain ⟨i, y, hy⟩ := hweak.1 x
      exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩, fun i ↦ (U i.1).prop⟩
  · rintro ⟨i, hi⟩
    obtain ⟨M, ⟨e⟩⟩ := hmodels i
    let w : (U i).left := Classical.choice hi
    let Ω := AlgebraicClosure ((U i).left.residueField w)
    let y : Spec (.of Ω) ⟶ (U i).left := (SpecToEquivOfField Ω _).2
      ⟨w, CommRingCat.ofHom (algebraMap ((U i).left.residueField w) Ω)⟩
    let x := y ≫ (U i).hom
    let Φ := AlgebraicGeometry.ProEtale.geometricPoint x
    let z : Φ.fiber.obj (U i) := ⟨Over.homMk y rfl⟩
    let estalk : proEtaleGeometricFixedModuleStalk x Λ F ≅ M :=
      AlgebraicGeometry.ProEtale.geometricStalkIsoFiber x Λ F ≪≫
      (AlgebraicGeometry.ProEtale.sheafFiberOverIso Φ z Λ F).symm ≪≫
      (Φ.over z).sheafFiber.mapIso e ≪≫ (Φ.over z).sheafFiberConstantSheafIso M
    have : Finite (proEtaleGeometricFixedModuleStalk x Λ F) := hstalks Ω x
    have hM : Finite M := Finite.of_equiv _ estalk.toLinearEquiv.toEquiv
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let S := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} Λ)
    let r : S.functor.obj (F.over (U i)) ≅
        (AlgebraicGeometry.ProEtale.localizationRestriction
          (ModuleCat.{u + 1} Λ) (U i).hom (U i).prop).obj F :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} Λ) (Over.mkIdTerminal (X := U i))).app M
    exact ⟨M, hM, ⟨
      (AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} Λ) (U i).hom (U i).prop).app F ≪≫
      r.symm ≪≫ S.functor.mapIso e ≪≫ c⟩⟩

end AlgebraicGeometry.Scheme
