/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Mathlib.AlgebraicGeometry.Noetherian

import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConnectedEtalePresentation
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # Separate local markings of the algebraic stalk tower

## References

* Stacks Project, Tags 09BV and 09C6
* Stacks Project, the construction of the normalized algebraic stalk diagram, with the bounded
  finite cohomology version of finite-ring local constancy
* Tag 09BV, first paragraph before the inverse system of isomorphism sheaves
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

private instance : etalePrecoverage.{u}.IsStableUnderBaseChange :=
  inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))

private theorem etale_cover_sieve_mem
    (Y : Scheme.{u}) (U : Y.ProEt) (𝒰 : Cover.{u} etalePrecoverage U.left) :
    Sieve.ofArrows (fun i ↦ ProEt.mk (𝒰.f i ≫ U.hom))
      (fun i ↦ MorphismProperty.Over.homMk (𝒰.f i) rfl) ∈ ProEt.topology Y U := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact etalePrecoverage_le_proetalePrecoverage U.left 𝒰.mem₀

private theorem stalk_homology_finite
    (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (z : Z)
    (L : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (q : ℤ) (h : IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj L)) :
    Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} B) q).obj
      ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Z.uliftPointSmallEtale z).sheafFiber (A := ModuleCat.{u + 1} B))
        (Functor.additive_of_preserves_binary_products _) _ _).obj L)) := by
  let F := (Z.uliftPointSmallEtale z).sheafFiber (A := ModuleCat.{u + 1} B)
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have := h
  have hfin : ConcreteCategory.IsFinitelyGenerated
      (((pointSmallEtale (Z.algClosurePoint z)).sheafFiber
        (A := ModuleCat.{u + 1} B)).obj ((DerivedCategory.homologyFunctor _ q).obj L)) :=
    IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (AlgebraicClosure (Z.residueField z)) (Z.algClosurePoint z)
  let e := ((pointSmallEtale (Z.algClosurePoint z)).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} B)).app ((DerivedCategory.homologyFunctor _ q).obj L)
  have hfin' : ConcreteCategory.IsFinitelyGenerated
      (F.obj ((DerivedCategory.homologyFunctor _ q).obj L)) := hfin.of_iso e.symm
  exact (ModuleCat.isFinitelyGenerated_iff _).mp
    (hfin'.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app L))

private theorem connected_presentation_markings
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (V : Y.Etale) (P : LisseTowerConnectedEtalePresentation X Y g d M V)
    (U : Y.ProEt) (b : U ⟶ (toProEt Y).obj V) (n : ℕ) :
    ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj
          ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
            ((V.left.uliftPointSmallEtale P.point).sheafFiber (A := ModuleCat.{u + 1}
              (AdicCompletion d.ideal A ⧸
                (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
            (Functor.additive_of_preserves_binary_products _) _ _).obj (P.level n)) ≅
            (adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  classical
  let C := AdicCompletion d.ideal A
  let J := d.ideal.map (algebraMap A C)
  let B := C ⧸ J ^ (n + 1)
  have : Finite B := Finite.of_surjective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n).surjective
  have := P.connected
  obtain ⟨𝒰, h𝒰⟩ :=
    (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy V.left B
      (P.level n) (P.bounded n) (P.lisse n)).2.2.2 P.connected
        (AlgebraicClosure (V.left.residueField P.point)) (V.left.algClosurePoint P.point)
  let 𝒲 := 𝒰.pullback₁ b.left
  let T := Sieve.ofArrows (fun i ↦ ProEt.mk (𝒲.f i ≫ U.hom))
    (fun i ↦ MorphismProperty.Over.homMk (𝒲.f i) rfl)
  refine ⟨T, etale_cover_sieve_mem Y U 𝒲, ?_⟩
  intro W w hw
  obtain ⟨i, a, _ha⟩ := (Sieve.mem_ofArrows_iff _ _ w).mp hw
  let Z : V.left.Etale := Etale.mk (𝒰.f i)
  have hab : 𝒰.pullbackHom b.left i ≫ 𝒰.f i ≫ V.hom =
      𝒲.f i ≫ U.hom := by
    rw [𝒰.pullbackHom_map_assoc]
    exact congrArg (fun k ↦ 𝒲.f i ≫ k) b.w
  let c : ProEt.mk (𝒲.f i ≫ U.hom) ⟶
      (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom)) :=
    MorphismProperty.Over.homMk (𝒰.pullbackHom b.left i) hab
  exact P.transport n Z (h𝒰 i) W (a ≫ c)

-- Preserve the original proof-binder names in the statement.
set_option linter.unusedVariables false in
/-- On a cover, one algebraic stalk tower models each level separately on a
possibly level-dependent further cover. No compatible family of markings is asserted. -/
theorem lisse_tower_stalk_level_models
    (X Y : Scheme.{u}) [IsNoetherian X] (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)))
    (hlisse : ∀ (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule g (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage g).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) :
    let C := AdicCompletion d.ideal A
    let J := d.ideal.map (algebraMap A C)
    ∃ V : Sieve (⊤_ Y.ProEt), V ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), V f →
        ∃ (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))))
          (t : ∀ n : ℕ, K (n + 1) ⟶
            (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.obj
                  (K n)),
          (∀ (n : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1)))),
            Function.Bijective (fun k : K n ⟶ N ↦ t n ≫
              (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
                (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))))).mapDerivedCategory.map
                    k)) ∧
          (∀ (n : ℕ) (q : ℤ),
            IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)) →
            IsZero ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))) q).obj (K n))) ∧
          (∀ (n : ℕ) (q : ℤ), Module.Finite (C ⧸ J ^ (n + 1))
            ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (C ⧸ J ^ (n + 1))) q).obj (K n))) ∧
          (∀ (W : Y.ProEt) (w : W ⟶ U) (n : ℕ) (q : ℤ),
            IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
              ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
                (pbcLevelConstantComparison X d n).hom)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj
                    ((adicTowerPullback (W.hom ≫ g)
                      ((pbcAdicRings X d).obj (op n))).obj (M.level n))))) ∧
          ∀ n : ℕ, ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
            ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
              Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
                (adicTowerPullback (W.hom ≫ g)
                  ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  classical
  dsimp only
  obtain ⟨𝒱, h𝒱⟩ := lisse_tower_connected_etale_presentation X Y g d M hbounded hlisse
  let V := Sieve.ofArrows (fun i ↦ (toProEt Y).obj (𝒱.etalePrecoverageToEtale i))
    (fun i ↦ terminal.from _)
  have hV : V ∈ ProEt.topology Y (⊤_ Y.ProEt) := by
    let U₀ : Y.ProEt := ProEt.mk (𝟙 Y)
    let e : (⊤_ Y.ProEt) ≅ U₀ :=
      terminalIsoIsTerminal (MorphismProperty.Over.mkIdTerminal _ _)
    have hV₀ : Sieve.ofArrows
        (fun i ↦ (toProEt Y).obj (𝒱.etalePrecoverageToEtale i))
        (fun i ↦ (MorphismProperty.Over.homMk (𝒱.f i) (Category.comp_id _) :
          (toProEt Y).obj (𝒱.etalePrecoverageToEtale i) ⟶ U₀)) ∈
          ProEt.topology Y U₀ := by
      apply Precoverage.generate_mem_toGrothendieck
      rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
      exact etalePrecoverage_le_proetalePrecoverage Y 𝒱.mem₀
    apply (GrothendieckTopology.pullback_mem_iff_of_isIso (i := e.inv)).mp
    apply (ProEt.topology Y).superset_covering ?_ hV₀
    intro W w hw
    obtain ⟨i, a, _ha⟩ := (Sieve.mem_ofArrows_iff _ _ w).mp hw
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, a, terminalIsTerminal.hom_ext _ _⟩
  refine ⟨V, hV, ?_⟩
  intro U f hf
  obtain ⟨i, b, _hb⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
  let P := (h𝒱 i).some
  let Z := 𝒱.etalePrecoverageToEtale i
  let K (n : ℕ) := (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Z.left.uliftPointSmallEtale P.point).sheafFiber (A := ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (Functor.additive_of_preserves_binary_products _) _ _).obj (P.level n)
  refine ⟨K, P.transition, P.universal, ?_, ?_, ?_, ?_⟩
  · intro n q hq
    let F := (Z.left.uliftPointSmallEtale P.point).sheafFiber
      (A := ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    exact (F.map_isZero (P.vanishing n q hq)).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app (P.level n)).symm
  · intro n q
    exact stalk_homology_finite Z.left _ P.point (P.level n) q (P.lisse n q)
  · intro W w n q
    exact P.refinementLisse W (w ≫ b) n q
  · intro n
    exact connected_presentation_markings X Y g d M Z P U b n

end AlgebraicGeometry.Scheme
