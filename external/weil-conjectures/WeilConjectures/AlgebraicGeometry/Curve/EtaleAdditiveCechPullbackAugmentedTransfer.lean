/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackTotalTransfer

/-! # Augmentation-preserving pullback maps of the additive Čech complexes
Source: Stacks Project, Tags 01FD, 01FB and 03P2.
(blueprint: lem-pbc-etale-additive-cech-pullback-augmented-transfer) -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_structural_resolution_comparison
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf) :
    ∃ α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex,
      I.ι.f 0 ≫ α.f 0 = Scheme.etaleAdditiveSheafToLowerStar g ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0) := by
  classical
  let G := Etale.lowerStar AddCommGrpCat.{u + 1} g
  let K := (G.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
  have (n : ℕ) : Injective (K.X n) := G.injective_obj (J.cocomplex.X n)
  let b₀ : I.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru
    (Scheme.etaleAdditiveSheafToLowerStar g ≫ G.map (J.ι.f 0)) (I.ι.f 0)
  have hb₀ : I.ι.f 0 ≫ b₀ = Scheme.etaleAdditiveSheafToLowerStar g ≫
      G.map (J.ι.f 0) := by simp [b₀]
  have hz : I.ι.f 0 ≫ (b₀ ≫ K.d 0 1) = 0 := by
    rw [← Category.assoc, hb₀, Category.assoc]
    change Scheme.etaleAdditiveSheafToLowerStar g ≫
      G.map (J.ι.f 0) ≫ G.map (J.cocomplex.d 0 1) = 0
    rw [← G.map_comp, J.ι_f_zero_comp_complex_d, G.map_zero, comp_zero]
  let b₁ := I.exact₀.descToInjective (b₀ ≫ K.d 0 1) hz
  have hb₁ : b₀ ≫ K.d 0 1 = I.cocomplex.d 0 1 ≫ b₁ :=
    (I.exact₀.comp_descToInjective _ _).symm
  let b : I.cocomplex ⟶ K := CochainComplex.mkHom _ _ b₀ b₁ hb₁
    (fun n data ↦ by
      rcases data with ⟨f, f', w⟩
      have hz' : I.cocomplex.d n (n + 1) ≫ (f' ≫ K.d (n + 1) (n + 2)) = 0 := by
        rw [← Category.assoc, ← w, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero]
      exact ⟨(I.exact_succ n).descToInjective _ hz',
        ((I.exact_succ n).comp_descToInjective _ hz').symm⟩)
  exact ⟨b, hb₀⟩

/-- Pullback and refinement give augmentation-preserving global and total cochain maps.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1 (double-complex maps),
Tag 01FB, resolution comparison, and Tag 03P2, structural-function coordinates.
(blueprint: lem-pbc-etale-additive-cech-pullback-augmented-transfer)

Proof: The right adjoint g_* of the monomorphism-preserving etale inverse image
preserves injectives, so every g_*J^n is injective. Extend the structural coefficient
map followed by g_*J augmentation across the augmentation of I to get α^0. Its
composite with the next differential vanishes on that augmentation; exact₀ and
injectivity supply α^1. Inductively the preceding commuting square and square-zero
identity let exact_succ and injectivity supply each succeeding component.
CochainComplex.mkHom assembles them into α, whose degree-zero equation is the
required augmentation equation. Apply exists_additiveCech_pullback_total_transfer
to this supplied α: tuplewise evaluation and restriction commute with both
differentials, giving the total map and the alpha and beta component equations.
Empty families give zero total maps; degree zero, empty intersections and empty
schemes need no extra assumptions. -/
theorem exists_additiveCech_pullback_augmented_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (n : ℕ) :
    ∃ α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex,
      I.ι.f 0 ≫ α.f 0 = Scheme.etaleAdditiveSheafToLowerStar g ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0) ∧
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal V J,
      (additiveCechAlpha U I n ≫ t.f n =
        (Etale.globalResolutionSectionTransfer g I.cocomplex J.cocomplex α).f n ≫
        additiveCechAlpha V J n) ∧
      (∀ (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)
        (x' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).X n),
        (∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                x' =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    x))) → t.f n (additiveCechBeta U I n x) = additiveCechBeta V J n x') := by
  obtain ⟨α, hα⟩ := exists_structural_resolution_comparison g I J
  obtain ⟨t, htα, htβ⟩ :=
    exists_additiveCech_pullback_total_transfer g U V hinter I J α hα n
  exact ⟨α, hα, t, htα, htβ⟩

end AlgebraicGeometry.Scheme.Modules
