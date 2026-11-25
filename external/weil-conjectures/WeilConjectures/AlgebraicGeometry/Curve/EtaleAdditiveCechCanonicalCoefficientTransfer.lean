/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle

/-!
# Canonical global transfer with a coefficient morphism

Source: Stacks Project, Tags 0A50, 03F3, 01F8 and 01FB.
(blueprint: lem-pbc-etale-additive-cech-canonical-coefficient-transfer)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private theorem constantSheafAdj_eval
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (k : T' ⟶ T)
    (A : AddCommGrpCat.{u + 1}) (N : Sheaf J AddCommGrpCat.{u + 1})
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (f : (constantSheaf J AddCommGrpCat.{u + 1}).obj A ⟶ N) :
    (constantSheafAdj J AddCommGrpCat.{u + 1} hT).homEquiv A N f ≫ N.obj.map k.op =
      (constantSheafAdj J AddCommGrpCat.{u + 1} hT').homEquiv A N f := by
  have hformula {S : C} (hS : IsTerminal S) :
      (constantSheafAdj J AddCommGrpCat.{u + 1} hS).homEquiv A N f =
        (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op S) ≫ f.hom.app (op S) := by
    rw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, Adjunction.comp]
  rw [hformula hT, hformula hT', Category.assoc, ← f.hom.naturality, ← Category.assoc]
  have h := (toSheafify J ((Functor.const Cᵒᵖ).obj A)).naturality k.op
  simpa using congrArg (fun t ↦ t ≫ f.hom.app (op T')) h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem section_adjunction_transfer {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : (upperStar AddCommGrpCat.{u + 1} g).obj M ⟶ N)
    (f : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ⟶ M) :
    (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale Y)).homAddEquiv _ N).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _))
      (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
        (AddCommGrpCat.of (ULift ℤ))).hom ≫
          (upperStar AddCommGrpCat.{u + 1} g).map f ≫ b) =
    N.obj.map (terminalSectionPullback g).op
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _) b |>.hom.app
        (op (Scheme.Etale.mk (𝟙 X)))
        ((((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
          (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ M).trans
            (AddCommGrpCat.uliftZMultiplesAddEquiv _)) f)) := by
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let adjY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let adjC := (adjX.comp adj).ofNatIsoRight
    (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g)
  let c := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app A).hom
  have hh : adjY.homEquiv A N
      ((Adjunction.leftAdjointUniq adjC adjY).inv.app A ≫
        (upperStar AddCommGrpCat.{u + 1} g).map f ≫ b) =
      adjC.homEquiv A N ((upperStar AddCommGrpCat.{u + 1} g).map f ≫ b) := by
    rw [Adjunction.leftAdjointUniq_inv_app, adjY.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, adjC.homEquiv_apply]
  change adjY.homEquiv A N (c ≫ (upperStar AddCommGrpCat.{u + 1} g).map f ≫ b) = _ at hh
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
  change adjY.homEquiv A N (c ≫ (upperStar AddCommGrpCat.{u + 1} g).map f ≫ b) =
    adjX.homEquiv A _ (adj.homEquiv _ N
      ((upperStar AddCommGrpCat.{u + 1} g).map f ≫ b)) ≫
        (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app N at hh
  rw [Adjunction.homEquiv_naturality_left] at hh
  let kX : Scheme.Etale.mk (𝟙 X) ⟶ ⊤_ X.Etale := terminal.from _
  let kY : Scheme.Etale.mk (𝟙 Y) ⟶ ⊤_ Y.Etale := terminal.from _
  have hs := congrArg (fun t ↦ t ≫ N.obj.map kY.op) hh
  erw [constantSheafAdj_eval Y.smallEtaleTopology terminalIsTerminal
    (MorphismProperty.Over.mkIdTerminal @Etale Y) kY A N
      (c ≫ (upperStar AddCommGrpCat.{u + 1} g).map f ≫ b)] at hs
  have square : kY ≫ (PreservesTerminal.iso g.Etale).inv =
      terminalSectionPullback g ≫ g.Etale.map kX := by
    apply (terminalIsTerminal.isTerminalObj g.Etale (⊤_ X.Etale)).hom_ext
  change _ = (adjX.homEquiv A _ (f ≫ adj.homEquiv M N b)) ≫
    N.obj.map (PreservesTerminal.iso g.Etale).inv.op ≫ N.obj.map kY.op at hs
  rw [← Functor.map_comp, ← op_comp, square, op_comp, Functor.map_comp,
    ← Category.assoc] at hs
  change _ = (adjX.homEquiv A _ (f ≫ adj.homEquiv M N b) ≫
    ((lowerStar AddCommGrpCat.{u + 1} g).obj N).obj.map kX.op) ≫
      N.obj.map (terminalSectionPullback g).op at hs
  erw [constantSheafAdj_eval X.smallEtaleTopology terminalIsTerminal
    (MorphismProperty.Over.mkIdTerminal @Etale X) kX A
      ((lowerStar AddCommGrpCat.{u + 1} g).obj N) (f ≫ adj.homEquiv M N b),
    Adjunction.homEquiv_naturality_right] at hs
  exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) hs

set_option backward.isDefEq.respectTransparency false in
/-- The canonical global transfer identity including an adjoint coefficient morphism.
Source: Stacks Project, Tags 0A50 and 03F3; this is the pointwise cocycle calculation
used in the global transfer theorem.
(blueprint: lem-pbc-etale-additive-cech-canonical-coefficient-transfer)

Proof: Represent the chosen homology class by a cycle and identify its representative
with a morphism from the constant lifted integer sheaf by the sections adjunction.
Adjoint the augmentation-preserving chain map, apply inverse image to the cocycle,
and use exactFunctor_resolution_cocycle with the adjoint of the coefficient morphism ψ.
Exactness of inverse image and the augmentation equation identify the resulting Ext
class with inverse-image pullback followed by that coefficient map. Normalization
of the two canonical comparisons and associativity of Ext composition then give
the displayed equality. The terminal-section adjunction calculation is independent
of the target coefficient sheaf.
The argument is valid in every degree, including degree zero and the zero sheaf.
-/
theorem resolutionSection_canonical_coefficient_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (J : InjectiveResolution H)
    (ψ : G ⟶ (lowerStar AddCommGrpCat.{u + 1} g).obj H)
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      ψ ≫ (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison H J)
    (q : ℕ)
    (x : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology q) :
    cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      Sheaf.H.map (((upperStarLowerStarAdjunction _ g).homEquiv _ _).symm ψ) q
        (cohomologyMap g G q (cX.globalEquiv q x)) := by
  let SX := (etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)
  let SY := (etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)
  let K := SX.obj I.cocomplex
  let L := SY.obj J.cocomplex
  let t := globalResolutionSectionTransfer g I.cocomplex J.cocomplex α
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance x
  let eX := fun n ↦ ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ (I.cocomplex.X n)).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let f := (eX q).symm (K.iCycles q z)
  have hf : f ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (eX (q + 1)).injective
    change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (((constantSheafAdj _ _ _).homAddEquiv _ _) (f ≫ I.cocomplex.d q (q + 1))) = _
    simp only [Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    change (K.d q (q + 1)) (eX q f) = _
    rw [AddEquiv.apply_symm_apply]
    have hz := ConcreteCategory.congr_hom (K.iCycles_d q (q + 1)) z
    simpa only [ConcreteCategory.comp_apply, map_zero, AddCommGrpCat.zero_apply] using hz
  let F := upperStar AddCommGrpCat.{u + 1} g
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let β : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
    { f := fun n ↦ (adj.homEquiv _ _).symm (α.f n)
      comm' := fun i j hij ↦ by
        change (adj.homEquiv _ _).symm (α.f i) ≫ J.cocomplex.d i j =
          F.map (I.cocomplex.d i j) ≫ (adj.homEquiv _ _).symm (α.f j)
        apply (adj.homEquiv _ _).injective
        rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
          Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
        exact α.comm i j }
  let ψ' := (adj.homEquiv _ _).symm ψ
  have hβ : F.map (I.ι.f 0) ≫ β.f 0 = ψ' ≫ J.ι.f 0 := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_naturality_right]
    change I.ι.f 0 ≫ α.f 0 =
      (adj.homEquiv G H) ((adj.homEquiv G H).symm ψ) ≫ _
    rw [Equiv.apply_symm_apply]
    exact hα
  have hfβ : (F.map f ≫ β.f q) ≫ J.cocomplex.d q (q + 1) = 0 := by
    rw [Category.assoc, β.comm q (q + 1)]
    change F.map f ≫ F.map (I.cocomplex.d q (q + 1)) ≫ β.f (q + 1) = 0
    rw [← Category.assoc, ← F.map_comp, hf, F.map_zero, zero_comp]
  let c := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
    (AddCommGrpCat.of (ULift ℤ))).hom
  let f' := c ≫ F.map f ≫ β.f q
  have hf' : f' ≫ J.cocomplex.d q (q + 1) = 0 := by
    simp only [f', Category.assoc, hfβ, comp_zero]
  have hrep : L.iCycles q (HomologicalComplex.cyclesMap t q z) =
      (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @Etale Y)).homAddEquiv _
          (J.cocomplex.X q)).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)) f' := by
    have hz := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i t q) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hz
    rw [hz, section_adjunction_transfer g (I.cocomplex.X q) (J.cocomplex.X q) (β.f q) f]
    change (t.f q) (K.iCycles q z) =
      (J.cocomplex.X q).obj.map (terminalSectionPullback g).op
        (((adj.homEquiv _ _) ((adj.homEquiv _ _).symm (α.f q))).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) (eX q f))
    rw [Equiv.apply_symm_apply]
    change _ = (J.cocomplex.X q).obj.map (terminalSectionPullback g).op
      ((α.f q).hom.app (op (Scheme.Etale.mk (𝟙 X))) (eX q ((eX q).symm _)))
    rw [AddEquiv.apply_symm_apply]
    rfl
  have hhom := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality t q) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hhom
  rw [hhom, cY.global_cocycle q f' hf' _ hrep]
  rw [cX.global_cocycle q f hf z (by exact ((eX q).apply_symm_apply _).symm)]
  have hExt : ((I.extMk f (q + 1) rfl hf).mapExactFunctor F).comp
      (Abelian.Ext.mk₀ ψ') (add_zero q) =
      J.extMk (F.map f ≫ β.f q) (q + 1) rfl hfβ :=
    exactFunctor_resolution_cocycle F ψ' I J β hβ q f hf hfβ
  rw [cohomologyMap_apply, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, hExt]
  exact (J.mk₀_comp_extMk (F.map f ≫ β.f q) (q + 1) rfl hfβ c).symm

end AlgebraicGeometry.Etale
