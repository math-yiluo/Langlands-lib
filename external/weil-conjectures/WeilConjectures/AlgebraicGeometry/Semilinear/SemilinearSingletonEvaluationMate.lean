/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import all WeilConjectures.AlgebraicGeometry.ProjectionTensorCore.SemilinearTensorReductionCore
import WeilConjectures.Algebra.Homology.System.SystemScalarDerivedExtension
import WeilConjectures.Algebra.Homology.SmoothPurity.NormalizedLeftExtension
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The singleton evaluation mate below its source vertex

## References

* Zheng Construction 4.1
* Stacks 06YT, 0FND
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section MateTransfer
universe a a' b b' d d'
variable {X : Type a} [Category.{a'} X] {Y : Type b} [Category.{b'} Y]
  {Z : Type d} [Category.{d'} Z]
private theorem mate_isIso_transfer
    {E : X ⥤ Y} {F : X ⥤ Z} {R : Z ⥤ Y}
    {L₀ L : Y ⥤ X} {S₀ S : Y ⥤ Z}
    (a₀ : L₀ ⊣ E) (a : L ⊣ E) (b₀ : S₀ ⊣ R) (b : S ⊣ R)
    (τ : E ⟶ F ⋙ R) (P : Y)
    (hk : IsIso ((b₀.homEquiv _ _).symm
      (a₀.unit.app P ≫ τ.app (L₀.obj P)))) :
    IsIso ((b.homEquiv _ _).symm (a.unit.app P ≫ τ.app (L.obj P))) := by
  let i := a₀.leftAdjointUniq a
  let j := b.leftAdjointUniq b₀
  let k := (b₀.homEquiv _ _).symm (a₀.unit.app P ≫ τ.app (L₀.obj P))
  have : IsIso k := hk
  have he : (b.homEquiv _ _).symm (a.unit.app P ≫ τ.app (L.obj P)) =
      j.hom.app P ≫ k ≫ F.map (i.hom.app P) := by
    apply (b.homEquiv _ _).injective
    dsimp only [j]
    rw [Equiv.apply_symm_apply, b.homEquiv_naturality_right]
    have hj := b.homEquiv_leftAdjointUniq_hom_app b₀ P
    change b.homEquiv ((𝟭 Y).obj P) _ ((b.leftAdjointUniq b₀).hom.app P) = _ at hj
    rw [hj]
    change _ = b₀.homEquiv _ _ (k ≫ F.map (i.hom.app P))
    rw [b₀.homEquiv_naturality_right]
    simp only [k, Equiv.apply_symm_apply]
    rw [Category.assoc]
    change _ = a₀.unit.app P ≫ τ.app (L₀.obj P) ≫ (F ⋙ R).map (i.hom.app P)
    rw [← τ.naturality, ← Category.assoc]
    exact congrArg (fun u ↦ u ≫ τ.app (L.obj P))
      (a₀.unit_leftAdjointUniq_hom_app a P).symm
  rw [he]
  infer_instance
private theorem mate_transpose_identity
    {E : X ⥤ Y} {F : X ⥤ Z} {R : Z ⥤ Y} {L : Y ⥤ X} {S : Y ⥤ Z}
    (a : L ⊣ E) (b : S ⊣ R) (τ : E ⟶ F ⋙ R) (P : Y) :
    ((mateEquiv a b).symm (TwoSquare.mk E F (𝟭 Y) R τ)).app P =
      (b.homEquiv _ _).symm (a.unit.app P ≫ τ.app (L.obj P)) := by
  apply (b.homEquiv P (F.obj (L.obj P))).injective
  change (b.homEquiv P (F.obj (L.obj P)))
      (((mateEquiv a b).symm (TwoSquare.mk E F (𝟭 Y) R τ)).app P) =
    (b.homEquiv P (F.obj (L.obj P)))
      ((b.homEquiv P (F.obj (L.obj P))).symm (a.unit.app P ≫ τ.app (L.obj P)))
  rw [Equiv.apply_symm_apply]
  have he := adjunctionMate_transpose a b (TwoSquare.mk E F (𝟭 Y) R τ)
    P (L.obj P) (𝟙 _)
  change (b.homEquiv P (F.obj (L.obj P)))
      (((mateEquiv a b).symm (TwoSquare.mk E F (𝟭 Y) R τ)).app P ≫
        F.map (𝟙 (L.obj P))) =
    (𝟭 Y).map (a.homEquiv P (L.obj P) (𝟙 _)) ≫ τ.app (L.obj P) at he
  erw [F.map_id, Category.comp_id, Adjunction.homEquiv_id, Functor.id_map] at he
  exact he

private theorem transfer_from_mate
    {E : X ⥤ Y} {F : X ⥤ Z} {R : Z ⥤ Y}
    {L₀ L : Y ⥤ X} {S₀ S : Y ⥤ Z}
    (a₀ : L₀ ⊣ E) (a : L ⊣ E) (b₀ : S₀ ⊣ R) (b : S ⊣ R)
    (τ : E ⟶ F ⋙ R) (P : Y)
    (hk : IsIso (((mateEquiv a₀ b₀).symm
      (TwoSquare.mk E F (𝟭 Y) R τ)).app P)) :
    IsIso ((b.homEquiv _ _).symm (a.unit.app P ≫ τ.app (L.obj P))) := by
  have hk₀ : IsIso ((b₀.homEquiv _ _).symm
      (a₀.unit.app P ≫ τ.app (L₀.obj P))) := by
    rw [← mate_transpose_identity a₀ b₀ τ P]
    exact hk
  exact mate_isIso_transfer a₀ a b₀ b τ P hk₀

private theorem transpose_unit
    {E : X ⥤ Y} {F : X ⥤ Z} {R : Z ⥤ Y} {L : Y ⥤ X} {S : Y ⥤ Z}
    (a : L ⊣ E) (b : S ⊣ R) (τ : E ⟶ F ⋙ R) (P : Y) :
    (b.homEquiv P (F.obj (L.obj P))).symm (a.unit.app P ≫ τ.app (L.obj P)) =
      S.map (a.unit.app P) ≫
        (b.homEquiv (E.obj (L.obj P)) (F.obj (L.obj P))).symm (τ.app (L.obj P)) := by
  apply (b.homEquiv P (F.obj (L.obj P))).injective
  rw [Equiv.apply_symm_apply, b.homEquiv_naturality_left]
  change _ = a.unit.app P ≫
    (b.homEquiv (E.obj (L.obj P)) (F.obj (L.obj P)))
      ((b.homEquiv (E.obj (L.obj P)) (F.obj (L.obj P))).symm (τ.app (L.obj P)))
  rw [Equiv.apply_symm_apply]

end MateTransfer

section CochainFactor
universe a₁ a₂ a₃ b₁ b₂ b₃
variable {X : Type a₁} [Category.{b₁} X] [Abelian X]
  {Y : Type a₂} [Category.{b₂} Y] [Abelian Y]
  {Z : Type a₃} [Category.{b₃} Z] [Abelian Z]
private theorem cochain_comp_factor (F : X ⥤ Y) (G : X ⥤ Z) (R : Z ⥤ Y)
    [F.Additive] [G.Additive] [R.Additive]
    (δ : F ⟶ G ⋙ R) (K : CochainComplex X ℤ) :
    (NatTrans.mapHomologicalComplex δ (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex δ (.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ R)) (.up ℤ)).inv.app K := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f]
  change δ.app (K.X i) = δ.app (K.X i) ≫ 𝟙 _
  rw [Category.comp_id]
end CochainFactor

namespace WeilConjectures.SemilinearSections
attribute [local irreducible] HasDerivedCategory.standard
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- Below a singleton vertex, the mate of the actual transition is invertible.
This assertion involves no tensor product or projection map. -/
theorem semilinearSingletonEvaluationMate_isIso
    (n q : ℕ) (h : q ≤ n)
    (A : ScalarData.{c, v, max c v r}
      (coefficientMap.{c, v, max c v r} J B τ h))
    (L : D.{c, v, max c v r} J (B n) ⥤ DS.{c, v, max c v r} J B τ)
    (adj : L ⊣ e.{c, v, max c v r} J B τ n)
    (P : D.{c, v, max c v r} J (B n)) :
    IsIso (A.T.map (adj.unit.app P) ≫
      reduction.{c, v, max c v r} J B τ h A (L.obj P)) := by
  classical
  let R := rings.{c, v, max c v r} J B τ
  let E := SheafOfModules.strictSystemSequenceEquivalence R
  have : E.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : E.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let S : SheafOfModules.SystemScalarAssignment.{c, v, max c v r} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let F : Mod.{c, v, max c v r} J (B n) ⥤
      SheafOfModules.StrictRingSystem.{c, v, max c v r} (J := J) R :=
    SheafOfModules.systemSingleFunctor S T R n
  have : F.Additive := SheafOfModules.systemSingleFunctorAdditive S T R n
  have (m : ℕ) : (evaluation.{c, v, max c v r} J B τ m).Additive :=
    evaluationAdditive.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteLimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationLimits.{c, v, max c v r} J B τ m
  have (m : ℕ) : PreservesFiniteColimits (evaluation.{c, v, max c v r} J B τ m) :=
    evaluationColimits.{c, v, max c v r} J B τ m
  let β (m : ℕ) : E.inverse ⋙ SheafOfModules.systemEvaluation R m ≅
      evaluation.{c, v, max c v r} J B τ m :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (evaluation_ring.{c, v, max c v r} J B τ m).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let a : (F ⋙ E.functor) ⊣ evaluation.{c, v, max c v r} J B τ n :=
    Adjunction.ofNatIsoRight
    ((SheafOfModules.systemSingleAdjunction S T R n).comp E.toAdjunction) (β n)
  obtain ⟨d⟩ := SheafOfModules.nonempty_normalizedLeftExtension
    (evaluation.{c, v, max c v r} J B τ n) (F ⋙ E.functor) a
    (SheafOfModules.systemLevelKFlat R n)
    (SheafOfModules.systemLevel_kFlatResolution R n) (by
      intro K K' f hK hK' hf
      have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) :=
        SheafOfModules.systemSingle_preserves S T R n f hK hK' hf
      change QuasiIso ((E.functor.mapHomologicalComplex (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f))
      infer_instance)
  let bq : E.functor ⋙ evaluation.{c, v, max c v r} J B τ q ≅
      SheafOfModules.systemEvaluation R q :=
    Functor.isoWhiskerLeft E.functor (β q).symm ≪≫
      (Functor.associator E.functor E.inverse (SheafOfModules.systemEvaluation R q)).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm (SheafOfModules.systemEvaluation R q) ≪≫
      Functor.leftUnitor (SheafOfModules.systemEvaluation R q)
  let ι : (𝟭 (Mod.{c, v, max c v r} J (B n))) ⋙
      (S (coefficientMap.{c, v, max c v r} J B τ h)).model.E ≅
      (F ⋙ E.functor) ⋙ evaluation.{c, v, max c v r} J B τ q :=
    Functor.leftUnitor _ ≪≫ (SheafOfModules.systemSingleBelow S T R n h).symm ≪≫
      Functor.isoWhiskerLeft F bq.symm ≪≫
      (Functor.associator F E.functor (evaluation.{c, v, max c v r} J B τ q)).symm
  have hi (P : Mod.{c, v, max c v r} J (B n)) :
      (S (coefficientMap J B τ h)).ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
        a.unit.app P ≫ (transition.{c, v, max c v r} J B τ h).app ((F ⋙ E.functor).obj P) := by
    rw [Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    have ht := eq_of_heq
      ((transition_exists.{c, v, max c v r} J B τ h).exists.choose_spec
        ((F ⋙ E.functor).obj P) U)
    change _ = ((transition.{c, v, max c v r} J B τ h).app
      ((F ⋙ E.functor).obj P)).val.app U ((a.unit.app P).val.app U x)
    have ht' := congrFun ht ((a.unit.app P).val.app U x)
    apply Eq.trans ?_ ht'.symm
    have hu := congrArg (fun f ↦ f.val.app U x)
      (SheafOfModules.systemSingleOrdinaryUnitSquare S T R h P)
    change ((SheafOfModules.systemSingleBelow S T R n h).inv.app P).val.app U
        (((S (coefficientMap J B τ h)).ordinaryAdj.unit.app P).val.app U x) =
      ((F.obj P).level q).val.map (𝟙 U)
        (((F.obj P).transition h).val.app U
          (((SheafOfModules.systemSingleAdjunction S T R n).unit.app P).val.app U x))
    rw [PresheafOfModules.map_id]
    exact hu
  let d₁ := d.toExtension
  let d₂ := SheafOfModules.systemScalarModelExtension.{c, v, max c v r} (S (coefficientMap J B τ h))
  let G := 𝟭 (Mod.{c, v, max c v r} J (B n))
  let GD := 𝟭 (D.{c, v, max c v r} J (B n))
  let g : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Iso.refl _
  let tD : e.{c, v, max c v r} J B τ n ⋙ GD ⟶
      e.{c, v, max c v r} J B τ q ⋙ resD (coefficientMap J B τ h) :=
    derivedTransition.{c, v, max c v r} J B τ h
  let t : evaluation.{c, v, max c v r} J B τ n ⋙ G ⟶
      evaluation.{c, v, max c v r} J B τ q ⋙ res (coefficientMap J B τ h) :=
    transition.{c, v, max c v r} J B τ h
  have ht (K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
      tD.app (DerivedCategory.Q.obj K) ≫
          (res.{c, v, max c v r} (coefficientMap J B τ h)).mapDerivedCategory.map
            ((evaluation.{c, v, max c v r} J B τ q).mapDerivedCategoryFactors.hom.app K) ≫
          (res.{c, v, max c v r} (coefficientMap J B τ h)).mapDerivedCategoryFactors.hom.app
            (((evaluation.{c, v, max c v r} J B τ q).mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map ((evaluation.{c, v, max c v r} J B τ n).mapDerivedCategoryFactors.hom.app K) ≫
          g.hom.app (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((t.mapHomologicalComplex (.up ℤ)).app K) := by
    have hu := cochain_comp_factor
      (evaluation.{c, v, max c v r} J B τ n) (evaluation.{c, v, max c v r} J B τ q)
      (res (coefficientMap J B τ h)) (transition J B τ h) K
    dsimp only [tD, GD, G, g, Functor.id_map, Iso.refl_hom, NatTrans.id_app]
    erw [Category.id_comp, hu]
    simpa only [derivedTransition, NatTrans.comp_app, Category.assoc] using
      localized_transition_fac
      (evaluation.{c, v, max c v r} J B τ n) (evaluation.{c, v, max c v r} J B τ q)
      (res (coefficientMap J B τ h)) (transition J B τ h) K
  have hm := SheafOfModules.derivedExtensionMate_isIso d₁ d₂ G
    (evaluation.{c, v, max c v r} J B τ q) GD g tD t ht ι hi
    (SheafOfModules.systemLevel_kFlatResolution R n) (fun _ hp ↦ hp.1)
  let k₀ := SheafOfModules.derivedExtensionMate d₁ d₂
    (evaluation.{c, v, max c v r} J B τ q) GD tD
  have : IsIso (k₀.app P) := by
    have : IsIso k₀ := hm
    infer_instance
  have hk := transfer_from_mate d₁.adjunction adj d₂.adjunction A.adjunction
    (derivedTransition J B τ h) P (show IsIso (k₀.app P) from inferInstance)
  change IsIso ((A.adjunction.homEquiv P
    ((e.{c, v, max c v r} J B τ q).obj (L.obj P))).symm
      (adj.unit.app P ≫ (derivedTransition J B τ h).app (L.obj P))) at hk
  rw [transpose_unit adj A.adjunction (derivedTransition J B τ h) P] at hk
  exact hk

end WeilConjectures.SemilinearSections
