/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProOpenAdjoints
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalProOpenEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import WeilConjectures.CategoryTheory.Exact.ExactDerivedAdjunctionBounds
import WeilConjectures.CategoryTheory.Scalar.ScalarAdjunctionDescent
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Construction of the pro-etale compact-support object -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
section ExactAdjunction
universe a av b bv d
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]

private theorem localizeOpenAdjunction
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory B ⥤ DerivedCategory A)
    (φ : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ψ : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    ∃ ad : FD ⊣ GD, ∀ P K (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (φ.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        ψ.inv.app K := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q FD := ⟨φ.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q GD := ⟨ψ.symm⟩
  let ad := (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) FD GD
  refine ⟨ad, ?_⟩
  intro P K f
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [show ad.unit.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ψ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫ GD.map (φ.inv.app P) from
        Adjunction.localization_unit_app _ _ _ _ _ _ _ P]
  simp only [Category.assoc, ← GD.map_comp, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  have hn := ψ.inv.naturality f
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ ψ.inv.app K =
    ψ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      GD.map (DerivedCategory.Q.map f) at hn
  rw [← hn, ← Category.assoc, ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_unit]

end ExactAdjunction

section GenericComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe ua va uu vv w d
variable {C : Type ua} [Category.{va} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type uu} [Category.{vv} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

private theorem compactSupportDerivedImage
    (S : CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj)
    (PY : CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell))
    (PX : CoefficientEvaluationDerivedPackage (J := K) (O := O) (ell := ell)) :
    Nonempty (CoefficientSystemDerivedImage O ell L V adj S PY PX) := by
  obtain ⟨T⟩ := coefficientSystemUnboundedComparison O ell L V adj S PY PX
  let image := T.evaluation
  let scalar := T.scalar
  have hlim : PreservesFiniteLimits S.inverse := S.systemExact.1
  have hcolim : PreservesFiniteColimits S.inverse := S.systemExact.2
  have hlevelLim (n : ℕ) : PreservesFiniteLimits (S.lift n).modules :=
    (S.inverseExact n).1
  have hlevelColim (n : ℕ) : PreservesFiniteColimits (S.lift n).modules :=
    (S.inverseExact n).2
  refine ⟨{
    construction := T
    detectsIso := coefficientEvaluation_detectsIso O ell PX
    boundedBelow := ?_
    origin := ?_ }⟩
  · rintro M ⟨a, ha⟩
    exact ⟨a, exactDerivedAdjunction_isGE S.inverse image.system.inverse
      image.system.inverseFactors image.system.adjunction M a⟩
  · intro hfull M hM horigin
    have hc (n : ℕ) :
        IsIso ((image.level n).adjunction.counit.app ((PX.evaluation n).obj M)) := by
      obtain ⟨H, hH, ⟨e⟩⟩ := horigin n
      exact exactDerivedAdjunction_counit_isIso_of_origin (S.lift n).modules
        (image.level n).inverse (image.level n).inverseFactors
        (image.level n).adjunction
        (hfull n) _ H hH e
    constructor
    · apply (coefficientEvaluation_detectsIso O ell PX _).2
      intro n
      rw [← image.counit n M]
      infer_instance
    · intro hnorm m n h
      have hreflect : (image.level n).inverse.ReflectsIsomorphisms :=
        exactDerived_reflectsIso_of_boundedBelow_faithful (S.lift n).modules
          (image.level n).inverse (image.level n).inverseFactors
          (fun A B hA hB ↦ (hfull n A B hA hB).1)
      have hnorm' := hnorm h
      exact isIso_scalar_transpose_of_mate (PY.scalar h).derivedAdj
        (PX.scalar h).derivedAdj (image.level m).adjunction (image.level n).adjunction
        (scalar.derivedTensor h) (scalar.restrictedDirect h) (scalar.restrictedDirect_mate h)
        ((image.directEvaluation m).app M) ((image.directEvaluation n).app M)
        ((PY.transition h).app (image.system.direct.obj M)) ((PX.transition h).app M)
        (scalar.directTransition h M)

end GenericComparison

namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

/-! The construction follows Zheng Construction 5.15: extension by zero on
strict pro-etale coefficient systems, followed by the universal derived image
of the proper factor.  The finite evaluation and localization equations are
constructed before passing to the derived category; the site equivalences are
used to transport the prescribed evaluation packages. -/
theorem exceptionalProCompactSupport_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ) :
    Nonempty (ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) := by
  have _ := hX
  have _ := hY
  have _ := hZ
  let : HasDerivedCategory.{u + 2}
      (CoefficientSystem (J := Scheme.ProEt.topology X) O ell) :=
    exceptionalProSystemDerived X O ell
  let : HasDerivedCategory.{u + 2}
      (CoefficientSystem (J := Scheme.ProEt.topology Y) O ell) :=
    exceptionalProSystemDerived Y O ell
  let : HasDerivedCategory.{u + 2}
      (CoefficientSystem (J := Scheme.ProEt.topology c.Z) O ell) :=
    exceptionalProSystemDerived c.Z O ell
  let : ∀ n : ℕ, HasDerivedCategory.{u + 2}
      (coefficientLevelModules (J := Scheme.ProEt.topology X) O ell n) :=
    fun n ↦ exceptionalProLevelDerived X O ell n
  let : ∀ n : ℕ, HasDerivedCategory.{u + 2}
      (coefficientLevelModules (J := Scheme.ProEt.topology Y) O ell n) :=
    fun n ↦ exceptionalProLevelDerived Y O ell n
  let : ∀ n : ℕ, HasDerivedCategory.{u + 2}
      (coefficientLevelModules (J := Scheme.ProEt.topology c.Z) O ell n) :=
    fun n ↦ exceptionalProLevelDerived c.Z O ell n
  let properLimits : PreservesFiniteLimits
      (Scheme.proEtaleSheafInverseImage c.g (Type (u + 1))) := by
    exact (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage c.g (𝟙 Y)).2.2.2.1
  let openLimits : PreservesFiniteLimits
      (Scheme.proEtaleSheafInverseImage c.i (Type (u + 1))) := by
    exact (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage c.i (𝟙 c.Z)).2.2.2.1
  obtain ⟨IY⟩ := coefficientSystemOrdinaryImage_exists O ell
    (Scheme.proEtaleSheafInverseImage c.g (Type (u + 1))) _
    (Scheme.proEtaleSheafAdjunction c.g (Type (u + 1)))
  obtain ⟨IX⟩ := coefficientSystemOrdinaryImage_exists O ell
    (Scheme.proEtaleSheafInverseImage c.i (Type (u + 1))) _
    (Scheme.proEtaleSheafAdjunction c.i (Type (u + 1)))
  obtain ⟨DY⟩ := compactSupportDerivedImage O ell _ _ _ IY CY.proEvaluation CZ.proEvaluation
  obtain ⟨DX⟩ := compactSupportDerivedImage O ell _ _ _ IX CZ.proEvaluation CX.proEvaluation
  obtain ⟨hs, hl⟩ := exceptionalProOpen_rightAdjoints O ell c.i IX
  let := hs
  let := hl
  let F := IX.inverse.leftAdjoint
  let ad₀ := Adjunction.ofIsRightAdjoint IX.inverse
  let Fn (n : ℕ) := (IX.lift n).modules.leftAdjoint
  let an (n : ℕ) := Adjunction.ofIsRightAdjoint (IX.lift n).modules
  obtain ⟨hexact, heval⟩ := exceptionalProOpen_evaluation O ell c.i IX
  let := heval
  let e (n : ℕ) :=
    (asIso ((mateEquiv ad₀ (an n)).symm (IX.inverseEvaluation n).hom)).symm
  have hmate (n : ℕ) : (IX.inverseEvaluation n).hom =
      (mateEquiv ad₀ (an n) (.mk _ _ _ _ (e n).inv)) := by
    exact (
      ((mateEquiv ad₀ (an n)).apply_symm_apply
        (.mk _ _ _ _ (IX.inverseEvaluation n).hom))).symm
  let : F.Additive := ad₀.left_adjoint_additive
  let (n : ℕ) : (Fn n).Additive := (an n).left_adjoint_additive
  let : ∀ n : ℕ, PreservesFiniteLimits
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n).1
  let : ∀ n : ℕ, PreservesFiniteColimits
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n).2
  let : ∀ n : ℕ, PreservesFiniteLimits
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n).1
  let : ∀ n : ℕ, PreservesFiniteColimits
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n) :=
    fun n ↦ (coefficientEvaluation_exact.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n).2
  have hf := (evaluations_jointlyReflect.{u + 1, u, u + 1}
    O ell (K := Scheme.ProEt.topology c.Z)).exactFunctor_of_iso
    (F := coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology X) (O := O) (ell := ell)) F Fn hexact e
  let : PreservesFiniteLimits F := hf.1
  let : PreservesFiniteColimits F := hf.2
  let (n : ℕ) : PreservesFiniteLimits (Fn n) := (hexact n).1
  let (n : ℕ) : PreservesFiniteColimits (Fn n) := (hexact n).2
  obtain ⟨ad, had⟩ := localizeOpenAdjunction F IX.inverse ad₀
    F.mapDerivedCategory DX.system.inverse F.mapDerivedCategoryFactors DX.system.inverseFactors
  have ha (n : ℕ) := localizeOpenAdjunction (Fn n) (IX.lift n).modules (an n)
    (Fn n).mapDerivedCategory (DX.level n).inverse
    (Fn n).mapDerivedCategoryFactors (DX.level n).inverseFactors
  choose al hal using ha
  have he (n : ℕ) := derivedSquare_exists F
    (coefficientEvaluation (J := Scheme.ProEt.topology X) (O := O) (ell := ell) n)
    (coefficientEvaluation (J := Scheme.ProEt.topology c.Z) (O := O) (ell := ell) n) (Fn n)
    F.mapDerivedCategory (CX.proEvaluation.evaluation n) (CZ.proEvaluation.evaluation n)
    (Fn n).mapDerivedCategory F.mapDerivedCategoryFactors
    (CX.proEvaluation.evaluationFactors n) (CZ.proEvaluation.evaluationFactors n)
    (Fn n).mapDerivedCategoryFactors (e n)
  choose ed hed using he
  let D : ExceptionalProCompactSupportData O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation := {
    openImage := IX
    properImage := IY
    properDerived := DY
    openExtension := F
    openAdjunction := ad₀
    levelOpen := Fn
    levelOpenAdjunction := an
    openEvaluation := e
    derivedOpen := F.mapDerivedCategory
    openDerived := DX
    derivedOpenAdjunction := ad
    openFactors := F.mapDerivedCategoryFactors
    levelDerivedOpen := fun n ↦ (Fn n).mapDerivedCategory
    levelDerivedOpenAdjunction := al
    levelOpenFactors := fun n ↦ (Fn n).mapDerivedCategoryFactors
    openDerivedEvaluation := ed }
  exact ⟨⟨D, hf, hmate, had, hal, hed⟩⟩

end AlgebraicGeometry
