/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive

import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicSliceScalarComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteModelDerivedScalarComparison

/-! # The coefficient-change square for a finite-quotient constant model

Source: Stacks Project, Tags 06YY, 07A6 and 094I.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData

private abbrev residueModules (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) :=
  SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

private def residueChange (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    DerivedCategory (residueModules X R) ⥤ DerivedCategory (residueModules X S) :=
  completedAdicDerivedChange X f

private instance residueRestriction_limits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteLimits (completedRestriction X f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose

private instance residueRestriction_colimits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteColimits (completedRestriction X f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose_spec.choose

private theorem residueChange_adjunction (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty (residueChange X f ⊣ (completedRestriction X f).mapDerivedCategory) := by
  let D := completedAdicChangeData X f
  let E : residueModules X R ⥤ residueModules X S := D.choose
  let hE : ∀ M, E.obj M = SheafOfModules.changeOfRings f M := D.choose_spec.choose
  let hm : ∀ {M N : residueModules X R} (a : M ⟶ N),
      E.map a = eqToHom (hE M) ≫ SheafOfModules.changeOfRingsHom f M a ≫
        eqToHom (hE N).symm := fun a ↦ D.choose_spec.choose_spec.choose a
  let : E.Additive := D.choose_spec.choose_spec.choose_spec.choose
  let L : DerivedCategory (residueModules X R) ⥤ DerivedCategory (residueModules X S) :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
  let ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
  have hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
  have h := (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose_spec.choose_spec
  have ha := (h E hE hm).choose_spec.2 L ε hL
  exact ⟨ha.choose⟩

private def residueChange_comp (X : Scheme.{t})
    {R S V : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (f : R ⟶ S) (g : S ⟶ V) :
    residueChange X f ⋙ residueChange X g ≅ residueChange X (f ≫ g) := by
  let a := (residueChange_adjunction X f).some
  let b := (residueChange_adjunction X g).some
  let c := (residueChange_adjunction X (f ≫ g)).some
  let e : (completedRestriction X g).mapDerivedCategory ⋙
      (completedRestriction X f).mapDerivedCategory ≅
      (completedRestriction X (f ≫ g)).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (completedRestrictCompIso X f g).symm
  exact ((a.comp b).ofNatIsoRight e).leftAdjointUniq c

private theorem residueCoefficient_square (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    adicConstantMap X (adicQuotientMap d.ideal (n + 1) (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le n))) ≫ φ 0 =
      φ n ≫ completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
  let p := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let q := adicQuotientMap d.ideal (n + 1) (0 + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have hp : Function.Surjective (RingHom.ulift p) := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  let : Epi (CommRingCat.ofHom (RingHom.ulift p)) :=
    ConcreteCategory.epi_of_surjective _ hp
  let : (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).IsLeftAdjoint :=
    (constantSheafAdj (ProEt.topology X) CommRingCat.{t + 1}
      terminalIsTerminal).isLeftAdjoint
  have : Epi (adicConstantMap X p) := by
    unfold adicConstantMap
    infer_instance
  have hq : q.comp p = Ideal.Quotient.mk (d.ideal ^ (0 + 1)) := by
    ext x
    rfl
  apply (cancel_epi (adicConstantMap X p)).1
  calc
    adicConstantMap X p ≫ adicConstantMap X q ≫ φ 0 =
        adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (0 + 1))) ≫ φ 0 := by
      rw [← Category.assoc, adicConstantMap_comp, hq]
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d 0 := (hc.2 0).symm
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [completedAdicCommProjection_comp]
    _ = adicConstantMap X p ≫ φ n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [← Category.assoc, hc.2 n, Category.assoc]

private def residueRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

-- The existing signature retains hφ, although the comparison does not need it.
set_option linter.unusedVariables false in
/-- Reduction of a given constant quotient model is the constant realization of its
algebraic derived residue, after the specified residue-ring identification. This is
only a coefficient-change comparison: there is no local projective-model hypothesis
and no boundedness or Tor-amplitude conclusion. It also holds on an empty chart.

Source: Stacks Project, Tags 06YY and 07A6, and sites-cohomology.tex,
Tag 094I, part (2), the derived residue computation.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-comparison).

Proof: obtain composition of the actual derived scalar-extension functors from
their existing adjunctions to exact restriction of scalars and uniqueness of left
adjoints. The limit-projection equation identifies nth reduction followed by residue
extension with zeroth reduction. Scalar compatibility identifies the finite coefficient
square after precomposition with the constant quotient map from A. That map is an
epimorphism, because its lifted ring map is surjective and constant sheafification is
a left adjoint; cancellation gives the square itself. The separate constant-model
comparison identifies algebraic derived residue, ring-equivalence transport and the
canonical representative with constant coefficient extension. The separate slice
comparison permits applying derived residue extension to the given local isomorphism.
Compose these isomorphisms, using the exact derived restriction's comparison with the
representative-based restriction in the statement. No boundedness, finiteness of P,
projectivity, invertibility of phi, or geometric-stalk argument is used. -/
theorem finiteQuotient_model_residueComparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (n : ℕ) (W : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P)))))
    (L : DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{t}
        ((A ⧸ d.ideal ^ (n + 1)) ⧸ d.ideal.map
          (Ideal.Quotient.mk (d.ideal ^ (n + 1))))))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars
          (Ideal.Quotient.mk (d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1))))))
        (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (ρ : ((A ⧸ d.ideal ^ (n + 1)) ⧸ d.ideal.map
      (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) ≃+* (A ⧸ d.ideal ^ (0 + 1)))
    (hρ : ρ.toRingHom.comp
        (Ideal.Quotient.mk (d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1))))) =
      adicQuotientMap d.ideal (n + 1) (0 + 1) (Nat.succ_le_succ (Nat.zero_le n))) :
    let C := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d 0).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ C)))) := by
  clear hφ
  let U := (toProEt X).obj W
  let Rn := completedAdicFiniteRing X d n
  let R₀ := completedAdicFiniteRing X d 0
  let q := completedAdicQuotientCommMap X d n 0 (Nat.zero_le n)
  let q₀ := adicQuotientMap d.ideal (n + 1) (0 + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  let B := A ⧸ d.ideal ^ (n + 1)
  let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let F := completedAdicSliceDerivedChange X U q
  let r₀ := ringedDerivedRestrictionGeneral R₀ U
  let en := (residueRestrictionComparison X Rn U _ ≪≫ e.some ≪≫
    (residueRestrictionComparison X Rn U _).symm)
  let s := (completedAdic_slice_scalarComparison X U q).some
  let mn := completedAdicCommProjection X d n
  let m₀ := completedAdicCommProjection X d 0
  have hm : mn ≫ q = m₀ := completedAdicCommProjection_comp X d n 0 (Nat.zero_le n)
  let em : (completedAdicQuotientReduction X d n ⋙
      completedAdicDerivedChange X q) ≅ completedAdicQuotientReduction X d 0 :=
    residueChange_comp X mn q ≪≫ eqToIso (congrArg (completedAdicDerivedChange X) hm)
  have hs : φ n ≫ q = adicConstantMap X q₀ ≫ φ 0 :=
    (residueCoefficient_square X d φ hcompat n).symm
  let ec : completedAdicDerivedChange X (φ n) ⋙ completedAdicDerivedChange X q ≅
      completedAdicDerivedChange X (adicConstantMap X q₀) ⋙
        completedAdicDerivedChange X (φ 0) :=
    residueChange_comp X (φ n) q ≪≫
      eqToIso (congrArg (completedAdicDerivedChange X) hs) ≪≫
      (residueChange_comp X (adicConstantMap X q₀) (φ 0)).symm
  obtain ⟨ea⟩ := finiteModel_derivedScalarComparison X (Ideal.Quotient.mk J) ρ P L ε hL
  have he : ρ.toRingHom.comp (Ideal.Quotient.mk J) = q₀ := hρ
  rw [he] at ea
  exact ⟨(residueRestrictionComparison X R₀ U _).symm ≪≫
    r₀.mapIso (em.app M).symm ≪≫ (s.app _).symm ≪≫ F.mapIso en ≪≫ s.app _ ≪≫
    r₀.mapIso (ec.app (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≪≫
    r₀.mapIso ((completedAdicDerivedChange X (φ 0)).mapIso ea) ≪≫
    residueRestrictionComparison X R₀ U _⟩

end AlgebraicGeometry.Scheme
