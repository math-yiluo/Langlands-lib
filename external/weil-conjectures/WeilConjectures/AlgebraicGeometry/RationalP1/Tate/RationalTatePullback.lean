/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedExchangeExactNormalization

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.Algebra.CharP.Invertible
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement

/-! # The normalized rational Tate pullback comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The given rational coefficient, with the finite-subextension convention for the closure. -/
def coefficient (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l)) :
    Profinite.CondensedRing.{u} :=
  match c with
  | some E => Mon.mk (Profinite.continuousMapRingObj E.1)
  | none => Mon.mk (Profinite.padicAlgClRingObj l)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The chosen coefficient ring is commutative. -/
theorem coefficient_isCommMonObj (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) :
    IsCommMonObj (coefficient.{u} l c).X := by
  cases c <;> dsimp only [coefficient] <;> infer_instance

/-- Commutativity of the actual selected coefficient ring. -/
instance coefficient_comm (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) :
    IsCommMonObj (coefficient.{u} l c).X := coefficient_isCommMonObj l c

/-- The existing positive Tate module. -/
def line (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (X : Scheme.{u}) : Modules (coefficient l c).X X :=
  match c with
  | some E => spRationalTwist X l E
  | none => spQbarTwist X l

-- Keep fixed site and derived comparisons folded during elaboration.
/-- Select the preceding coefficient diagram, retaining its fixed class and traces. -/
def diagram (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u}) (family : Family l Y) :
    Diagram (coefficient l c).X Y (line l c) :=
  match c with
  | some E => family.rational E
  | none => family.closure

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The unique linear lift of the prescribed abelian adjunct. -/
theorem linePull_existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (τ : (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).obj LS.X ⟶ LX.X)
    (_h : SpInternalCartesian f Λ LS LX τ) :
    ∃! e : (CondensedRing.upperStar Λ f).obj LS ≅ LX,
      HEq (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LS LX) e.hom).hom
        (((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv LS.X LX.X) τ) := by
  classical
  obtain ⟨_, β, hβ⟩ := _h
  let ES := InternalModuleOperations.equivalence Λ S
  let EX := InternalModuleOperations.equivalence Λ X
  let lc := InternalModuleOperations.lowerComparison Λ f ≪≫ pushBridge f Λ
  obtain ⟨j, _, _, hj, _, _⟩ := exists_equivalenceAdjunctionComparison ES EX
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (Scheme.proEtaleRingModuleAdjunction f _ _ (spCoefficientIso f Λ)) lc
  let c := (β.signed 1)
  let g : (CondensedRing.upperStar Λ f).obj LS ⟶ LX :=
    EX.functor.preimage (j.hom.app LS ≫ c.hom)
  have hg : EX.functor.map g = j.hom.app LS ≫ c.hom :=
    EX.functor.map_preimage _
  have : IsIso (EX.functor.map g) := by
    rw [hg]
    infer_instance
  have : IsIso g := isIso_of_fully_faithful EX.functor g
  have he : j.inv.app LS ≫ EX.functor.map g = c.hom := by
    rw [hg, ← Category.assoc, j.inv_hom_id_app]
    exact Category.id_comp _
  have hn : ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LS LX g).hom =
      ((Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv LS.X LX.X) τ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    have hh := congrArg (fun k ↦ k.val.app V m) (hj LS LX g)
    rw [he] at hh
    change _ = ((lc.hom.app LX).val.app V)
      ((((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LS LX g).hom.hom.app V) m)
      at hh
    simp only [lc, Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, lowerComparison_apply] at hh
    rw [pushBridge_apply] at hh
    exact hh.symm.trans (hβ V m)
  refine ⟨asIso g, heq_of_eq hn, ?_⟩
  intro e he'
  apply Iso.ext
  apply ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv LS LX).injective
  apply Mod.hom_ext
  exact (eq_of_heq he').trans hn.symm

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The determined linear lift; its data are fixed by the displayed adjunct equation. -/
def linePullIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (τ : (Scheme.proEtaleSheafInverseImage f Ab.{u + 1}).obj LS.X ⟶ LX.X)
    (h : SpInternalCartesian f Λ LS LX τ) : (CondensedRing.upperStar Λ f).obj LS ≅ LX :=
  (linePull_existsUnique Λ f LS LX τ h).exists.choose

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The existing normalized adic comparison. Its root, scalar and coprojection
normalizations determine the maps used here. -/
def adicComparison (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] : CartesianAdicComparison l f :=
  Classical.choice (((cartesianCoefficients l f).2.1 inferInstance inferInstance).2.2)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The linear rational or closure comparison with its prescribed abelian adjunct. -/
def lineComparison (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (CondensedRing.upperStar (coefficient l c).X f).obj (line l c S) ≅ line l c X :=
  match c with
  | some E => linePullIso _ f _ _ ((adicComparison l f).rational E)
      ((adicComparison l f).integral_rational_cartesian E).2
  | none => linePullIso _ f _ _ (adicComparison l f).qbar
      (adicComparison l f).qbar_cartesian

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The canonical shifted derived comparison, with no new line isomorphism. -/
def shiftedLineComparison (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (moduleObjectDerivedPullback (coefficient l c).X f).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X S) 0).obj
        (line l c S)) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X X) 0).obj
        (line l c X)) ⟦(2 : ℤ)⟧ :=
  ((moduleObjectDerivedPullback (coefficient l c).X f).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((CondensedRing.upperStar (coefficient l c).X f).singleFunctorCompLeftDerivedFunctorIso.app
        _) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (lineComparison l c f))

end AlgebraicGeometry.ProEtale.RationalP1

namespace AlgebraicGeometry.ProEtale.RationalP1
open CategoryTheory CategoryTheory.Limits DiagonalCoefficients
open scoped CategoryTheory.Obj

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The coefficient prime remains a unit in every residue field over the given field. -/
theorem residueIsUnit (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) (x : X) :
    IsUnit (l : X.residueField x) := by
  have hl : IsUnit (l : k) := (CharP.isUnit_natCast_iff (Fact.out : p.Prime)).2
    (fun h ↦ _hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime)
      (Fact.out : l.Prime)).1 h))
  simpa only [map_natCast] using hl.map (a.residueFieldAlgebraMap x)

-- Keep fixed site and derived comparisons folded during elaboration.
/-- The specified shifted Tate comparison for the second projective projection. -/
def secondLineComparison (l : ℕ) [Fact l.Prime]
    (c : Option (PadicAlgCl.FiniteIntermediateField l)) (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (CondensedRing.moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧ :=
  letI : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  letI : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  shiftedLineComparison l c (secondProjection Y)

end AlgebraicGeometry.ProEtale.RationalP1
