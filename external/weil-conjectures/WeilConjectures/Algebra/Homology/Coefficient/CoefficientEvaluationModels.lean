/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
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
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
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
import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Abelian.Transfer
/-!
# Derived extension from a coefficient level
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Indices in this module are Zheng's nonnegative indices: `n` denotes the paper node's
positive level `n + 1`. No normalization or cartesianness is imposed on a system.
The auxiliary declarations construct the actual strict systems and their evaluations;
the final package records the constructions, universal properties and all coherence laws.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
/-- The constant quotient coefficient sheaf. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientQuotientSheaf (O : Type w) [CommRing O] (ell : O) (n : ℕ) :
    Sheaf J CommRingCat.{w} :=
  (constantSheaf J CommRingCat.{w}).obj
    (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1)))
/-- The quotient-induced map, with no arbitrary ring-sheaf map parameter.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientQuotientMap (O : Type w) [CommRing O] (ell : O)
    {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientSheaf (J := J) O ell m ⟶ coefficientQuotientSheaf (J := J) O ell n :=
  (constantSheaf J CommRingCat.{w}).map
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))))
/-- Modules at level `n+1`, using the recorded general ringed-site category.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientLevelModules (O : Type w) [CommRing O] (ell : O) (n : ℕ) :=
  ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      (coefficientQuotientSheaf (J := J) O ell n))
/-- Scalar restriction along the actual coefficient quotient.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03CZ
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientRestriction (O : Type w) [CommRing O] (ell : O)
    {m n : ℕ} (h : n ≤ m) :
    coefficientLevelModules (J := J) O ell n ⥤ coefficientLevelModules (J := J) O ell m :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
    (coefficientQuotientMap (J := J) O ell h))
/-- Strict semilinear systems; only successive transitions are data.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientSystem (O : Type w) [CommRing O] (ell : O) where
  level : ∀ n : ℕ, coefficientLevelModules (J := J) O ell n
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (coefficientRestriction (J := J) O ell (Nat.le_succ n)).obj (level n)
variable {O : Type w} [CommRing O] {ell : O}
/-- Componentwise morphisms commuting with all transitions.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientSystem.Hom (M N : CoefficientSystem (J := J) O ell) where
  app : ∀ n : ℕ, M.level n ⟶ N.level n
  comm : ∀ n : ℕ, app (n + 1) ≫ N.transition n =
    M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map (app n)
/-- Identity families commute with transitions. Source: Zheng, Construction 4.1, p. 21.
Proof: the two composites are the same transition, by the identity laws and functoriality
of scalar restriction (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_id_comm (M : CoefficientSystem (J := J) O ell) (n : ℕ) :
    𝟙 (M.level (n + 1)) ≫ M.transition n =
      M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map (𝟙 _) := by
  have := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  have := ‹HasSheafify J AddCommGrpCat.{w}›
  simp
/-- Composable compatible families remain compatible. Source: Zheng, Construction 4.1, p. 21.
Proof: substitute the two commuting squares, then use associativity and preservation
of composition by restriction (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_comp_comm {M N P : CoefficientSystem (J := J) O ell}
    (f : M.Hom N) (g : N.Hom P) (n : ℕ) :
    (f.app (n + 1) ≫ g.app (n + 1)) ≫ P.transition n =
      M.transition n ≫ (coefficientRestriction (J := J) O ell (Nat.le_succ n)).map
        (f.app n ≫ g.app n) := by
  have := ‹J.WEqualsLocallyBijective AddCommGrpCat.{w}›
  have := ‹HasSheafify J AddCommGrpCat.{w}›
  rw [Category.assoc, g.comm, ← Category.assoc, f.comm]
  simp only [Category.assoc, Functor.map_comp]
/-- Componentwise identity. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.identity (M : CoefficientSystem (J := J) O ell) : M.Hom M :=
  ⟨fun _n ↦ 𝟙 _, coefficientSystem_id_comm M⟩
/-- Componentwise composition. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.Hom.compose {M N P : CoefficientSystem (J := J) O ell}
    (f : M.Hom N) (g : N.Hom P) : M.Hom P :=
  ⟨fun n ↦ f.app n ≫ g.app n, coefficientSystem_comp_comm f g⟩
/-- Category laws for the displayed componentwise operations.
Source: Zheng, Construction 4.1, p. 21.
Proof: equality of these structures is equality of their components; identity and
associativity hold in each module category. Proof fields are irrelevant
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_category_laws :
    (∀ (M N : CoefficientSystem (J := J) O ell) (f : M.Hom N),
      M.identity.compose f = f ∧ f.compose N.identity = f) ∧
    (∀ (M N P Q : CoefficientSystem (J := J) O ell)
      (f : M.Hom N) (g : N.Hom P) (h : P.Hom Q),
      (f.compose g).compose h = f.compose (g.compose h)) := by
  have ext {M N : CoefficientSystem (J := J) O ell} (f g : M.Hom N)
      (h : f.app = g.app) : f = g := by
    cases f
    cases g
    cases h
    rfl
  constructor
  · intro M N f
    constructor
    · apply ext
      funext n
      exact Category.id_comp (f.app n)
    · apply ext
      funext n
      exact Category.comp_id (f.app n)
  · intro M N P Q f g h
    apply ext
    funext n
    exact Category.assoc (f.app n) (g.app n) (h.app n)
/-- The category with precisely the declared objects and componentwise maps.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
instance coefficientSystemCategory : Category (CoefficientSystem (J := J) O ell) where
  Hom := CoefficientSystem.Hom
  id := CoefficientSystem.identity
  comp := CoefficientSystem.Hom.compose
  id_comp := fun f ↦ (coefficientSystem_category_laws.1 _ _ f).1
  comp_id := fun f ↦ (coefficientSystem_category_laws.1 _ _ f).2
  assoc := fun f g h ↦ coefficientSystem_category_laws.2 _ _ _ _ f g h
/-- Exact level evaluation, on its actual object and morphism data.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientEvaluation (n : ℕ) :
    CoefficientSystem (J := J) O ell ⥤ coefficientLevelModules (J := J) O ell n where
  obj M := M.level n
  map f := f.app n

-- Iterate successor transitions over an arbitrary ring diagram before specializing to
-- constant quotient sheaves, so kernel checking does not unfold their sheafifications.
section CoefficientSystemBridge
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coefficientRingQuotients : ℕᵒᵖ ⥤ CommRingCat.{w} where
  obj n := CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n.unop + 1))
  map f := CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)))
  map_id n := by
    apply CommRingCat.hom_ext
    exact Ideal.Quotient.factor_eq
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact (Ideal.Quotient.factor_comp
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

private def coefficientRings : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w} where
  obj n := coefficientQuotientSheaf (J := J) O ell n.unop
  map f := coefficientQuotientMap (J := J) O ell (leOfHom f.unop)
  map_id n := (coefficientRingQuotients (O := O) (ell := ell) ⋙
    constantSheaf J CommRingCat.{w}).map_id n
  map_comp f g := (coefficientRingQuotients (O := O) (ell := ell) ⋙
    constantSheaf J CommRingCat.{w}).map_comp f g

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap

private abbrev ringSequenceUnderlying
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ) :=
  toSheaf.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op n)))

private def ringSequence
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n)) :
    ℕᵒᵖ ⥤ Sheaf J AddCommGrpCat.{w} :=
  Functor.ofOpSequence (X := fun n ↦ (ringSequenceUnderlying B n).obj (L n))
    (fun n ↦ (ringSequenceUnderlying B (n + 1)).map (t n))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] in
private theorem ringSequence_smul
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n))
    {n m : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (r : (B.obj (op m)).obj.obj U)
    (x : (L m).val.obj U) :
    ((ringSequence B L t).map (homOfLE h).op).hom.app U (r • x) =
      (B.map (homOfLE h).op).hom.app U r •
        (show (L n).val.obj U from ((ringSequence B L t).map (homOfLE h).op).hom.app U x) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) from rfl]
    rw [(ringSequence B L t).map_id, B.map_id]
    rfl
  | succ m h ih =>
    have he : (homOfLE (Nat.le.step h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    simp only [he, Functor.map_comp]
    change ((ringSequence B L t).map (homOfLE h).op).hom.app U
        (((ringSequence B L t).map (homOfLE (Nat.le_succ m)).op).hom.app U (r • x)) = _
    rw [show (ringSequence B L t).map (homOfLE (Nat.le_succ m)).op =
      (ringSequenceUnderlying B (m + 1)).map (t m) from
        Functor.ofOpSequence_map_homOfLE_succ _ m]
    change ((ringSequence B L t).map (homOfLE h).op).hom.app U
      ((t m).val.app U (r • x)) = _
    rw [(t m).val.app U |>.hom.map_smul]
    exact ih _ _

private def ringSequenceTransition
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n))
    {n m : ℕ} (h : n ≤ m) : L m ⟶ (systemRestriction B h).obj (L n) :=
  ⟨PresheafOfModules.homMk (((ringSequence B L t).map (homOfLE h).op).hom)
    (ringSequence_smul B L t h)⟩

private def ringSequenceSystem
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n)) :
    StrictRingSystem B where
  level := L
  transition h := ringSequenceTransition B L t h
  identity n U x := by
    change ((ringSequence B L t).map (homOfLE (Nat.le_refl n)).op).hom.app U x = x
    rw [show (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) from rfl]
    rw [(ringSequence B L t).map_id]
    rfl
  compose h k U x := by
    change ((ringSequence B L t).map (homOfLE (h.trans k)).op).hom.app U x = _
    rw [show (homOfLE (h.trans k)).op = (homOfLE k).op ≫ (homOfLE h).op from
      Subsingleton.elim _ _, Functor.map_comp]
    rfl

private abbrev coefficientIteratedTransition (M : CoefficientSystem (J := J) O ell)
    {n m : ℕ} (h : n ≤ m) :=
  ringSequenceTransition (coefficientRings (J := J) (O := O) (ell := ell))
    M.level M.transition h

private def coefficientToStrictObj (M : CoefficientSystem (J := J) O ell) :
    StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell)) :=
  ringSequenceSystem _ M.level M.transition

private theorem coefficient_hom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def ringSequenceMap
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L L' : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n))
    (t' : ∀ n, L' (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L' n))
    (f : ∀ n, L n ⟶ L' n)
    (hf : ∀ n, f (n + 1) ≫ t' n = t n ≫ (systemRestriction B (Nat.le_succ n)).map (f n)) :
    ringSequence B L t ⟶ ringSequence B L' t' :=
  NatTrans.ofOpSequence (fun n ↦ (ringSequenceUnderlying B n).map (f n))
    (by
      intro n
      simp only [ringSequence, Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg (ringSequenceUnderlying B (n + 1)).map (hf n)).symm)

private def ringSequenceSystemMap
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L L' : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n))
    (t' : ∀ n, L' (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L' n))
    (f : ∀ n, L n ⟶ L' n)
    (hf : ∀ n, f (n + 1) ≫ t' n = t n ≫ (systemRestriction B (Nat.le_succ n)).map (f n)) :
    ringSequenceSystem B L t ⟶ ringSequenceSystem B L' t' where
  app := f
  comm := by
    intro m n h
    ext U x
    exact congrArg (fun a ↦ a.hom.app U x)
      ((ringSequenceMap B L L' t t' f hf).naturality (homOfLE h).op).symm

private def coefficientToStrict : CoefficientSystem (J := J) O ell ⥤
    StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell)) where
  obj := coefficientToStrictObj
  map f := ringSequenceSystemMap _ _ _ _ _ f.app f.comm

private def coefficientFromStrict :
    StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell)) ⥤
      CoefficientSystem (J := J) O ell where
  obj M := ⟨M.level, fun n ↦ M.transition (Nat.le_succ n)⟩
  map f := ⟨f.app, fun n ↦ f.comm (Nat.le_succ n)⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] in
private theorem ringSequenceTransition_succ
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (L : ∀ n, systemLevel B n)
    (t : ∀ n, L (n + 1) ⟶ (systemRestriction B (Nat.le_succ n)).obj (L n)) (n : ℕ) :
    ringSequenceTransition B L t (Nat.le_succ n) = t n := by
  ext U x
  have h : (ringSequence B L t).map (homOfLE (Nat.le_succ n)).op =
      (ringSequenceUnderlying B (n + 1)).map (t n) :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  exact congrArg (fun a : (ringSequence B L t).obj (op (n + 1)) ⟶
      (ringSequence B L t).obj (op n) ↦ a.hom.app U x) h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem coefficientIterated_succ (M : CoefficientSystem (J := J) O ell) (n : ℕ) :
    coefficientIteratedTransition M (Nat.le_succ n) = M.transition n :=
  ringSequenceTransition_succ _ _ _ _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] in
private theorem ringSequenceTransition_strict
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (M : StrictRingSystem B)
    {n m : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : (M.level m).val.obj U) :
    (ringSequenceTransition B M.level (fun n ↦ M.transition (Nat.le_succ n)) h).val.app U x =
      (M.transition h).val.app U x := by
  induction m, h using Nat.le_induction with
  | base =>
    change ((ringSequence B M.level (fun n ↦ M.transition (Nat.le_succ n))).map
      (homOfLE (Nat.le_refl n)).op).hom.app U x = _
    rw [show (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) from rfl]
    rw [(ringSequence B M.level (fun n ↦ M.transition (Nat.le_succ n))).map_id]
    exact (M.identity n U x).symm
  | succ m h ih =>
    change ((ringSequence B M.level (fun n ↦ M.transition (Nat.le_succ n))).map
      (homOfLE (Nat.le.step h)).op).hom.app U x = _
    rw [show (homOfLE (Nat.le.step h)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op from Subsingleton.elim _ _,
      Functor.map_comp]
    change (ringSequenceTransition B M.level (fun n ↦ M.transition (Nat.le_succ n))
      h).val.app U ((ringSequenceTransition B M.level
        (fun n ↦ M.transition (Nat.le_succ n)) (Nat.le_succ m)).val.app U x) = _
    rw [ringSequenceTransition_succ, ih]
    exact (M.compose h (Nat.le_succ m) U x).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] in
private theorem ringSequenceTransition_strict_eq
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (M : StrictRingSystem B)
    {n m : ℕ} (h : n ≤ m) :
    ringSequenceTransition B M.level (fun n ↦ M.transition (Nat.le_succ n)) h =
      M.transition h := by
  ext U x
  exact ringSequenceTransition_strict B M h U x

private theorem coefficientStrictTransition_eq
    (M : StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell)))
    {n m : ℕ} (h : n ≤ m) :
    coefficientIteratedTransition (coefficientFromStrict.obj M) h = M.transition h :=
  ringSequenceTransition_strict_eq _ _ _

private theorem bridge_id_comm {A D : Type*} [Category A] [Category D]
    (R : A ⥤ D) {X : D} {Y : A} {f g : X ⟶ R.obj Y} (h : f = g) :
    𝟙 X ≫ f = g ≫ R.map (𝟙 Y) := by
  rw [Category.id_comp, R.map_id, Category.comp_id]
  exact h

private theorem coefficient_strict_hom_ext
    {M N : StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell))}
    (f g : M ⟶ N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

private def coefficientSystemEquivalence : CoefficientSystem (J := J) O ell ≌
    StrictRingSystem (coefficientRings (J := J) (O := O) (ell := ell)) where
  functor := coefficientToStrict
  inverse := coefficientFromStrict
  unitIso := NatIso.ofComponents (fun M ↦
    { hom := ⟨fun _ ↦ 𝟙 _, fun n ↦
        bridge_id_comm (coefficientRestriction (J := J) O ell (Nat.le_succ n))
          (coefficientIterated_succ M n)⟩
      inv := ⟨fun _ ↦ 𝟙 _, fun n ↦
        bridge_id_comm (coefficientRestriction (J := J) O ell (Nat.le_succ n))
          (coefficientIterated_succ M n).symm⟩
      hom_inv_id := coefficient_hom_ext _ _ (fun _ ↦ Category.id_comp _)
      inv_hom_id := coefficient_hom_ext _ _ (fun _ ↦ Category.id_comp _) })
    (by
      intro M N f
      apply coefficient_hom_ext
      intro n
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun M ↦
    { hom := ⟨fun _ ↦ 𝟙 _, fun h ↦
        bridge_id_comm (systemRestriction _ h) (coefficientStrictTransition_eq M h).symm⟩
      inv := ⟨fun _ ↦ 𝟙 _, fun h ↦
        bridge_id_comm (systemRestriction _ h) (coefficientStrictTransition_eq M h)⟩
      hom_inv_id := coefficient_strict_hom_ext _ _ (fun _ ↦ Category.id_comp _)
      inv_hom_id := coefficient_strict_hom_ext _ _ (fun _ ↦ Category.id_comp _) })
    (by
      intro M N f
      apply coefficient_strict_hom_ext
      intro n
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp M := by
    apply coefficient_strict_hom_ext
    intro n
    exact Category.id_comp _

end CoefficientSystemBridge

/-- The additive structure is normalized by the jointly faithful evaluations.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientSystem.AbelianNormalized
    (a : Abelian (CoefficientSystem (J := J) O ell)) : Prop :=
  @id Prop (by
    letI := a
    exact ∀ n : ℕ, (coefficientEvaluation (J := J) (O := O) (ell := ell) n).Additive)
/-- The unique componentwise abelian structure.
Source: Zheng, Construction 4.1, p. 21.
Proof: add morphisms componentwise; restriction is additive so compatibility is preserved.
Take kernels and sheafified cokernels at each level; their universal properties induce
successive transitions and the componentwise universal properties. Finite biproducts
are componentwise, and monos and epis are normal at each level. This gives an abelian
category. Joint faithfulness of evaluation fixes addition; all remaining abelian fields
are properties, so the normalized structure is unique
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientSystem_abelian_exists :
    ∃! a : Abelian (CoefficientSystem (J := J) O ell),
      CoefficientSystem.AbelianNormalized a := by
  let e := coefficientSystemEquivalence (J := J) (O := O) (ell := ell)
  let : Preadditive (CoefficientSystem (J := J) O ell) :=
    Preadditive.ofFullyFaithful e.fullyFaithfulFunctor
  have : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  have : HasFiniteProducts (CoefficientSystem (J := J) O ell) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let a : Abelian (CoefficientSystem (J := J) O ell) := abelianOfEquivalence e.functor
  refine ⟨a, ?_, ?_⟩
  · intro n
    change (e.functor ⋙ systemEvaluation _ n).Additive
    infer_instance
  · intro b _
    have hsub : Subsingleton (Preadditive (CoefficientSystem (J := J) O ell)) := by
      let := a
      infer_instance
    cases b
    cases a
    congr 1
    exact hsub.elim _ _
/-- The uniquely determined componentwise abelian structure, not an unspecified object.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
instance coefficientSystemAbelian : Abelian (CoefficientSystem (J := J) O ell) :=
  coefficientSystem_abelian_exists.exists.choose
/-- Evaluation is additive. Source: Zheng, Construction 4.1, p. 21.
Proof: apply the normalization in the unique abelian-structure theorem
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientEvaluation_additive (n : ℕ) :
    (coefficientEvaluation (J := J) (O := O) (ell := ell) n).Additive := by
  exact coefficientSystem_abelian_exists.exists.choose_spec n
attribute [instance] coefficientEvaluation_additive
/-- Evaluation is exact. Source: Zheng, Construction 4.1, p. 21.
Proof: kernels and cokernels in the constructed abelian category are componentwise;
finite biproducts and hence finite limits and colimits are componentwise as well
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem coefficientEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) ∧
      PreservesFiniteColimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) := by
  let e := coefficientSystemEquivalence (J := J) (O := O) (ell := ell)
  constructor
  · change PreservesFiniteLimits (e.functor ⋙ systemEvaluation _ n)
    infer_instance
  · change PreservesFiniteColimits (e.functor ⋙ systemEvaluation _ n)
    infer_instance
variable [EssentiallySmall.{w} C]
variable {R R' : Sheaf J CommRingCat.{w}}

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension respects identities. Source: Stacks Tag 03EK.
Proof: the sectionwise tensor map of the identity is the identity on every pure tensor;
sheafification preserves identity maps
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_map_id (φ : R ⟶ R')
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    changeOfRingsHom (φ) F (𝟙 F) =
      𝟙 (changeOfRings (φ) F) := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  unfold changeOfRingsHom changeOfRings
  convert (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R').obj)).map_id
      (changeOfRingsPresheaf φ F) using 1
  congr 1
  ext U x
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalars (φ.hom.app U).hom).map_id (F.val.obj U)) x

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension respects composition. Source: Stacks Tag 03EK.
Proof: on a tensor generator both composites apply the two module maps successively;
sheafify that equality (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_map_comp (φ : R ⟶ R')
    {F G H : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (f
      : F ⟶ G) (g : G ⟶ H) :
    changeOfRingsHom (φ) F (f ≫ g) =
      changeOfRingsHom (φ) F f ≫
        changeOfRingsHom (φ) G g := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  unfold changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  ext U x
  exact ConcreteCategory.congr_hom
    ((ModuleCat.extendScalars (φ.hom.app U).hom).map_comp (f.val.app U) (g.val.app U)) x

/-- The recorded sheafified sectionwise scalar extension, on objects and maps.
Source: Stacks Tag 03EK; Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteCoefficientTensor (φ : R ⟶ R') :
    SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R') where
  obj := changeOfRings (φ)
  map := changeOfRingsHom (φ) _
  map_id := siteCoefficientTensor_map_id φ
  map_comp := siteCoefficientTensor_map_comp φ

set_option backward.isDefEq.respectTransparency false in
/-- The tensor functor is additive. Source: Stacks Tag 03EK.
Proof: the tensor map is additive in the module-map variable before sheafification, and
module sheafification is additive
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensor_additive (φ : R ⟶ R') :
    (siteCoefficientTensor (J := J) φ).Additive := by
  have := ‹HasWeakSheafify J CommRingCat.{w}›
  have := ‹EssentiallySmall.{w} C›
  have hscalar (U : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  have hsheaf : (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R').obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
  constructor
  intro F G f g
  dsimp only [siteCoefficientTensor, changeOfRingsHom]
  rw [← CategoryTheory.Functor.map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  exact (ModuleCat.extendScalars (φ.hom.app U).hom).map_add (f := f.val.app U) (g := g.val.app U)

attribute [instance] siteCoefficientTensor_additive

/-- The canonical tensor Hom correspondence is evaluated on the sheafification image of
`1 tensor x`. Source: Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def SiteCoefficientTensorAdjunctionNormalized (φ : R ⟶ R')
    (a : siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) : Prop :=
  ∀ (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (G : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R'))
    (f : (siteCoefficientTensor (J := J) φ).obj F ⟶ G) (U : Cᵒᵖ) (x : F.val.obj
      U),
    ((a.homEquiv F G) f).val.app U x = f.val.app U
      ((toSheafify J
        (changeOfRingsPresheaf (φ) F).presheaf).app U
          (((ModuleCat.extendRestrictScalarsAdj
            ((φ).hom.app U).hom).unit.app
              (F.val.obj U)) x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor adjunction, uniquely fixed by its action on local tensor generators.
Source: Stacks Tag 03D7.
Proof: take the ordinary sectionwise tensor/restriction Hom bijections and then the module
sheafification Hom bijection. Their composite has exactly the displayed normalization.
They are natural in both variables and mutually inverse. Pure tensors generate, and
sheafification is universal, so this normalization determines the adjunction uniquely
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
theorem siteCoefficientTensorAdj_exists (φ : R ⟶ R') :
    ∃! a : siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ),
        SiteCoefficientTensorAdjunctionNormalized φ a := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R'))
  obtain ⟨_, _, h⟩ := sheafRingDerivedCoefficientAdjunction φ
  obtain ⟨a, ha, _⟩ := h (siteCoefficientTensor φ) (fun _ ↦ rfl) (by
    intro F G f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  have hn : SiteCoefficientTensorAdjunctionNormalized φ a := by
    intro F G f U x
    have hx := ha F G f U x
    simp only [eqToHom_refl, Category.id_comp] at hx
    convert hx using 1
    rfl
  refine ⟨a, hn, ?_⟩
  intro b hb
  apply Adjunction.ext
  ext F U x
  have he : b.homEquiv F ((siteCoefficientTensor φ).obj F) (𝟙 _) =
      a.homEquiv F ((siteCoefficientTensor φ).obj F) (𝟙 _) := by
    ext V y
    rw [hb, hn]
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at he
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) he) x

/-- The specified tensor/restriction adjunction, not a choice of an arbitrary map.
Source: Stacks Tag 03D7 (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteCoefficientTensorAdj (φ : R ⟶ R') :
    siteCoefficientTensor φ ⊣
      restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) :=
  (siteCoefficientTensorAdj_exists (J := J) φ).exists.choose

/-- Specialize the canonical site tensor functor to the actual coefficient quotient map.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03EK
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientTensor {m n : ℕ} (h : n ≤ m) :=
  siteCoefficientTensor (coefficientQuotientMap (J := J) O ell h)

/-- Specialize the normalized tensor adjunction to the coefficient quotient map.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev coefficientTensorAdj {m n : ℕ} (h : n ≤ m) :=
  siteCoefficientTensorAdj (coefficientQuotientMap (J := J) O ell h)

/-- Forgetting scalars after scalar restriction leaves the underlying additive sheaf
literally unchanged. This uses Mathlib's existing `toSheaf` and `restrictScalars`.
Source: Stacks Tag 03CZ (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteScalarUnderlyingIso (φ : R ⟶ R') :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) ⋙
      SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ≅
    SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R') :=
  Iso.refl _

/-- The underlying additive-sheaf map of the canonical scalar-extension unit.
Source: Stacks Tag 03D7 (blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def siteTensorUnitUnderlying (φ : R ⟶ R')
    (F : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    (SheafOfModules.toSheaf _).obj F ⟶
      (SheafOfModules.toSheaf _).obj ((siteCoefficientTensor φ).obj F) :=
  (SheafOfModules.toSheaf _).map ((siteCoefficientTensorAdj φ).unit.app F) ≫
    (siteScalarUnderlyingIso φ).hom.app ((siteCoefficientTensor φ).obj F)

/-- A strict transition on the underlying additive sheaves, without coefficient-action
casts. Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def coefficientTransitionUnderlying {m n : ℕ} (h : n ≤ m)
    (t : coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
      coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
        coefficientRestriction (J := J) O ell h)
    (M : CoefficientSystem (J := J) O ell) :
    (SheafOfModules.toSheaf _).obj (M.level m) ⟶
      (SheafOfModules.toSheaf _).obj (M.level n) :=
  (SheafOfModules.toSheaf _).map (t.app M) ≫
    (siteScalarUnderlyingIso (coefficientQuotientMap (J := J) O ell h)).hom.app (M.level n)

/-- Iterated transitions are fixed by the actual successor maps, identity and composition.
The forgetful functors are faithful, so these are equations of the actual transitions.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTransitionsNormalized
    (t : ∀ {m n : ℕ} (h : n ≤ m),
      coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
        coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
          coefficientRestriction (J := J) O ell h) : Prop :=
  (∀ n M, coefficientTransitionUnderlying (Nat.le_refl n) (t (Nat.le_refl n)) M = 𝟙 _) ∧
  (∀ n (M : CoefficientSystem (J := J) O ell),
    (t (Nat.le_succ n)).app M = M.transition n) ∧
  (∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
    coefficientTransitionUnderlying (h₂.trans h₁) (t (h₂.trans h₁)) M =
      coefficientTransitionUnderlying h₁ (t h₁) M ≫ coefficientTransitionUnderlying h₂ (t h₂) M)

/-- The tensor unit is the inverse of the canonical scalar-extension unit, on underlying
additive sheaves (faithful forgetting). Source: Stacks Tag 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTensorUnitNormalized
    (tensorUnit : ∀ n, coefficientTensor (J := J) (O := O) (ell := ell) (Nat.le_refl n) ≅
      𝟭 (coefficientLevelModules (J := J) O ell n)) : Prop :=
  ∀ n F,
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell (Nat.le_refl n)) F ≫
      (SheafOfModules.toSheaf _).map ((tensorUnit n).hom.app F) = 𝟙 _

/-- The balanced associator is fixed on the generating scalar-extension units.
The scalar-unit formula above identifies this equation with the tensor-generator formula.
Source: Stacks Tags 03EK and 03D7
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
def CoefficientTensorAssocNormalized
    (tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
      coefficientTensor (J := J) (O := O) (ell := ell) h₁ ⋙
        coefficientTensor (J := J) (O := O) (ell := ell) h₂ ≅
          coefficientTensor (J := J) (O := O) (ell := ell) (h₂.trans h₁)) : Prop :=
  ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) F,
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell h₁) F ≫
      siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell h₂)
        ((coefficientTensor (J := J) (O := O) (ell := ell) h₁).obj F) ≫
      (SheafOfModules.toSheaf _).map ((tensorAssoc h₁ h₂).hom.app F) =
    siteTensorUnitUnderlying (coefficientQuotientMap (J := J) O ell (h₂.trans h₁)) F

section GeneralInterfaces

universe a b c a' b' c'

variable {A : Type a} {B : Type b} [Category.{a'} A] [Category.{b'} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]

/-- Universal scalar extension and its normalized derived adjunction for fixed functors.
The specialization below fixes these functors to the actual coefficient tensor and
restriction, and fixes K-flatness to the recorded sheaf tensor predicate.
Source: Stacks Tags 06YY and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure DerivedCoefficientScalarExtension (T : A ⥤ B) (R : B ⥤ A)
    [T.Additive] [R.Additive] (adj : T ⊣ R) (KFlat : CochainComplex A ℤ → Prop) where
  derived : DerivedCategory A ⥤ DerivedCategory B
  counit : DerivedCategory.Q ⋙ derived ⟶
    T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  isDerived : derived.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  computes : ∀ P, KFlat P → IsIso (counit.app P)
  restriction : DerivedCategory B ⥤ DerivedCategory A
  restrictionFactors : DerivedCategory.Q ⋙ restriction ≅
    R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  derivedAdj : derived ⊣ restriction
  transpose : ∀ P K (f : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ K),
    derivedAdj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (counit.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          P K f) ≫ restrictionFactors.inv.app K

variable {S : Type c} [Category.{c'} S] [Abelian S] [HasDerivedCategory.{d} S]
  {M : ℕ → Type a} [∀ n, Category.{a'} (M n)] [∀ n, Abelian (M n)]
  [∀ n, HasDerivedCategory.{d} (M n)]
  (e : ∀ n, S ⥤ M n) [∀ n, (e n).Additive]
  (r : ∀ {m n : ℕ}, n ≤ m → M n ⥤ M m) [∀ m n (h : n ≤ m), (r h).Additive]
  (T : ∀ {m n : ℕ}, n ≤ m → M m ⥤ M n) [∀ m n (h : n ≤ m), (T h).Additive]
  (aTensor : ∀ {m n : ℕ} (h : n ≤ m), T h ⊣ r h)
  (KFlat : ∀ n, CochainComplex (M n) ℤ → Prop) (Flat : ∀ n, M n → Prop)
  (TransitionsNormalized : (∀ {m n : ℕ} (h : n ≤ m), e m ⟶ e n ⋙ r h) → Prop)
  (TensorUnitNormalized : (∀ n, T (Nat.le_refl n) ≅ 𝟭 (M n)) → Prop)
  (TensorAssocNormalized :
    (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m), T h₁ ⋙ T h₂ ≅ T (h₂.trans h₁)) → Prop)

/-- The complete extension, strict representative, index coherence and mate equations.
The parameters are specialized to concrete coefficient systems in
`CoefficientEvaluationDerivedPackage`; they are not hypotheses of the final theorem.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
structure CoefficientEvaluationExtensionData where
  strictTransition : ∀ {m n : ℕ} (h : n ≤ m),
    e m ⟶
      e n ⋙
        r h
  transitionsNormalized : TransitionsNormalized strictTransition
  scalar : ∀ {m n : ℕ} (h : n ≤ m), DerivedCoefficientScalarExtension (T h) (r h) (aTensor h)
    (KFlat m)
  extension : ∀ n, M n ⥤ S
  [extensionAdditive : ∀ n, (extension n).Additive]
  adj : ∀ n, extension n ⊣ e n
  below : ∀ {n q} (h : q ≤ n), extension n
    ⋙ e q ≅ (T h)
  above : ∀ n q, n < q → ∀ F, IsZero ((e q).obj ((extension n).obj F))
  hom_formula : ∀ {n q} (h : q ≤ n) F M (f : (extension n).obj F ⟶ M),
    ((aTensor h).homEquiv F ((e q).obj M)) ((below
      h).inv.app F ≫ (e q).map f) =
      ((adj n).homEquiv F M f) ≫ (strictTransition h).app M
  evaluation : ∀ n, DerivedCategory (S) ⥤
    DerivedCategory (M n)
  evaluationFactors : ∀ n, DerivedCategory.Q ⋙ evaluation n ≅
    (e n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  derivedExtension : ∀ n, DerivedCategory (M n) ⥤
    DerivedCategory (S)
  counit : ∀ n, DerivedCategory.Q ⋙ derivedExtension n ⟶
    (extension n).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  isDerived : ∀ n, (derivedExtension n).IsLeftDerivedFunctor (counit n)
    (HomologicalComplex.quasiIso (M n)
      (ComplexShape.up ℤ))
  computes : ∀ n P,
    KFlat n P →
    (∀ i, Flat n (P.X i)) →
      IsIso ((counit n).app P)
  derivedAdj : ∀ n, derivedExtension n ⊣ evaluation n
  transpose : ∀ n P K
      (f : ((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ K),
    (derivedAdj n).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      ((counit n).app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map (((adj n).mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv
          P K f) ≫ (evaluationFactors n).inv.app K
  derivedBelow : ∀ {n q} (h : q ≤ n),
    derivedExtension n ⋙ evaluation q ≅ (scalar h).derived
  derivedAbove : ∀ n q, n < q → ∀ N, IsZero ((evaluation q).obj ((derivedExtension n).obj N))
  transition : ∀ {m n} (h : n ≤ m),
    evaluation m ⟶ evaluation n ⋙ (scalar h).restriction
  transition_rep : ∀ {m n} (h : n ≤ m) K,
    (transition h).app (DerivedCategory.Q.obj K) ≫
      (scalar h).restriction.map ((evaluationFactors n).hom.app K) ≫
      (scalar h).restrictionFactors.hom.app
        (((e n).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (evaluationFactors m).hom.app K ≫
        DerivedCategory.Q.map
          (((strictTransition h).mapHomologicalComplex (ComplexShape.up ℤ)).app K)
  sigma : ∀ {m n} (h : n ≤ m),
    (scalar h).derived ⋙ derivedExtension n ⟶ derivedExtension m
  mate : ∀ {m n} (h : n ≤ m) N M (f : (derivedExtension m).obj N ⟶ M),
    (derivedAdj n).homEquiv ((scalar h).derived.obj N) M ((sigma h).app N ≫ f) =
      (scalar h).derived.map ((derivedAdj m).homEquiv N M f) ≫
        ((scalar h).derivedAdj.homEquiv ((evaluation m).obj M) ((evaluation n).obj M)).symm
          ((transition h).app M)
  tensorUnit : ∀ n, (T (Nat.le_refl n)) ≅ 𝟭 _
  tensorUnit_normalized : TensorUnitNormalized tensorUnit
  tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (T h₁) ⋙ (T h₂) ≅ (T (h₂.trans h₁))
  tensorAssoc_normalized : TensorAssocNormalized tensorAssoc
  strictSigma : ∀ {m n} (h : n ≤ m),
    (T h) ⋙ extension n ⟶ extension m
  strictSigma_below : ∀ {m n q} (h : n ≤ m) (hq : q ≤ n) F,
    (below hq).inv.app ((T h).obj F) ≫
      (e q).map ((strictSigma h).app F) ≫ (below (hq.trans h)).hom.app F =
        (tensorAssoc h hq).hom.app F
  strictSigma_above : ∀ {m n q} (h : n ≤ m) (_hq : n < q) F,
    (e q).map ((strictSigma h).app F) = 0
  strictSigmaComplex : ∀ {m n} (h : n ≤ m) P,
    ((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((T h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    ((extension m).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  strictSigmaComplex_f : ∀ {m n} (h : n ≤ m) P i,
    (strictSigmaComplex h P).f i = (strictSigma h).app (P.X i)
  sigma_rep : ∀ {m n} (h : n ≤ m) P,
    KFlat m P →
    (∀ i, Flat m (P.X i)) →
    (sigma h).app (DerivedCategory.Q.obj P) ≫ (counit m).app P =
      (derivedExtension n).map ((scalar h).counit.app P) ≫
        (counit n).app (((T h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strictSigmaComplex h P)
  tensorUnitComplex : ∀ n P,
    ((T (Nat.le_refl n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ≅ P
  tensorUnitComplex_f : ∀ n P i,
    ((tensorUnitComplex n P).hom).f i = (tensorUnit n).hom.app (P.X i)
  tensorAssocComplex : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    ((T h₂).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj
      (((T h₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
    ((T (h₂.trans h₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
  tensorAssocComplex_f : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P i,
    ((tensorAssocComplex h₁ h₂ P).hom).f i = (tensorAssoc h₁ h₂).hom.app (P.X i)
  derivedUnit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _
  derivedUnit_rep : ∀ n P,
    KFlat n P →
    (derivedUnit n).hom.app (DerivedCategory.Q.obj P) =
      (scalar (Nat.le_refl n)).counit.app P ≫
        DerivedCategory.Q.map (tensorUnitComplex n P).hom
  derivedAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (scalar h₁).derived ⋙ (scalar h₂).derived ≅ (scalar (h₂.trans h₁)).derived
  derivedAssoc_rep : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    KFlat l P →
    (∀ i, Flat l (P.X i)) →
    (derivedAssoc h₁ h₂).hom.app (DerivedCategory.Q.obj P) ≫
      (scalar (h₂.trans h₁)).counit.app P =
    (scalar h₂).derived.map ((scalar h₁).counit.app P) ≫
      (scalar h₂).counit.app
        (((T h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (tensorAssocComplex h₁ h₂ P).hom
  sigma_id : ∀ n N, (sigma (Nat.le_refl n)).app N =
    (derivedExtension n).map ((derivedUnit n).hom.app N)
  sigma_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) N,
    (sigma h₂).app ((scalar h₁).derived.obj N) ≫ (sigma h₁).app N =
      (derivedExtension n).map ((derivedAssoc h₁ h₂).hom.app N) ≫
        (sigma (h₂.trans h₁)).app N
  belowComplex : ∀ {n q} (h : q ≤ n) P,
    ((e q).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
    ((T h).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj P
  belowComplex_f : ∀ {n q} (h : q ≤ n) P i,
    ((belowComplex h P).hom).f i = (below h).hom.app (P.X i)
  derivedBelow_rep : ∀ {n q} (h : q ≤ n) P,
    (derivedBelow h).inv.app (DerivedCategory.Q.obj P) ≫
      (evaluation q).map ((counit n).app P) ≫
      (evaluationFactors q).hom.app
        (((extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (belowComplex h P).hom = (scalar h).counit.app P
end GeneralInterfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficientScalarPresentation
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (D : DerivedChangeOfRingsCochainModel φ) : D.E = siteCoefficientTensor φ := by
  refine CategoryTheory.Functor.ext D.obj_eq ?_
  intro M N f
  exact D.map_eq f

private theorem coefficientScalarAdj_homEquiv
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (D : SystemScalarModel φ)
    (F : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R))
    (G : ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J S))
    (f : (siteCoefficientTensor φ).obj F ⟶ G) :
    D.ordinaryAdj.homEquiv F G
      ((eqToIso (coefficientScalarPresentation φ D.model)).hom.app F ≫ f) =
        (siteCoefficientTensorAdj φ).homEquiv F G f := by
  ext U x
  have hn : SiteCoefficientTensorAdjunctionNormalized φ (siteCoefficientTensorAdj φ) :=
    (siteCoefficientTensorAdj_exists φ).exists.choose_spec
  rw [hn]
  simp only [Adjunction.homEquiv_unit]
  change f.val.app U
    (((eqToIso (coefficientScalarPresentation φ D.model)).hom.app F).val.app U
      ((D.ordinaryAdj.unit.app F).val.app U x)) = _
  rw [D.unit_normalized]
  dsimp only [systemModelTmul]
  simp only [one_smul]
  congr 1
  change ((eqToIso (coefficientScalarPresentation φ D.model)).hom.app F).val.app U
    ((eqToHom (D.model.obj_eq F).symm).val.app U _) = _
  have he : (eqToIso (coefficientScalarPresentation φ D.model)).hom.app F =
      eqToHom (D.model.obj_eq F) := by
    simp only [eqToIso.hom, eqToHom_app]
  rw [he]
  change ((eqToHom (D.model.obj_eq F).symm ≫
    eqToHom (D.model.obj_eq F)).val.app U) _ = _
  simp only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]

private def coefficientStrictTransition {m n : ℕ} (h : n ≤ m) :
    coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
      coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
        coefficientRestriction (J := J) O ell h where
  app M := coefficientIteratedTransition M h
  naturality M N f := by
    have hh := (coefficientToStrict.map f).comm h
    exact hh

omit [EssentiallySmall.{w} C] in
private theorem coefficientStrictTransition_normalized :
    CoefficientTransitionsNormalized
      (J := J) (O := O) (ell := ell) (fun {_ _} h ↦ coefficientStrictTransition h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n M
    ext U x
    exact (coefficientToStrict.obj M).identity n U x
  · intro n M
    exact coefficientIterated_succ M n
  · intro l m n h₁ h₂ M
    ext U x
    exact (coefficientToStrict.obj M).compose h₂ h₁ U x

private theorem coefficientOrdinaryExtension (n : ℕ) :
    ∃ (E : coefficientLevelModules (J := J) O ell n ⥤
        CoefficientSystem (J := J) O ell) (adj : E ⊣ coefficientEvaluation n)
      (below : ∀ {q : ℕ} (h : q ≤ n), E ⋙ coefficientEvaluation q ≅ coefficientTensor h),
      (∀ q : ℕ, n < q → ∀ F, IsZero ((coefficientEvaluation q).obj (E.obj F))) ∧
      (∀ {q : ℕ} (h : q ≤ n) F M (f : E.obj F ⟶ M),
        (coefficientTensorAdj h).homEquiv F (M.level q)
          ((below h).inv.app F ≫ (coefficientEvaluation q).map f) =
            adj.homEquiv F M f ≫ (coefficientStrictTransition h).app M) := by
  classical
  let t := (systemLevelLeftExtensionTheory (J := J)).some
  let B := coefficientRings (J := J) (O := O) (ell := ell)
  let e := coefficientSystemEquivalence (J := J) (O := O) (ell := ell)
  let E := (t.single B n).ordinary ⋙ e.inverse
  let adj : E ⊣ coefficientEvaluation n := (t.single B n).ordinaryAdj.comp
    e.symm.toAdjunction
  have hi {q : ℕ} (h : q ≤ n) :
      systemTensor t.scalar B h = coefficientTensor (J := J) (O := O) (ell := ell) h :=
    coefficientScalarPresentation _ _
  let below : ∀ {q : ℕ} (h : q ≤ n), E ⋙ coefficientEvaluation q ≅ coefficientTensor h :=
    fun h ↦ (t.singleBelow B h) ≪≫ eqToIso (hi h)
  refine ⟨E, adj, below, ?_, ?_⟩
  · intro q hq F
    exact t.singleAbove B q n hq F
  · intro q h F M f
    have hf := t.singleTranspose B h F (e.functor.obj M)
      (e.symm.toAdjunction.homEquiv _ _ f)
    rw [← coefficientScalarAdj_homEquiv
      (coefficientQuotientMap (J := J) O ell h) (t.scalar _) F (M.level q)]
    have hev : (systemEvaluation B q).map
        (e.symm.toAdjunction.homEquiv _ _ f) = f.app q := by
      rw [Adjunction.homEquiv_unit]
      change 𝟙 _ ≫ f.app q = f.app q
      exact Category.id_comp _
    rw [hev] at hf
    have hb : (eqToIso (coefficientScalarPresentation
        (coefficientQuotientMap (J := J) O ell h) (t.scalar _).model)).hom.app F ≫
        (below h).inv.app F = (t.singleBelow B h).inv.app F := by
      dsimp only [below]
      simp only [Iso.trans_inv, NatTrans.comp_app,
        Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, hb]
    change _ = (adj.homEquiv F M f) ≫ (e.functor.obj M).transition h
    dsimp only [adj]
    rw [Adjunction.comp_homEquiv]
    exact hf

/-- The strict part of extension from a coefficient level. The transitions are the
actual iterates, and the Hom formula fixes the below-level comparisons by adjunction.
Source: Zheng, Construction 4.1, printed p. 21, the formula for `e_n!` and its adjunction
(blueprint: lem-pur-coefficient-evaluation-strict-extension). -/
structure CoefficientOrdinaryEvaluationData where
  strictTransition : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientEvaluation (J := J) (O := O) (ell := ell) m ⟶
      coefficientEvaluation (J := J) (O := O) (ell := ell) n ⋙
        coefficientRestriction (J := J) O ell h
  transitionsNormalized : CoefficientTransitionsNormalized strictTransition
  extension : ∀ n : ℕ, coefficientLevelModules (J := J) O ell n ⥤
    CoefficientSystem (J := J) O ell
  [extensionAdditive : ∀ n : ℕ, (extension n).Additive]
  adj : ∀ n : ℕ, extension n ⊣ coefficientEvaluation n
  below : ∀ {n q : ℕ} (h : q ≤ n), extension n ⋙ coefficientEvaluation q ≅
    coefficientTensor h
  above : ∀ n q : ℕ, n < q → ∀ F, IsZero ((coefficientEvaluation q).obj ((extension n).obj F))
  hom_formula : ∀ {n q : ℕ} (h : q ≤ n) F M (f : (extension n).obj F ⟶ M),
    (coefficientTensorAdj h).homEquiv F (M.level q)
      ((below h).inv.app F ≫ (coefficientEvaluation q).map f) =
        (adj n).homEquiv F M f ≫ (strictTransition h).app M

/-- Strict extension from a single coefficient level exists with its specified tensor
components and ordinary adjunction.
Source: Zheng, Construction 4.1, printed p. 21
(blueprint: lem-pur-coefficient-evaluation-strict-extension).
Proof: iterate the successor transitions by the functor on the opposite sequence.
The equivalence with all-transition systems preserves each level and all component maps.
Use the general strict-system extension, and transport it through this equivalence.
Its scalar functor equals the prescribed sheafified change of rings on objects and maps.
Both scalar Hom correspondences send a morphism to its value on the sheafification image
of `1 tensor x`, so they agree. Transfer the general extension's below-level isomorphisms,
zero components, and Hom formula across these equalities. The equivalence's unit has
identity components, so no correction appears in that formula. Finally additivity follows
from the ordinary adjunction between preadditive categories. The iteration functor fixes
identity, successor, and composite transitions exactly as required. -/
theorem coefficientOrdinaryEvaluationExtension :
    Nonempty (CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell)) := by
  classical
  choose E a b ha hb using coefficientOrdinaryExtension (J := J) (O := O) (ell := ell)
  exact ⟨{
    strictTransition := fun h ↦ coefficientStrictTransition h
    transitionsNormalized := coefficientStrictTransition_normalized
    extension := E
    extensionAdditive := fun n ↦ (a n).left_adjoint_additive
    adj := a
    below := fun h ↦ b _ h
    above := ha
    hom_formula := fun h F M f ↦ hb _ h F M f }⟩

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

/-- Specialize every ambient object and functor in the coherence interface to the
actual constant quotient rings, strict systems, scalar functors and recorded flatness
predicates. There are no arbitrary category, tensor or transition inputs.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint). -/
abbrev CoefficientEvaluationDerivedPackage :=
  CoefficientEvaluationExtensionData
    (coefficientEvaluation (J := J) (O := O) (ell := ell))
    (fun {_ _} h ↦ coefficientRestriction (J := J) O ell h)
    (fun {_ _} h ↦ coefficientTensor (J := J) (O := O) (ell := ell) h)
    (fun {_ _} h ↦ coefficientTensorAdj (J := J) (O := O) (ell := ell) h)
    (fun n ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell n))
    (fun n ↦ IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell n))
    (CoefficientTransitionsNormalized (J := J) (O := O) (ell := ell))
    (CoefficientTensorUnitNormalized (J := J) (O := O) (ell := ell))
    (CoefficientTensorAssocNormalized (J := J) (O := O) (ell := ell))

end SheafOfModules
