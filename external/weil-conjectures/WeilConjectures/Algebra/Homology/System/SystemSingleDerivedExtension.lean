/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.SmoothPurity.NormalizedLeftExtension
public import WeilConjectures.Algebra.Homology.System.SystemOrdinarySingleExtension
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemEvaluationKFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Derived extension from one coefficient level

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)

/-- Flat-term K-flat complexes resolve every level complex.
Source: Stacks 06YS (blueprint: lem-pur-system-single-derived-extension).
Proof: use the coefficient-universe K-flat resolution and convert its tensor-exact
terms to the site-flat predicate using the tensor identification. -/
theorem systemLevel_kFlatResolution (K : CochainComplex (systemLevel B n) ℤ) :
    ∃ (L : CochainComplex (systemLevel B n) ℤ) (f : L ⟶ K),
      systemLevelKFlat B n L ∧ QuasiIso f := by
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B.obj (op n)) K
  exact ⟨P, q, ⟨hP, fun i ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso (B.obj (op n)) (P.X i)).symm (hflat i)⟩, hq⟩

/-- The singleton extension preserves quasi-isomorphisms between its resolving objects.
Source: Zheng 4.1; Stacks 06YT
(blueprint: lem-pur-system-single-derived-extension).
Proof: below n its evaluated complex is ordinary scalar extension, which preserves
quasi-isomorphisms between K-flat objects. Above n both evaluated complexes vanish.
Joint detection by exact evaluations then gives the strict quasi-isomorphism. -/
theorem systemSingle_preserves {K L : CochainComplex (systemLevel B n) ℤ} (f : K ⟶ L)
    (hK : systemLevelKFlat B n K) (hL : systemLevelKFlat B n L) (hf : QuasiIso f) :
    QuasiIso (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (strictRingSystem_quasiIso_iff B _).2
  intro m
  let F := systemSingleFunctor S T B n
  let V := systemEvaluation B m
  let i := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ V)) (.up ℤ)
  by_cases hm : m ≤ n
  · have hp := (S (B.map (homOfLE hm).op)).model.preserves f hK.1 hL.1 hf
    let j := NatIso.mapHomologicalComplex (systemSingleBelow S T B n hm) (.up ℤ)
    let e := i.symm ≪≫ j
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)).2 hp
  · have hzero (P : CochainComplex (systemLevel B n) ℤ) :
        IsZero ((V.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.hom_ext
      intro k
      exact (systemSingleLevelAbove S B n (P.X k) (Nat.lt_of_not_ge hm)).eq_of_src _ _
    have : IsIso (((V.mapHomologicalComplex (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f))) :=
      (hzero K).isIso (hzero L) _
    infer_instance

/-- The determined normalized derivation of the fixed ordinary singleton adjunction.
Keeping the selected derivation named prevents repeated reduction of its resolving-class
construction when comparing fields. Source: Zheng 4.1; Stacks 06XN and 0FND
(blueprint: lem-pur-system-single-derived-extension). -/
@[irreducible]
def systemSingleDerivation (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemLeftExtensionDerivation (systemEvaluation B n) (systemSingleFunctor S T B n)
      (systemSingleAdjunction S T B n) (systemLevelKFlat B n) :=
  Classical.choice <|
    nonempty_normalizedLeftExtension (systemEvaluation B n) (systemSingleFunctor S T B n)
      (systemSingleAdjunction S T B n) (systemLevelKFlat B n)
      (systemLevel_kFlatResolution B n) (fun f ↦ systemSingle_preserves S T B n f)

/-- The ordinary singleton adjunction has its everywhere-defined normalized derived
adjunction. Source: Zheng 4.1; Stacks 06XN and 0FND
(blueprint: lem-pur-system-single-derived-extension).
Proof: apply normalized derivation to the flat-term K-flat resolving class, using
the preceding resolution and invariance lemmas. -/
def systemSingleDerivedExtension (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    SystemDerivedLeftExtension (systemEvaluation B n) (systemLevelKFlat B n) :=
  (systemSingleDerivation B n S T).toExtension

end SheafOfModules
