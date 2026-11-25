/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorShriek
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorConstructibility
import WeilConjectures.AlgebraicGeometry.SixFunctors.DualizableIntegralCompletion

/-!
# The ordinary integral derived tensor product

All tensors use the ambient K-flat derived monoidal structure over the pulled-back
continuous condensed valuation ring. Constructibility uses finite constant scalar models.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem localModel_dualizable
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (M : DerivedCategory (AdicCompletion.Modules l E S))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (hC : ∀ i : C.I₀,
      ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
        (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X n)) ∧
        Nonempty
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (C.f i)).mapDerivedCategory.obj M ≅
            DerivedCategory.Q.obj
              (((DerivedNakayama.pullback l E (C.X i)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))) : IsDualizable M := by
  classical
  apply (condensed_dualizable_iff_proetale_cover
    ⟨DerivedNakayama.integerRing l E⟩ S C M).2
  intro i
  obtain ⟨P, ⟨a, b, hb⟩, hf, ⟨e⟩⟩ := hC i
  let F := DerivedNakayama.pullback l E (C.X i)
  let T := (F.mapHomologicalComplex (.up ℤ)).obj P
  have : CochainComplex.IsStrictlyGE T a := (CochainComplex.isStrictlyGE_iff T a).2
    (fun n hn ↦ F.map_isZero (hb n (.inl hn)))
  have : CochainComplex.IsStrictlyLE T b := (CochainComplex.isStrictlyLE_iff T b).2
    (fun n hn ↦ F.map_isZero (hb n (.inr hn)))
  apply IsDualizable.of_iso e.symm
  apply DerivedCategory.isDualizable_Q_obj T a b
  intro n
  obtain ⟨r, ⟨er⟩⟩ := hf n
  obtain ⟨ep⟩ := freeFromPoint (DerivedNakayama.integerRing l E) (C.X i) r
  exact (isDualizable_biproduct_unit
    (C := AdicCompletion.Modules l E (C.X i)) r).of_iso
      (F.mapIso er ≪≫ ep.symm).symm

private theorem dualizable_preserves_products
    {A : Type*} [Category A] [MonoidalCategory A]
    (M : A) (hM : IsDualizable M) (I : Type w) :
    PreservesLimitsOfShape (Discrete I) (tensorLeft M) := by
  obtain ⟨hM⟩ := hM
  let := hM
  exact (tensorLeftAdjunction M Mᘁ).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- The uncompleted integral tensor preserves bounded constructibility, and local bounded
finite free scalar complexes are dualizable and preserve products, sequential derived limits
and derived completeness. -/
theorem integralTensorProduct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpl : p ≠ l) :
    (∀ (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      (K L : DerivedCategory (AdicCompletion.Modules l E X)),
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X L →
      constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X (K ⊗ L)) ∧
    (∀ (S : Scheme.{u}) (M : DerivedCategory (AdicCompletion.Modules l E S)),
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i : C.I₀,
        ∃ P : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
          (DerivedNakayama.integerRing l E)) ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
          (∀ n : ℤ, Mod.IsFree (DerivedNakayama.integerRing l E) (P.X n)) ∧
          Nonempty
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
                (C.f i)).mapDerivedCategory.obj M ≅
              DerivedCategory.Q.obj
                (((DerivedNakayama.pullback l E (C.X i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P))) →
      IsDualizable M ∧
        (∀ I : Type w, PreservesLimitsOfShape (Discrete I) (tensorLeft M)) ∧
        (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (AdicCompletion.Modules l E S)) (c : Cone F),
          IsHomotopyLimit c → IsHomotopyLimit ((tensorLeft M).mapCone c)) ∧
        (∀ N : DerivedCategory (AdicCompletion.Modules l E S),
          IsDerivedComplete l E S N → IsDerivedComplete l E S (M ⊗ N))) := by
  constructor
  · exact integralTensorConstructibility l E k p _hp _hpl
  · intro S M hM
    obtain ⟨C, hC⟩ := hM
    have hd := localModel_dualizable l E S M C hC
    refine ⟨hd, dualizable_preserves_products M hd, ?_, ?_⟩
    · intro F c hc
      let := dualizable_preserves_products M hd ℕ
      exact hc.map (tensorLeft M)
    · exact dualizableIntegralCompletion l E S M hd

end AlgebraicGeometry.ProEtale
