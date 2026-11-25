/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveDiagonalComposition
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor

/-! # Invertibility of the normalized left projection on rational localizing objects -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [-instance] internalMonoidal in
private theorem traceProjection_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (h : IsIso (moduleObjectProjectionMate Λ f N K)) :
    IsIso (traceProjection Λ f K N) := by
  have := h
  unfold traceProjection
  infer_instance

private theorem normalized_projection_isIso (a : ProjectionFamily Λ)
    (ha : ProjectionNormalized Λ a) {X S : Scheme.{u}} (f : X ⟶ S)
    (K : DerivedCategory (Modules Λ S)) (N : DerivedCategory (Modules Λ X))
    (h : IsIso (moduleObjectProjectionMate Λ f N K)) : IsIso (a f K N) := by
  unfold ProjectionNormalized ProjectionFamily internalMonoidal
    internalTensorBundle nativeTensorBundle at *
  dsimp only at ha
  rw [eq_of_heq (ha f K N)]
  exact traceProjection_isIso Λ f K N h

-- Specialize the two-variable extension through the internal module comparisons.
attribute [-instance] internalMonoidal in
private theorem selected_projection_isIso
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f]
    (N : DerivedCategory (Modules (coefficient l c).X X))
    (K : DerivedCategory (Modules (coefficient l c).X S))
    (hN : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X X) N)
    (hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X S) K) :
    IsIso (moduleObjectProjectionMate (coefficient l c).X f N K) := by
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  let Λ := (coefficient l c).X
  have hbc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) := by
    cases c with
    | none =>
      exact constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k l T
    | some E =>
      exact constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k l E T
  have hctf (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T := by
    have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
    have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
    apply (localizingClosure_ctf_equals_bc l T Λ ?_).1.2.2.1
    cases c with
    | none => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
    | some E => exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr ⟨Iso.refl _⟩⟩))
  let E := c.getD ⟨⊥, inferInstance⟩
  have hcoeff : coefficient l c ∈
      [Mon.mk (Profinite.continuousMapRingObj (ZMod l)),
        Mon.mk (Profinite.continuousMapRingObj ℤ_[l]),
        Mon.mk (Profinite.padicIntegersRingObj l E.val),
        Mon.mk (Profinite.continuousMapRingObj ℚ_[l]),
        Mon.mk (Profinite.continuousMapRingObj E), Mon.mk (Profinite.padicAlgClRingObj l)] := by
    cases c <;> simp [coefficient, E]
  have hp := proper_image_localizing_proper_coefficients l E (ZMod l) ⟨1, by simp⟩
    (coefficient l c) hcoeff k f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (S ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated (S ↘ Spec (.of k))
  have htensor (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      ∀ A B, constantModelBoundedConstructible Λ T A →
        constantModelBoundedConstructible Λ T B →
        constantModelBoundedConstructible Λ T (A ⊗ B) := by
    intro A B hA hB
    have hc : (∃ E : PadicAlgCl.FiniteIntermediateField l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj l)) := by
      cases c with
      | none => exact Or.inr ⟨Iso.refl _⟩
      | some E => exact Or.inl ⟨E, ⟨Iso.refl _⟩⟩
    exact (constantModelBoundedConstructible_derivedTensor l p hpl
      (T ↘ Spec (.of k)) Λ hc).1 A B hA hB
  apply (projection_localizing_of_interfaces Λ f (hbc X) (hbc S) (hctf X) (hctf S)
    hp (pullback_bounded_constructible Λ f (pullback_constructible Λ f))
    (htensor X) (htensor S) ?_ N K hN hK).2.2
  intro A B hA hB
  have hc : (∃ E : PadicAlgCl.FiniteIntermediateField l,
      coefficient l c = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      coefficient l c = Mon.mk (Profinite.padicAlgClRingObj l) := by
    cases c with
    | none => exact Or.inr rfl
    | some E => exact Or.inl ⟨E, rfl⟩
  have : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : LocallyOfFiniteType (S.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (S ↘ Spec (.of k)))
  have : QuasiCompact (S.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (S ↘ Spec (.of k)))
  have : IsSeparated (S.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (S ↘ Spec (.of k)))
  have : IsProper (f.asOver (Spec (.of k))).left := inferInstanceAs (IsProper f)
  exact (canonical_projection_isIso Λ f A B).mp
    (isIso_properProjectionMap_boundedConstructible_rational l
      (f.asOver (Spec (.of k))) (coefficient l c) hc A B hA hB)

/-- The fixed left-factor projection is invertible on rational localizing objects. -/
theorem projectionMap_isIso_localizing
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    (f : X ⟶ S) [f.IsOver (Spec (.of k))] [IsProper f]
    (K : DerivedCategory (Modules (coefficient l c).X S))
    (N : DerivedCategory (Modules (coefficient l c).X X))
    (hK : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X S) K)
    (hN : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X X) N) :
    IsIso (projectionMap (coefficient l c).X f K N) := by
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ l) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  apply normalized_projection_isIso (coefficient l c).X
    (projection_existsUnique (coefficient l c).X).exists.choose
    (projection_existsUnique (coefficient l c).X).exists.choose_spec f K N
  exact selected_projection_isIso l c k p hpl f N K hN hK

end AlgebraicGeometry.ProEtale.RationalP1
