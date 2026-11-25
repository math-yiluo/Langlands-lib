/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrices of continuous functions for condensed field presentations

Source: Hemo--Richarz--Scholbach, Example 3.1; the rank/descent argument of
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuous condensed coefficients with the normed-field instances fixed once. -/
noncomputable abbrev condensedFieldCoefficientRingObj
    (E : Type u) [NormedField E] :=
  Profinite.continuousCoefficientRingObj E

/-- The realized coefficient object with its normed-field instances fixed once. -/
noncomputable abbrev condensedFieldContinuousCoefficientObj
    (E : Type u) [NormedField E] (V : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology V)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf V E)

/-- A continuous coefficient endomorphism evaluated on the unit section. -/
noncomputable def condensedFieldContinuousCoefficientMap
    (E : Type u) [NormedField E] (V : Scheme.{u})
    (g : condensedFieldContinuousCoefficientObj E V ⟶
      condensedFieldContinuousCoefficientObj E V) : C(V, E) :=
  ((g.hom.app (op (Scheme.ProEt.mk (𝟙 V)))) (ULift.up 1)).down

/-- The continuous-function matrix of a finite free morphism and a coefficient realization.
Source: Hemo--Richarz--Scholbach, Example 3.1, and the presentation-matrix step of
(auxiliary; not a blueprint node).
Each entry is the image of the unit under the corresponding regular-module endomorphism,
conjugated by the supplied ring-object isomorphism. -/
noncomputable def continuousFieldPresentationMatrix
    (E : Type u) [NormedField E] (V : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ condensedFieldContinuousCoefficientObj E V) [IsIso e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    Matrix (Fin n) (Fin m) C(V, E) := fun i j ↦
  let a := biproduct.ι (fun _ : Fin m ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : Fin n ↦ Mod.regular R) i
  condensedFieldContinuousCoefficientMap E V (inv e ≫ a.hom ≫ e)

/-- The explicit composite uniquely determines the pullback realization.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: the displayed composite is a witness, and the defining equality proves uniqueness. -/
theorem existsUnique_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    ∃! α : (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
    condensedFieldContinuousCoefficientObj E V,
      α = condensedPullbackHom (condensedFieldCoefficientRingObj E) g ≫
        (condensedFieldContinuousMapIso E V).hom.hom := by
  exact ⟨_, rfl, fun _ h ↦ h⟩


/-- The realization of coefficients pulled back along an arbitrary scheme map.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Compose the monoidal coefficient pullback comparison with the canonical realization. -/
noncomputable def condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (condensedFieldCoefficientRingObj E) X) ⟶
    condensedFieldContinuousCoefficientObj E V :=
  condensedPullbackHom (condensedFieldCoefficientRingObj E) g ≫
    (condensedFieldContinuousMapIso E V).hom.hom

/-- The pullback realization equals its explicit defining composite.
Source: Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: the chosen morphism satisfies its uniquely determining equality. This equation
allows controlled rewriting without reducing the inverse-image construction at evaluation. -/
theorem condensedFieldPullbackRealization_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    condensedFieldPullbackRealization E g =
      condensedPullbackHom (condensedFieldCoefficientRingObj E) g ≫
        (condensedFieldContinuousMapIso E V).hom.hom :=
  rfl

instance isIso_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsIso (condensedFieldPullbackRealization E g) := by
  rw [condensedFieldPullbackRealization_eq]
  infer_instance

instance isMonHom_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsMonHom (condensedFieldPullbackRealization E g) := by
  rw [condensedFieldPullbackRealization_eq]
  infer_instance

end AlgebraicGeometry.ProEtale
