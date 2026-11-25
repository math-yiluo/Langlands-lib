/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationModel

/-! # Transporting localization colimits from a strict complex model -/

@[expose] public section

universe u v w x y z
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable def sequenceComparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (C : A) (K : B) (e : F.obj C ≅ K) :
    Mod.smulSequence C ℓ ⋙ F ⟶ Mod.smulSequence K ℓ where
  app _ := e.hom
  naturality _ _ _ := by
    simp [F.map_nsmul]

omit [Fact ℓ.Prime] in
/-- Transport colimits from a strict complex telescope along its localization-unit model.
Source: Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node).
Proof: whisker the representative isomorphism to identify the diagrams, and use the
model vertex isomorphism and its leg equations to identify the cocones. -/
theorem localizationCocone_isColimit_of_model
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [HasColimitsOfShape (ULift.{x} ℕ) A]
    (K : DerivedCategory A) (c : Cocone (Mod.smulSequence K ℓ))
    (m : IntegralLocalizationComplexModel.{v, w, x} ℓ K c)
    {B : Type y} [Category.{z} B] (F : DerivedCategory A ⥤ B)
    (hcont : ∀ (C : CochainComplex A ℤ) (a : ℤ), C.IsStrictlyGE a →
      Nonempty (IsColimit ((DerivedCategory.Q ⋙ F).mapCocone
        (condensedContinuityCocone
          (integralLocalizationLiftedSequence.{max v w, w, x} ℓ C) a)))) :
    Nonempty (IsColimit (F.mapCocone (c.whisker
      (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor))) := by
  let C := m.complex
  let a := m.bound
  let e := m.representative
  let v := m.comparison
  have hv := m.leg
  have hC := m.strictlyGE
  let J := (ULift.orderIso : ULift.{x} ℕ ≃o ℕ).equivalence.functor
  let D := integralLocalizationLiftedSequence.{max v w, w, x} ℓ C
  let α₀ := sequenceComparison ℓ DerivedCategory.Q C K e.symm
  let α := Functor.whiskerRight (Functor.whiskerLeft J α₀) F
  have : ∀ n, IsIso (α.app n) := fun n ↦ by
    change IsIso (F.map e.inv)
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let cF := F.mapCocone (c.whisker J)
  obtain ⟨hc⟩ := hcont C a hC
  refine ⟨(IsColimit.precomposeHomEquiv (asIso α) cF) ?_⟩
  apply hc.ofIsoColimit
  refine Cocone.ext (F.mapIso v) ?_
  intro n
  change F.map (DerivedCategory.Q.map
      ((condensedContinuityCocone D a).ι.app n)) ≫ F.map v.hom =
    F.map e.inv ≫ F.map (c.ι.app n.down)
  rw [← F.map_comp, ← F.map_comp, hv]

end AlgebraicGeometry.ProEtale.CondensedRing
