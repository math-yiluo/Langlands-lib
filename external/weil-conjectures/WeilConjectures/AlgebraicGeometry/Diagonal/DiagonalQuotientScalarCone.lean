/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalScalarCone
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Quotient-normalized reductions are scalar cones

Source: Stacks 099M and uniqueness of pointwise left derived functors.
(blueprint: lem-sfb-diagonal-quotient-scalar-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

variable {A : Type a} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private theorem reduction_computes_regular (ℓ : ℕ)
    (D : DiagonalDerivedReduction ℓ (𝟭 A))
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
        (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p)
    (P : CochainComplex A ℤ)
    (hP : ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) :
    IsIso (D.ε.app P) := by
  let good : CochainComplex A ℤ → Prop := fun Q ↦
    ∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (Q.X i))
  obtain ⟨T, ε, hu, _, _, hc⟩ := cochainDerivedFullExists D.ordinary.E good res (by
    intro X Y f hf hX hY
    let := hf
    exact reductionTower_quasiIso ℓ (𝟭 A) D.ordinary f hX hY)
  let := hu
  let := D.universal
  let c := Functor.leftDerivedNatIso D.T T D.ε ε
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _)
  have h : c.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = D.ε.app P := by
    dsimp only [c, Functor.leftDerivedNatIso]
    simpa only [Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      Functor.leftDerivedNatTrans_app D.T T D.ε ε
        (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 _) P
  let := hc P hP
  rw [← h]
  infer_instance

/-- In any abelian category admitting regular resolutions, normalized simultaneous
quotients are the localized two-term scalar cones, including their quotient units.

Source: Stacks 099M, the free two-term resolution, and Stacks 06YY.
(blueprint: lem-sfb-diagonal-quotient-scalar-cone).
Proof: evaluate the supplied left derived functor. Exact evaluation is a right
adjoint with exact left adjoint, so preserves its pointwise right Kan extension.
The cone-to-cokernel maps give another counit. On regular resolutions they are
quasi-isomorphisms, as is the supplied counit by uniqueness of left derived
functors on the regular resolving class. The universal comparison is therefore
invertible on resolutions and hence on every derived object. Its defining counit
square and the two unit formulas prove the unit equation on regular resolutions.
Naturality transports it to every object. -/
theorem diagonal_quotient_scalar_cone (ℓ : ℕ) (N : DiagonalCompletedReductionData ℓ A)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
        (∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 (P.X i))) ∧ QuasiIso p)
    (n : ℕ) :
    let E := ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory
    ∃ α : N.derived.T ⋙ E ≅ diagonalScalarCone A (ℓ ^ (n + 1)),
      ∀ X : DerivedCategory A,
        (N.unit n).app X ≫ α.hom.app X =
          (diagonalScalarConeUnit A (ℓ ^ (n + 1))).app X := by
  let D := N.derived
  let V := (evaluation ℕᵒᵖ A).obj (op n)
  let G := D.T ⋙ V.mapDerivedCategory
  let E := D.ordinary.E.mapHomologicalComplex (.up ℤ)
  let F := E ⋙ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let q : 𝟭 (CochainComplex A ℤ) ⟶ E ⋙ V.mapHomologicalComplex (.up ℤ) :=
    NatTrans.mapHomologicalComplex (D.ordinary.π n) (.up ℤ)
  let S (P : CochainComplex A ℤ) := ShortComplex.mk
    (ℓ ^ (n + 1) • 𝟙 P) (q.app P) (by ext i; exact D.ordinary.zero n (P.X i))
  let c : diagonalScalarConeComplex A (ℓ ^ (n + 1)) ⟶
      E ⋙ V.mapHomologicalComplex (.up ℤ) :=
    { app P := CochainComplex.mappingCone.descShortComplex (S P)
      naturality P Q f := by
        let t : S P ⟶ S Q :=
          { τ₁ := f, τ₂ := f, τ₃ := (E ⋙ V.mapHomologicalComplex (.up ℤ)).map f
            comm₁₂ := by
              simp only [S, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
                Category.id_comp, Category.comp_id]
            comm₂₃ := q.naturality f }
        exact CochainComplex.mappingCone.map_descShortComplex (S P) (S Q) t }
  let α : DerivedCategory.Q ⋙ G ⟶ F :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.ε V.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft E V.mapDerivedCategoryFactors.hom
  let β : DerivedCategory.Q ⋙ diagonalScalarCone A (ℓ ^ (n + 1)) ⟶ F :=
    (diagonalScalarConeFactors A (ℓ ^ (n + 1))).hom ≫
      Functor.whiskerRight c DerivedCategory.Q
  let H := evaluationLeftAdjoint A (op n)
  have : PreservesFiniteLimits H := evaluationLeft_exact (op n)
  have : H.IsLeftAdjoint := (evaluationAdjunctionRight A (op n)).isLeftAdjoint
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have : V.mapDerivedCategory.IsRightAdjoint :=
    (evaluationAdjunctionRight A (op n)).onDerivedCategory.isRightAdjoint
  let := D.universal
  let := D.pointwise
  have : Functor.HasPointwiseRightKanExtension DerivedCategory.Q (E ⋙ DerivedCategory.Q) :=
    Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor _
      DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  have : D.T.IsRightKanExtension D.ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension D.T D.ε
      (HomologicalComplex.quasiIso A (.up ℤ))
  let α₀ : DerivedCategory.Q ⋙ G ⟶ (E ⋙ DerivedCategory.Q) ⋙ V.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.ε V.mapDerivedCategory
  have : G.IsRightKanExtension α₀ :=
    Functor.PreservesRightKanExtension.preserves D.T D.ε
  have : G.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ)) := by
    let e : (E ⋙ DerivedCategory.Q) ⋙ V.mapDerivedCategory ≅ F :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft E V.mapDerivedCategoryFactors
    refine ⟨(Functor.isRightKanExtension_iff_of_iso₂ α₀ α e (Iso.refl G) ?_).1
      inferInstance⟩
    ext P
    simp [α₀, α, e]
  let τ := G.leftDerivedLift α (HomologicalComplex.quasiIso A (.up ℤ))
    (diagonalScalarCone A (ℓ ^ (n + 1))) β
  have hτ (P : CochainComplex A ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ α.app P = β.app P :=
    G.leftDerived_fac_app α (HomologicalComplex.quasiIso A (.up ℤ)) _ β P
  have hi (P : CochainComplex A ℤ)
      (hP : ∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 (P.X i))) :
      IsIso (τ.app (DerivedCategory.Q.obj P)) := by
    have hε := reduction_computes_regular ℓ D res P hP
    let := hε
    have hα : IsIso (α.app P) := by
      dsimp only [α, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    have hs : (S P).ShortExact := by
      exact reductionComplexSequence_shortExact ℓ (𝟭 A) D.ordinary n P (hP n)
    have : QuasiIso (c.app P) := CochainComplex.mappingCone.quasiIso_descShortComplex hs
    have hβ : IsIso (β.app P) := by
      change IsIso ((diagonalScalarConeFactors A (ℓ ^ (n + 1))).hom.app P ≫
        DerivedCategory.Q.map (c.app P))
      infer_instance
    have : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ α.app P) := by rw [hτ]; exact hβ
    exact IsIso.of_isIso_comp_right _ (α.app P)
  have hiall (X : DerivedCategory A) : IsIso (τ.app X) := by
    obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage X)
    let := hp
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso τ e).1 (hi P hP)
  let := NatIso.isIso_of_isIso_app τ
  refine ⟨(asIso τ).symm, ?_⟩
  intro X
  have heq (P : CochainComplex A ℤ)
      (hP : ∀ (m : ℕ) (i : ℤ), Mono (ℓ ^ (m + 1) • 𝟙 (P.X i))) :
      (diagonalScalarConeUnit A (ℓ ^ (n + 1))).app (DerivedCategory.Q.obj P) ≫
        τ.app (DerivedCategory.Q.obj P) = (N.unit n).app (DerivedCategory.Q.obj P) := by
    let := reduction_computes_regular ℓ D res P hP
    have : IsIso (α.app P) := by
      dsimp only [α, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance
    apply (cancel_mono (α.app P)).1
    rw [Category.assoc, hτ]
    change _ ≫ ((diagonalScalarConeFactors A (ℓ ^ (n + 1))).hom.app P ≫
      DerivedCategory.Q.map (c.app P)) = _
    rw [← Category.assoc, diagonalScalarConeUnit_factors, ← DerivedCategory.Q.map_comp]
    have hc : CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 P) ≫ c.app P =
        q.app P := CochainComplex.mappingCone.inr_descShortComplex (S P)
    rw [hc]
    dsimp only [α, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    erw [Category.id_comp, Category.id_comp]
    exact (N.normalization P n).symm
  obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage X)
  let := hp
  let e : DerivedCategory.Q.obj P ≅ X :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have hx : (diagonalScalarConeUnit A (ℓ ^ (n + 1))).app X ≫ τ.app X =
      (N.unit n).app X := by
    apply (cancel_epi e.hom).1
    have hn := (diagonalScalarConeUnit A (ℓ ^ (n + 1))).naturality e.hom
    have ht := τ.naturality e.hom
    have hu := (N.unit n).naturality e.hom
    change e.hom ≫ _ = _ ≫ _ at hn hu
    rw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc, heq P hP]
    exact hu.symm
  apply (cancel_mono (τ.app X)).1
  simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  change ((N.unit n).app X ≫ inv (τ.app X)) ≫ τ.app X = _
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hx.symm

end AlgebraicGeometry.ProEtale
