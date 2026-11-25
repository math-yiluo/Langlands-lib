/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalQuotientScalarCone
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerScalarConeIsIso
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalReductionResolution
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves

/-! # Finite reduction of the normalized total limit

(blueprint: lem-sfb-diagonal-adic-evaluation-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.ProEtale

private theorem moduleUnit_mono (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (r : ℕ) (hr : r ≠ 0) : Mono (r • 𝟙 (𝟙_ (DiagonalMod ℓ W))) := by
  let R := ULift.{u + 1} ℤ_[ℓ]
  have hm : Mono (r • 𝟙 (ModuleCat.of R R)) := by
    rw [ModuleCat.mono_iff_injective]
    intro x y h
    change r • x = r • y at h
    exact ULift.ext (nsmul_right_injective hr (congrArg ULift.down h))
  have hm' : Mono (r • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R))) := by
    have : Mono ((Functor.const W.ProEtᵒᵖ).map (r • 𝟙 (ModuleCat.of R R))) :=
      NatTrans.mono_of_mono_app _
    have : Mono ((presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} R)).map
        ((Functor.const W.ProEtᵒᵖ).map (r • 𝟙 (ModuleCat.of R R)))) := inferInstance
    have hmap : (Functor.const W.ProEtᵒᵖ).map (𝟙 (ModuleCat.of R R)) = 𝟙 _ :=
      (Functor.const W.ProEtᵒᵖ).map_id _
    have hsheaf := (presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} R)).map_id
      ((Functor.const W.ProEtᵒᵖ).obj (ModuleCat.of R R))
    rw [Functor.map_nsmul, hmap, Functor.map_nsmul, hsheaf] at this
    exact this
  exact hm'

private theorem module_regular_resolutions (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (K : CochainComplex (DiagonalMod ℓ W) ℤ) :
    ∃ (P : CochainComplex (DiagonalMod ℓ W) ℤ) (p : P ⟶ K),
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) ∧ QuasiIso p := by
  obtain ⟨P, p, hp, hflat, _⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  refine ⟨P, p, ?_, hp⟩
  intro n i
  exact flat_multiplication_mono _
    (moduleUnit_mono ℓ W _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)) _ (hflat i)

/-- Reduction of a total limit of derived quotient towers is naturally evaluation;
the comparison is the adjoint of the actual limit projection.

Source: Stacks 099M; blueprint diagonal tower limit proof, paragraph (3), and
`lemma-weil-pbc-adic-completion-reduction`.
(blueprint: lem-sfb-diagonal-adic-evaluation-comparison).
Proof: identify D's ordinary cokernel tower with the strict scalar quotient tower.
Uniqueness of its pointwise left derived functor identifies D.T with the K-flat
quotient model; uniqueness of total right derived limits identifies L.R and its
projections with the normalized adic completion model. The finite quotient is
perfect, with the two-term resolution by multiplication by ell^(n+1). The adic
completion reduction theorem makes the adjoint of each projection an isomorphism.
Uniqueness of the pointwise left derived quotient identifies any normalized N with
this same finite reduction. Transport the evaluation-adjoint comparison through
these identifications. Its adjunction unit formula gives the displayed equation,
and functoriality on K-flat representatives descends to a natural isomorphism on
the entire integral derived category. -/
theorem diagonal_adic_evaluation_comparison (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (hcompletion : DiagonalCompletionSpec ℓ W D)
    (L : DiagonalRlim (DiagonalMod ℓ W))
    (N : DiagonalCompletedReductionData ℓ (DiagonalMod ℓ W)) (n : ℕ) :
    let E := ((evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)).mapDerivedCategory
    ∃ β : D.T ⋙ L.R ⋙ N.derived.T ⋙ E ≅ D.T ⋙ E,
      ∀ K : DerivedCategory (DiagonalAb W),
        (N.unit n).app (L.R.obj (D.T.obj K)) ≫ β.hom.app K =
          (L.projection n).app (D.T.obj K) := by
  classical
  have _ := hcompletion
  let A := DiagonalAb W
  let B := DiagonalMod ℓ W
  let V := (evaluation ℕᵒᵖ B).obj (op n)
  let E := V.mapDerivedCategory
  let C := diagonalScalarCone B (ℓ ^ (n + 1))
  obtain ⟨a, ha⟩ := diagonal_quotient_scalar_cone ℓ N
    (module_regular_resolutions ℓ W) n
  let G := D.T ⋙ E
  let H := D.T ⋙ L.R ⋙ C
  let O := D.ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let α : DerivedCategory.Q ⋙ G ⟶ O ⋙ E :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.ε E
  let β : DerivedCategory.Q ⋙ H ⟶ O ⋙ E :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.ε (L.R ⋙ C) ≫
      diagonalTowerScalarConeComparison D.ordinary L n
  let Hleft := evaluationLeftAdjoint B (op n)
  have : PreservesFiniteLimits Hleft := evaluationLeft_exact (op n)
  have : Hleft.IsLeftAdjoint := (evaluationAdjunctionRight B (op n)).isLeftAdjoint
  have : Hleft.Additive := Functor.additive_of_preserves_binary_products Hleft
  have : E.IsRightAdjoint := (evaluationAdjunctionRight B (op n)).onDerivedCategory.isRightAdjoint
  let := D.universal
  let := D.pointwise
  have : Functor.HasPointwiseRightKanExtension DerivedCategory.Q O :=
    Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor _
      DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  have : D.T.IsRightKanExtension D.ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension D.T D.ε
      (HomologicalComplex.quasiIso A (.up ℤ))
  have : G.IsRightKanExtension α := Functor.PreservesRightKanExtension.preserves D.T D.ε
  let τ : H ⟶ G := G.liftOfIsRightKanExtension α H β
  have hτ (P : CochainComplex A ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫ E.map (D.ε.app P) =
        (L.R ⋙ C).map (D.ε.app P) ≫
          (diagonalTowerScalarConeComparison D.ordinary L n).app P := by
    have hh := G.liftOfIsRightKanExtension_fac_app α H β P
    dsimp only [α, β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app] at hh
    change τ.app (DerivedCategory.Q.obj P) ≫ (𝟙 _ ≫ E.map (D.ε.app P)) =
      𝟙 _ ≫ (L.R ⋙ C).map (D.ε.app P) ≫
        (diagonalTowerScalarConeComparison D.ordinary L n).app P at hh
    simpa only [Category.id_comp] using hh
  have hi (K : DerivedCategory A) : IsIso (τ.app K) := by
    obtain ⟨P, e, hP, hε⟩ := diagonal_reduction_resolution ℓ W D K
    let := hε
    have : IsIso ((diagonalTowerScalarConeComparison D.ordinary L n).app P) :=
      diagonal_tower_scalar_cone_isIso ℓ W D.ordinary L n P hP
    have hh : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ E.map (D.ε.app P)) := by
      rw [hτ]
      infer_instance
    have : IsIso (τ.app (DerivedCategory.Q.obj P)) :=
      IsIso.of_isIso_comp_right _ (E.map (D.ε.app P))
    exact (NatTrans.isIso_app_iff_of_iso τ e).1 this
  let := NatIso.isIso_of_isIso_app τ
  let b : D.T ⋙ L.R ⋙ N.derived.T ⋙ E ≅ G :=
    Functor.isoWhiskerLeft (D.T ⋙ L.R) a ≪≫ asIso τ
  refine ⟨b, ?_⟩
  intro K
  have hunit (P : CochainComplex A ℤ) (hε : IsIso (D.ε.app P)) :
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app
          (L.R.obj (D.T.obj (DerivedCategory.Q.obj P))) ≫
        τ.app (DerivedCategory.Q.obj P) =
          (L.projection n).app (D.T.obj (DerivedCategory.Q.obj P)) := by
    let := hε
    apply (cancel_mono (E.map (D.ε.app P))).1
    rw [Category.assoc, hτ]
    have hn := (diagonalScalarConeUnit B (ℓ ^ (n + 1))).naturality
      (L.R.map (D.ε.app P))
    change L.R.map (D.ε.app P) ≫
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app
        (L.R.obj (DerivedCategory.Q.obj ((D.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P))) =
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app
        (L.R.obj (D.T.obj (DerivedCategory.Q.obj P))) ≫
      (L.R ⋙ C).map (D.ε.app P) at hn
    rw [← Category.assoc, ← hn, Category.assoc,
      diagonalTowerScalarConeComparison_unit]
    exact (L.projection n).naturality (D.ε.app P)
  have hall (X : DerivedCategory A) :
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app (L.R.obj (D.T.obj X)) ≫
        τ.app X = (L.projection n).app (D.T.obj X) := by
    obtain ⟨P, e, _, hε⟩ := diagonal_reduction_resolution ℓ W D X
    apply (cancel_epi ((D.T ⋙ L.R).map e.hom)).1
    have hu := (diagonalScalarConeUnit B (ℓ ^ (n + 1))).naturality
      ((D.T ⋙ L.R).map e.hom)
    change (D.T ⋙ L.R).map e.hom ≫
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app (L.R.obj (D.T.obj X)) =
      (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app
        (L.R.obj (D.T.obj (DerivedCategory.Q.obj P))) ≫ H.map e.hom at hu
    rw [← Category.assoc, hu, Category.assoc, τ.naturality,
      ← Category.assoc, hunit P hε]
    exact (L.projection n).naturality (D.T.map e.hom) |>.symm
  change (N.unit n).app _ ≫ (a.hom.app _ ≫ τ.app K) = _
  rw [← Category.assoc, ha]
  exact hall K

end AlgebraicGeometry.ProEtale
