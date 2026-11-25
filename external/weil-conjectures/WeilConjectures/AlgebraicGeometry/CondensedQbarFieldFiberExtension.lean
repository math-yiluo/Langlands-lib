/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction

import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def fieldFiber_extension_component
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) :
    (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).obj M ≅
      ((((upperStar Ab (Spec.map (CommRingCat.ofHom i))).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) ⋙
          Mod.comap (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
            (Spec.map (CommRingCat.ofHom i))))) ⋙
              CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).obj M := by
  let f := Spec.map (CommRingCat.ofHom i)
  have : IsIso (geometricFieldEvaluationComparison f Ab.{u + 1}) :=
    (geometric_field_proetale_evaluation_extension K K' i).2.2.2.2.1
  refine ModuleCat.isoMk ((asIso (geometricFieldEvaluationComparison f Ab)).app M.X) ?_
  intro r
  exact condensedQbar_field_evaluation_linear ℓ K K' i M r

private theorem fieldFiber_extension_component_naturality
    (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K')
    {M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))}
    (g : M ⟶ N) :
    (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).map g ≫
        (fieldFiber_extension_component ℓ K K' i N).hom =
      (fieldFiber_extension_component ℓ K K' i M).hom ≫
        (((((upperStar Ab (Spec.map (CommRingCat.ofHom i))).mapMod
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) ⋙
            Mod.comap (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
              (Spec.map (CommRingCat.ofHom i))))) ⋙
                CondensedQbarGeometricEvaluation.fieldFiber K' ℓ).map g) := by
  apply (forget₂ (ModuleCat (PadicAlgCl ℓ)) Ab).map_injective
  change g.hom.hom.app _ ≫
      (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) Ab).app N.X =
    (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) Ab).app M.X ≫
      ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) Ab).map g.hom).hom.app _
  exact (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) Ab).naturality g.hom

private noncomputable def fieldFiber_extension_comapIso (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') : CondensedQbarGeometricEvaluation.fieldFiber K ℓ ≅
      ((((upperStar Ab (Spec.map (CommRingCat.ofHom i))).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K)))) ⋙
          Mod.comap (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
            (Spec.map (CommRingCat.ofHom i))))) ⋙
              CondensedQbarGeometricEvaluation.fieldFiber K' ℓ) := by
  refine NatIso.ofComponents (fun M ↦ fieldFiber_extension_component ℓ K K' i M) ?_
  intro M N g
  exact fieldFiber_extension_component_naturality ℓ K K' i g

private theorem whisker_comparison
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    (G : C ⥤ D) (H H' : D ⥤ E) (T : E ⥤ F) (S : C ⥤ F)
    (U : C ⥤ E) (hU : U = G ⋙ H')
    (e : S ≅ (G ⋙ H) ⋙ T) (h : H ≅ H') :
    Nonempty (S ≅ U ⋙ T) := by
  subst U
  exact ⟨e ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft G h) T⟩

/-- Algebraically closed field extension preserves the constructed module evaluation.

Source: Bhatt--Scholze, Example 4.1.10; RefactorInstruction, Section 4, geometric
fiber comparison in the finite-matrix refinement, steps 1--3
(auxiliary; not a blueprint node).

Proof: use the concrete scalar-linearity theorem for the canonical abelian
comparison. The comparison is invertible by geometric field evaluation under
extension. ModuleCat.isoMk lifts it to module isomorphisms; its sheaf naturality
proves naturality on modules. Finally, extendScalarsIsoComapInv identifies the
restriction-along-inverse formula with the actual module inverse image.
-/
theorem condensedQbar_fieldFiber_extension (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') : Nonempty
    (CondensedQbarGeometricEvaluation.fieldFiber K ℓ ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        (Spec.map (CommRingCat.ofHom i)) ⋙
          CondensedQbarGeometricEvaluation.fieldFiber K' ℓ) := by
  exact whisker_comparison
    ((upperStar Ab (Spec.map (CommRingCat.ofHom i))).mapMod
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))))
    (Mod.comap (inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i)))))
    (Mod.extendScalars (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i))))
    (CondensedQbarGeometricEvaluation.fieldFiber K' ℓ)
    (CondensedQbarGeometricEvaluation.fieldFiber K ℓ)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i))) rfl
    (fieldFiber_extension_comapIso ℓ K K' i)
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ)
      (Spec.map (CommRingCat.ofHom i)))).symm

end AlgebraicGeometry.ProEtale
