/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Systems supported at one finite coefficient level -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
open scoped ZeroObject
namespace AlgebraicGeometry
attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

variable (O : Type (u + 1)) [CommRing O] (ell : O) (T : Scheme.{u})

private theorem systemHom_ext {M N : strictEtaleCoefficientSystem T O ell}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  change CoefficientSystem.Hom (J := T.smallEtaleTopology) (O := O) (ell := ell) M N at f g
  cases f
  cases g
  cases h
  rfl

private def singletonLevel (n m : ℕ) : strictEtaleLevel T O ell n ⥤
    strictEtaleLevel T O ell m := if h : m = n then h ▸ 𝟭 _ else 0

private instance singletonLevelAdditive (n m : ℕ) :
    (singletonLevel O ell T n m).Additive := by
  by_cases h : m = n
  · subst m; simpa [singletonLevel] using
      (inferInstance : (𝟭 (strictEtaleLevel T O ell n)).Additive)
  · simpa only [singletonLevel, dite_eq_right h] using
      (inferInstance : (0 : strictEtaleLevel T O ell n ⥤ strictEtaleLevel T O ell m).Additive)

private def singleton (n : ℕ) :
    strictEtaleLevel T O ell n ⥤ strictEtaleCoefficientSystem T O ell where
  obj N := {
    level := fun m ↦ (singletonLevel O ell T n m).obj N
    transition := fun _ ↦ 0 }
  map f := {
    app := fun m ↦ (singletonLevel O ell T n m).map f
    comm := by intro m; simp }
  map_id N := by
    apply systemHom_ext O ell T
    funext m
    exact (singletonLevel O ell T n m).map_id N
  map_comp f g := by
    apply systemHom_ext O ell T
    funext m
    exact (singletonLevel O ell T n m).map_comp f g

private def singletonEvaluation (n : ℕ) :
    singleton O ell T n ⋙ coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) n ≅ 𝟭 _ := by
  change singletonLevel O ell T n n ≅ 𝟭 _
  exact eqToIso (by simp [singletonLevel])

private def singletonOther (n m : ℕ) (h : m ≠ n) :
    singleton O ell T n ⋙ coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) m ≅ 0 := by
  change singletonLevel O ell T n m ≅ 0
  exact eqToIso (by simp only [singletonLevel, dite_eq_right h])

private instance singletonAdditive (n : ℕ) : (singleton O ell T n).Additive where
  map_add {N N'} f g := by
    apply systemHom_ext O ell T
    funext m
    change (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology) m).map
      ((singleton O ell T n).map (f + g)) =
      (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology) m).map
        ((singleton O ell T n).map f + (singleton O ell T n).map g)
    rw [(coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) m).map_add (f := (singleton O ell T n).map f)
        (g := (singleton O ell T n).map g)]
    exact (singletonLevel O ell T n m).map_add (f := f) (g := g)

private theorem evaluationsConservative :
    JointlyReflectIsomorphisms
      (coefficientEvaluation.{u + 1, u, u + 1}
        (J := T.smallEtaleTopology) (O := O) (ell := ell)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := T.smallEtaleTopology) O ell
          (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩ <;> apply systemHom_ext O ell T <;> funext n
    · exact IsIso.hom_inv_id (f.app n)
    · exact IsIso.inv_hom_id (f.app n)

private instance evalLimits (m : ℕ) : PreservesFiniteLimits
    (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (O := O) (ell := ell) m) :=
  (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) m).1
private instance evalColimits (m : ℕ) : PreservesFiniteColimits
    (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology) (O := O) (ell := ell) m) :=
  (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) m).2

private instance singletonEvaluationLimits (n m : ℕ) : PreservesFiniteLimits
    (singleton O ell T n ⋙ coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) m) := by
  by_cases h : m = n
  · subst m
    exact preservesFiniteLimits_of_natIso (singletonEvaluation O ell T n).symm
  · have : PreservesLimits (0 : strictEtaleLevel T O ell n ⥤ strictEtaleLevel T O ell m) :=
      Functor.preservesLimitsOfSize_of_isZero _ (isZero_zero _)
    exact preservesFiniteLimits_of_natIso (singletonOther O ell T n m h).symm

private instance singletonEvaluationColimits (n m : ℕ) : PreservesFiniteColimits
    (singleton O ell T n ⋙ coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) m) := by
  by_cases h : m = n
  · subst m
    exact preservesFiniteColimits_of_natIso (singletonEvaluation O ell T n).symm
  · have : PreservesColimits (0 : strictEtaleLevel T O ell n ⥤ strictEtaleLevel T O ell m) :=
      Functor.preservesColimitsOfSize_of_isZero _ (isZero_zero _)
    exact preservesFiniteColimits_of_natIso (singletonOther O ell T n m h).symm

private instance singletonLimits (n : ℕ) : PreservesFiniteLimits (singleton O ell T n) where
  preservesFiniteLimits {I} _ _ := {
    preservesLimit := fun {K} ↦ {
      preserves := fun {c} hc ↦ ⟨(evaluationsConservative O ell T).jointlyReflectsLimit
        (fun m ↦ by
          exact isLimitOfPreserves (singleton O ell T n ⋙ coefficientEvaluation
            (J := T.smallEtaleTopology) (O := O) (ell := ell) m) hc)⟩ } }

private instance singletonColimits (n : ℕ) : PreservesFiniteColimits (singleton O ell T n) where
  preservesFiniteColimits {I} _ _ := {
    preservesColimit := fun {K} ↦ {
      preserves := fun {c} hc ↦ ⟨(evaluationsConservative O ell T).jointlyReflectsColimit
        (fun m ↦ by
          exact isColimitOfPreserves (singleton O ell T n ⋙ coefficientEvaluation
            (J := T.smallEtaleTopology) (O := O) (ell := ell) m) hc)⟩ } }

private def evaluationIso (PE : StrictEtaleEvaluation T O ell) (n : ℕ) :
    PE.evaluation n ≅ (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
      (O := O) (ell := ell) n).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (strictEtaleCoefficientSystem T O ell) (.up ℤ))
    _ _ _ _ (PE.evaluationFactors n ≪≫
      (coefficientEvaluation.{u + 1, u, u + 1} (J := T.smallEtaleTopology)
        (O := O) (ell := ell) n).mapDerivedCategoryFactors.symm)

/-- Every bounded-below finite coefficient object is the evaluation of a system
with the same lower bound, whose other evaluations vanish.
Source: Zheng Construction 4.1, the exact evaluation and its single-level section.
(blueprint: lem-sf-exceptional-evaluation-singleton).

Proof: put the given module at level n, zero at every other level, and zero in
all successive transition maps. This defines an additive exact functor: after
each evaluation it is the identity or zero, and evaluations jointly reflect
finite limits and colimits. Apply its exact functor on derived categories.
The uniqueness of exact localization identifies its evaluations with identity
and zero, and exactness preserves the original lower bound. -/
theorem exceptionalEvaluationSingleton (PE : StrictEtaleEvaluation T O ell)
    (n : ℕ) (N : DerivedCategory (strictEtaleLevel T O ell n)) (a : ℤ) (hN : N.IsGE a) :
    ∃ M : DerivedCategory (strictEtaleCoefficientSystem T O ell),
      M.IsGE a ∧ Nonempty ((PE.evaluation n).obj M ≅ N) ∧
      ∀ m, m ≠ n → IsZero ((PE.evaluation m).obj M) := by
  let F := singleton O ell T n
  have := hN
  refine ⟨F.mapDerivedCategory.obj N, F.isGE_mapDerivedCategory_obj N a, ?_, ?_⟩
  · let e := isoWhiskerLeft F.mapDerivedCategory (evaluationIso O ell T PE n) ≪≫
      mapDerivedCategoryCompIso F (coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O) (ell := ell) n) ≪≫
      mapDerivedCategoryNatIso (singletonEvaluation O ell T n) ≪≫
      mapDerivedCategoryIdIso (strictEtaleLevel T O ell n)
    exact ⟨e.app N⟩
  · intro m h
    let E := coefficientEvaluation.{u + 1, u, u + 1}
      (J := T.smallEtaleTopology) (O := O) (ell := ell) m
    let e := isoWhiskerLeft F.mapDerivedCategory (evaluationIso O ell T PE m) ≪≫
      mapDerivedCategoryCompIso F E
    have hz : IsZero ((F ⋙ E).mapDerivedCategory.obj N) :=
      (F ⋙ E).isZero_mapDerivedCategory_obj N (fun q ↦
        (Functor.isZero_iff _ |>.mp (isZero_zero _) _).of_iso
          ((singletonOther O ell T n m h).app
          ((DerivedCategory.homologyFunctor (strictEtaleLevel T O ell n) q).obj N)))
    exact hz.of_iso (e.app N)

end AlgebraicGeometry
