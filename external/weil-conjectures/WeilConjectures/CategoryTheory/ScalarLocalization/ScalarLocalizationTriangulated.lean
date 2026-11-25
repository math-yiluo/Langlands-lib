/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Triangulation of scalar localization

Source: Stacks Project, Derived Categories, Tags 05R2 and 05R6, applied to the scalar
localization in the blueprint `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-triangulated).
-/

@[expose] public section

universe r u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory
namespace ScalarLocalization

private theorem all_shift_linear
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasShift C ℤ]
    [(shiftFunctor C (1 : ℤ)).Linear R] (n : ℤ) :
    (shiftFunctor C n).Linear R := by
  have hn : (shiftFunctor C (-1 : ℤ)).Linear R :=
    by
      have : (shiftEquiv C (1 : ℤ)).functor.Linear R := ‹_›
      exact Equivalence.inverseLinear R (shiftEquiv C (1 : ℤ))
  induction n using Int.induction_on with
  | zero => exact Functor.linear_of_iso R (shiftFunctorZero C ℤ).symm
  | @succ n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (n : ℤ) 1).symm
  | @pred n ih =>
    have := ih
    exact Functor.linear_of_iso R (shiftFunctorAdd C (-(n : ℤ)) (-1)).symm

private noncomputable def rationalComparison
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

set_option linter.unusedVariables false in
/-- Scalar localization with its induced shift and image triangles is triangulated, and
localization is exact. Source: Stacks Project, Tags 05R2 and 05R6; blueprint rationalization
of `def-weil-rationalization-karoubi`
(blueprint: lem-weil-linear-scalar-localization-triangulated).

Proof plan:
1. Use `lem-weil-linear-scalar-localization-category` for composition, Q, and the induced
shift. The zero object and biproduct diagrams survive. By
`lem-weil-pbc-localization-module-tensor` and `def-weil-pbc-module-localization-away`,
morphisms are fractions f/p^n, with equality after multiplying by a further power of p.
2. Let S consist of arrows inverted by Q. An inverse fraction can be cleared to give
h s = p^N id and s h = p^N id in C. Identity/composition closure, saturation, and shift
invariance follow, giving MS1, MS4, MS5 of `def-pur-saturated-triangulated-localization`.
3. The cleared inverse gives both Ore squares: use p^N id as the new denominator.
For cancellation, Q(f) = Q(g) means p^k(f-g) = 0, giving both equalizing denominators.
This proves MS2 and MS3.
4. Apply `lem-weil-pbc-hom-into-triangle-exact` to triangles and their rotations. Localize
the resulting five-term R-linear exact Hom rows. If b(y)/p^n = 0, then b(p^k y) = 0
for some k; lift p^k y along the preceding map to prove exactness after localization.
5. Complete a square of distinguished triangles by TR3. Four vertical Hom maps are
invertible, so `lem-weil-pbc-five-lemma` in the abelian category of additive groups
(`def-sp-abelian`) makes the middle Hom map invertible. Testing all sources proves the
third triangle map is inverted by Q, establishing MS6.
6. Verify Q's localization universal property for arbitrary functors F inverting S:
send f/p^n to F(f) F(p id)^(-n). Scalar naturality gives well-definedness and composition;
the same identity extends natural transformations uniquely. No additivity of F is needed.
7. Apply `lem-pur-localization-triangles-05r6`. Its shift agrees with the tensor-induced
shift, its distinguished triangles are exactly the isomorphic Q-images, and it supplies
TR4 and exactness of Q. There is no idempotent completion.

The existential instances supply structures on the fixed raw scalar category. The equality
of shift functors specifies the induced shift on objects and tensor morphisms. The HEq
normalization specifies the canonical identity comparison with Q, rather than a twisted
shift comparison. Only the shift by one is assumed R-linear. -/
theorem exists_triangulated_scalarLocalization
    (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [(shiftFunctor C (1 : ℤ)).Linear R] (p : R) :
    ∃ z : HasZeroObject (ScalarLocalization R C p),
      (fun [zeroInst : HasZeroObject (ScalarLocalization R C p)] ↦
        ∃ s : HasShift (ScalarLocalization R C p) ℤ,
          (fun [shiftInst : HasShift (ScalarLocalization R C p) ℤ] ↦
            shiftFunctor (ScalarLocalization R C p) (1 : ℤ) =
                map R C p (shiftFunctor C (1 : ℤ)) ∧
            ∃ a : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive,
              (fun [addInst : ∀ n : ℤ,
                  (shiftFunctor (ScalarLocalization R C p) n).Additive] ↦
                ∃ q : (localization R C p).CommShift ℤ,
                  (fun [commInst : (localization R C p).CommShift ℤ] ↦
                    (∀ X : C,
                      HEq (((localization R C p).commShiftIso (1 : ℤ)).hom.app X)
                        (𝟙 ((localization R C p).obj ((shiftFunctor C (1 : ℤ)).obj X)))) ∧
                    ∃ t : Pretriangulated (ScalarLocalization R C p),
                      (fun [triInst : Pretriangulated (ScalarLocalization R C p)] ↦
                        IsTriangulated (ScalarLocalization R C p) ∧
                        (localization R C p).IsTriangulated ∧
                        ∀ T : Triangle (ScalarLocalization R C p),
                          T ∈ distTriang (ScalarLocalization R C p) ↔
                            ∃ T' : Triangle C, T' ∈ distTriang C ∧
                              Nonempty (T ≅ (localization R C p).mapTriangle.obj T'))
                        (triInst := t)) (commInst := q)) (addInst := a)) (shiftInst := s))
        (zeroInst := z) := by
  classical
  have : ∀ n : ℤ, (shiftFunctor C n).Linear R := all_shift_linear R C
  let M := Submonoid.powers p
  let E := rationalComparison R C p
  have : E.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : E.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : E.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : E.IsEquivalence := {}
  let Q := localization R C p
  have fac : Q ⋙ E ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, E, localization, rationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  have : Q.IsLocalization (Rationalization.W M C) :=
    Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
      (Rationalization.W M C) Q E.asEquivalence.symm
      (Functor.isoWhiskerRight fac.symm E.inv ≪≫ (Functor.associator _ _ _) ≪≫
        Functor.isoWhiskerLeft Q E.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)
  let z : HasZeroObject (ScalarLocalization R C p) := Q.hasZeroObject_of_additive
  refine ⟨z, ?_⟩
  have : ((Functor.whiskeringLeft C (ScalarLocalization R C p)
      (ScalarLocalization R C p)).obj Q).Full :=
    Localization.full_whiskeringLeft Q (Rationalization.W M C) _
  have : ((Functor.whiskeringLeft C (ScalarLocalization R C p)
      (ScalarLocalization R C p)).obj Q).Faithful :=
    Localization.faithful_whiskeringLeft Q (Rationalization.W M C) _
  let s' : ℤ → ScalarLocalization R C p ⥤ ScalarLocalization R C p :=
    fun n ↦ map R C p (shiftFunctor C n)
  let i : ∀ n : ℤ, Q ⋙ s' n ≅ shiftFunctor C n ⋙ Q :=
    fun n ↦ NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, s', localization, map, mapHom]
      simp)
  let s : HasShift (ScalarLocalization R C p) ℤ := HasShift.induced Q ℤ s' i
  refine ⟨s, ?_⟩
  refine ⟨rfl, ?_⟩
  let a : ∀ n : ℤ, (shiftFunctor (ScalarLocalization R C p) n).Additive :=
    fun n ↦ inferInstanceAs ((map R C p (shiftFunctor C n)).Additive)
  refine ⟨a, ?_⟩
  let q : Q.CommShift ℤ := Functor.CommShift.ofInduced Q ℤ s' i
  refine ⟨q, ?_⟩
  refine ⟨fun X ↦ HEq.rfl, ?_⟩
  let t := Triangulated.Localization.pretriangulated Q (Rationalization.W M C)
  refine ⟨t, ?_⟩
  have : Q.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor Q (Rationalization.W M C)
  refine ⟨Triangulated.Localization.isTriangulated Q (Rationalization.W M C),
    inferInstance, ?_⟩
  intro T
  change (∃ T', ∃ _ : T ≅ Q.mapTriangle.obj T', T' ∈ distTriang C) ↔ _
  constructor
  · rintro ⟨T', e, hT'⟩
    exact ⟨T', hT', ⟨e⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    exact ⟨T', e, hT'⟩

end ScalarLocalization
end CategoryTheory
