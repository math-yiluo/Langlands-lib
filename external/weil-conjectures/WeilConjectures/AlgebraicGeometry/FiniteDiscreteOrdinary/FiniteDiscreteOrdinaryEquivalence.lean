/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite discrete coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryLocalModel_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryLocalModel A T M) : ordinaryLocalModel A T N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hC i
  exact ⟨P, hP, ⟨(upperStar _ (C.f i)).mapIso e.symm ≪≫ h⟩⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryStratified_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryStratified A T M) : ordinaryStratified A T N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ ordinaryLocalModel_of_iso A _
    ((upperStar _ (S.immersion a)).mapIso e) (hS a)⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinaryConstructible_of_iso (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) (h : ordinaryConstructible A T M) : ordinaryConstructible A T N := by
  classical
  unfold ordinaryConstructible at h ⊢
  split_ifs at h ⊢ with hT
  · exact ordinaryStratified_of_iso A T e h
  · intro U hU
    exact ordinaryStratified_of_iso A U.toScheme ((upperStar _ U.ι).mapIso e) (h U hU)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private local instance ordinaryCtf_iso (T : Scheme.{u}) :
    (ordinaryCtf A T).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1.1, ?_⟩,
      (DerivedCategory.finiteTorAmplitude _).prop_of_iso e h.2⟩
    intro n
    exact ordinaryConstructible_of_iso A T ((DerivedCategory.homologyFunctor _ n).mapIso e)
      (h.1.2 n)

section Localizing
universe w v₁ v₂
variable {C D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type v₁, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.prop_colimit (G ⋙ F) inferInstance hPG)

private theorem localizing_forward (S : ObjectProperty C) (T : ObjectProperty D)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type v₁, PreservesColimitsOfShape (Discrete I) F]
    (hST : ∀ K, S K → T (F.obj K)) {K : C} (hK : localizingClosure S K) :
    localizingClosure T (F.obj K) := by
  intro P hP hT
  exact hK (P.inverseImage F) (inverseImageLocalizing P F hP)
    (fun L hL ↦ hT _ (hST L hL))

private theorem localizing_equivalence (S : ObjectProperty C) (T : ObjectProperty D)
    [T.IsClosedUnderIsomorphisms] (e : C ≌ D)
    [e.functor.CommShift ℤ] [e.functor.IsTriangulated]
    [e.inverse.CommShift ℤ] [e.inverse.IsTriangulated]
    (hST : ∀ K, S K ↔ T (e.functor.obj K)) (K : C) :
    localizingClosure S K ↔ localizingClosure T (e.functor.obj K) := by
  constructor
  · exact localizing_forward S T e.functor (fun L ↦ (hST L).1)
  · intro hK P hP hS
    let := hP.2.1
    have hi (L : D) (hL : T L) : S (e.inverse.obj L) :=
      (hST _).2 (T.prop_of_iso (e.counitIso.app L).symm hL)
    have h := localizing_forward T S e.inverse hi hK
    exact P.prop_of_iso (e.unitIso.app K).symm (h P hP hS)
end Localizing

/-- Finite discrete condensed and ordinary coefficients agree, including the exact
section-action equivalence, its actual unbounded termwise extension, relative derived
tensor, every ordered Tor interval, finite local models, bounded constructible finite-Tor
objects, triangulated and coproduct structure, localizing closures, and the two composites
for each fixed compactification.

Source: blueprint main-20261015, chap-Construction-of-f,
theorem-f-shriek-finite-coefficients, coefficient-identification step
(blueprint: lem-sf-module-object-ordinary-coefficient-equivalence).

Proof following the twelve DAG steps:
1. The finite-discrete condensed-ring constant comparison and its scheme inverse-image
comparison give the normalized ringIso. The canonical map is sheafified constant functions
followed by constantSchemeIso and upperStarFromPoint. Zero rings and empty schemes are allowed.
2. Apply def-weil-pbc-internal-abelian-sheaf-module-equivalence and restrict scalars along
ringIso. The maps and underlying abelian sheaves are identical. Both functors are additive
and inverse equivalences preserve kernels and cokernels, hence are exact.
3. Restrict to constant scalars to identify the intrinsic module category with fixed scalar
module sheaves (lem-cbc-constant-ring-module-sheaves). Conversely local scalar sections act
by gluing constant actions. The unit and counit are identity on underlying sections.
4. Apply situation-conventions to the two additive equivalences and
inverses. Units and counits extend termwise and descend through quasi-isomorphisms. Homology,
shifts and distinguished triangles are preserved.
5. Apply lem-pe-internal-section-tensor-comparison. Its local pure-tensor comparison is the
identity. Restriction along ringIso preserves the same balancing relations and coherence.
6. The equivalences preserve coproducts by their Hom bijections. Their termwise comparisons
therefore identify direct-sum total tensors, including their signed differential. The cited
tensor comparison preserves and reflects acyclicity and K-flatness. The mapping-cone test
identifies this K-flatness with def-sfb-preserves-kflat-quasi-iso. Compute both relative derived
tensors on the same K-flat resolution to obtain the monoidal derived comparison.
7. Every module sheaf in degree zero corresponds in both directions. Tensor comparison and
homology compatibility identify all zero tests outside each specified interval. This is
exactly def-weil-proetale-tor-amplitude in intrinsic coordinates, and the generic Tor predicate
in fixed scalar coordinates. No test sheaf or interval is omitted.
8. lem-weil-pbc-finite-discrete-coefficient-sections identifies the scalar maps under every
scheme pullback. Adjoint transposition gives compatibility of ringIso with inverse image.
The balanced tensor description then identifies both module pullbacks.
9. A finite presentation over A is the cokernel of a finite scalar matrix. Both encodings
send it to the identical matrix, and sheafification preserves cokernels. Thus the same cover
trivializes the constant models. Over finite A, finite and finitely presented modules agree.
Apply this on the same constructible locally closed strata, and affine-locally on arbitrary
schemes. Homology and Tor compatibility identify the bounded constructible finite-Tor objects.
10. The derived equivalence preserves shifts, triangles, isomorphisms and small coproducts.
Transport the subcategories in the intersection defining definition-localizing-subcategory. Apply
the same argument to the inverse to obtain equality of localizing-closure membership.
11. Both direct images have sections M(V times_T U). The coefficient-sections equation
identifies their actions. For an open immersion both extensions by zero are left adjoint
to the same restriction, so adjunction uniqueness identifies them naturally.
12. Each equivalence is right adjoint to its exact inverse and hence preserves K-injectives
by lem-weil-pbc-right-adjoint-preserves-kinjective. Compute direct images on corresponding
K-injective resolutions, then compose with the termwise exact extension-by-zero comparison.
This gives exactly Rp_*D(j_!) and Rp_*j_! for the same specified compactification.
-/
theorem moduleObject_ordinary_coefficient_equivalence [Finite A] [DiscreteTopology A] :
    ∃ E : ∀ T : Scheme.{u}, Encoding A T,
      (∀ T : Scheme.{u},
        Nonempty ((E T).fixedDerived.functor.Monoidal) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔
            Scheme.HasProEtaleTorAmplitude T A ((E T).ordinaryDerived.functor.obj K) a b)) ∧
        (∀ (K : DerivedCategory (Internal A T)) (a b : ℤ), a ≤ b →
          (DerivedCategory.torAmplitudeIn _ a b K ↔ DerivedCategory.torAmplitudeIn _ a b
            ((E T).fixedDerived.functor.obj K))) ∧
        (∀ M : Internal A T,
          HasFiniteConstantLocalModel (coefficient A) T M ↔
            ordinaryLocalModel A T (((E T).ordinary.functor ⋙ (E T).fixed.functor).obj M)) ∧
        (∀ K : DerivedCategory (Internal A T),
          (constantModelBoundedConstructible (coefficient A) T K ∧
            DerivedCategory.finiteTorAmplitude _ K) ↔
              ordinaryCtf A T ((E T).fixedDerived.functor.obj K)) ∧
        Nonempty ((E T).fixedDerived.functor.CommShift ℤ) ∧
        (E T).fixedDerived.functor.IsTriangulated ∧
        PreservesColimitsOfSize.{u + 1, u + 1} (E T).fixedDerived.functor ∧
        (∀ K : DerivedCategory (Internal A T),
          localizingClosureProEtale (coefficient A) T K ↔
            CategoryTheory.localizingClosure (ordinaryCtf A T)
              ((E T).fixedDerived.functor.obj K))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f),
        Nonempty (CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
            (E Y).fixedDerived.functor ≅
          (E X).fixedDerived.functor ⋙
            rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1} A)) c)) := by
  classical
  let E : ∀ T : Scheme.{u}, Encoding A T := fun T ↦ Classical.choice (encoding_exists A T)
  refine ⟨E, ?_, encoding_compactification A E⟩
  intro T
  obtain ⟨hm, ho, ht⟩ := encoding_tensor_tor A T (E T)
  obtain ⟨hl, hb⟩ := encoding_constructibility A T (E T)
  have hf (K : DerivedCategory (Internal A T)) :
      DerivedCategory.finiteTorAmplitude _ K ↔
        DerivedCategory.finiteTorAmplitude _ ((E T).fixedDerived.functor.obj K) := by
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).1
        (h.mono (min_le_left a b) le_rfl)⟩
    · rintro ⟨a, b, h⟩
      exact ⟨min a b, b, (ht K _ _ (min_le_right a b)).2
        (h.mono (min_le_left a b) le_rfl)⟩
  have hctf (K : DerivedCategory (Internal A T)) :
      (constantModelBoundedConstructible (coefficient A) T K ∧
        DerivedCategory.finiteTorAmplitude _ K) ↔
          ordinaryCtf A T ((E T).fixedDerived.functor.obj K) :=
    and_congr (hb K) (hf K)
  let : ((E T).ordinary.trans (E T).fixed).functor.Additive :=
    inferInstanceAs ((E T).ordinary.functor ⋙ (E T).fixed.functor).Additive
  let : ((E T).ordinary.trans (E T).fixed).inverse.Additive :=
    inferInstanceAs ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).Additive
  let : (E T).fixedDerived.functor.IsTriangulated := by
    change ((E T).ordinary.functor ⋙ (E T).fixed.functor).mapDerivedCategory.IsTriangulated
    infer_instance
  let : (E T).fixedDerived.inverse.CommShift ℤ := by
    change ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).mapDerivedCategory.CommShift ℤ
    infer_instance
  let : (E T).fixedDerived.inverse.IsTriangulated := by
    change ((E T).fixed.inverse ⋙ (E T).ordinary.inverse).mapDerivedCategory.IsTriangulated
    infer_instance
  exact ⟨hm, ho, ht, hl, hctf, ⟨inferInstance⟩, inferInstance, inferInstance,
    localizing_equivalence _ _ (E T).fixedDerived hctf⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
