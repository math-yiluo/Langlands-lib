/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteScalarConstantModels

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

private theorem localModel_comparison [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    HasFiniteConstantLocalModel (coefficient A) T M ↔
      ordinaryLocalModel A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  refine (finiteConstantLocalModel_iff_exists_cover (coefficient A) M).trans ?_
  apply exists_congr
  intro C
  refine forall_congr' fun i ↦ ?_
  let eU := (encoding_exists A (C.X i)).some
  let h := (encoding_pullback_fixed A (C.f i) e eU M).some
  refine (finite_scalar_model_iff_constant A (C.X i) eU _).trans ?_
  constructor
  · rintro ⟨P, hP, ⟨j⟩⟩
    exact ⟨P, hP, ⟨h.symm ≪≫ j⟩⟩
  · rintro ⟨P, hP, ⟨j⟩⟩
    exact ⟨P, hP, ⟨h ≪≫ j⟩⟩

private theorem localModel_iso (A : Type u) [CommRing A] (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) : ordinaryLocalModel A T M ↔ ordinaryLocalModel A T N := by
  have transport {M N : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))} (j : M ≅ N)
      (h : ordinaryLocalModel A T M) : ordinaryLocalModel A T N := by
    obtain ⟨C, hC⟩ := h
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨h⟩⟩ := hC i
    exact ⟨P, hP, ⟨(upperStar _ (C.f i)).mapIso j.symm ≪≫ h⟩⟩
  exact ⟨transport e, transport e.symm⟩

private theorem stratified_iso (A : Type u) [CommRing A] (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) : ordinaryStratified A T M ↔ ordinaryStratified A T N := by
  apply exists_congr
  intro S
  exact forall_congr' fun a ↦ localModel_iso A _ ((upperStar _ (S.immersion a)).mapIso e)

private theorem constructible_iso (A : Type u) [CommRing A] (T : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (e : M ≅ N) : ordinaryConstructible A T M ↔ ordinaryConstructible A T N := by
  classical
  unfold ordinaryConstructible
  split_ifs with hT
  · exact stratified_iso A T e
  · exact forall_congr' fun U ↦ forall_congr' fun _ ↦
      stratified_iso A U.toScheme ((upperStar _ U.ι).mapIso e)

private theorem stratified_comparison [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    IsFiniteConstantStratified (coefficient A) T M ↔
      ordinaryStratified A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  apply exists_congr
  intro S
  refine forall_congr' fun a ↦ ?_
  let eU := (encoding_exists A (S.domain a)).some
  exact (localModel_comparison A _ eU _).trans
    (localModel_iso A _ (encoding_pullback_fixed A (S.immersion a) e eU M).some)

private theorem constructible_comparison [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    IsConstantModelConstructible (coefficient A) T M ↔
      ordinaryConstructible A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
  classical
  unfold IsConstantModelConstructible ordinaryConstructible
  split_ifs with hT
  · exact stratified_comparison A T e M
  · refine forall_congr' fun U ↦ forall_congr' fun _ ↦ ?_
    let eU := (encoding_exists A U.toScheme).some
    exact (stratified_comparison A _ eU _).trans
      (stratified_iso A _ (encoding_pullback_fixed A U.ι e eU M).some)

/-- Finite local models and bounded constructibility under coefficient encoding.
Source: blueprint coefficient-identification proof, steps 8--9; Stacks Tags 03DA and 099R.
(auxiliary; not a blueprint node).

Proof: the coefficient-sections equation identifies the canonical ring maps after every
scheme inverse image. The section-action equivalence thus commutes with these inverse
images. A finite module over the finite ring is finitely presented. Present it by a
finite scalar matrix: the encodings carry the matrix to exactly the same matrix, and
preserve its cokernel. Hence they identify the corresponding constant sheaves. Apply
these comparisons on each member of the same pro-etale covering; the inverse equivalence
gives the converse. Applying this argument to every immersion in the same finite
constructible stratification proves stratified constructibility in both directions.
On schemes that are not qcqs use the same comparison on every affine open, as required
by both definitions. Finally the termwise derived equivalence is t-exact and commutes
with every homology functor; its inverse has the same properties. This identifies both
boundedness and constructibility of every homology sheaf. -/
theorem encoding_constructibility [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) :
    (∀ M : Internal A T,
      HasFiniteConstantLocalModel (coefficient A) T M ↔
        ordinaryLocalModel A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M)) ∧
    (∀ K : DerivedCategory (Internal A T),
      constantModelBoundedConstructible (coefficient A) T K ↔
        ordinaryBoundedConstructible A T (e.fixedDerived.functor.obj K)) := by
  refine ⟨localModel_comparison A T e, fun K ↦ ?_⟩
  let F := e.ordinary.functor ⋙ e.fixed.functor
  change (DerivedCategory.TStructure.t.bounded K ∧ _) ↔
    (DerivedCategory.TStructure.t.bounded (F.mapDerivedCategory.obj K) ∧ _)
  refine and_congr
    ⟨F.bounded_mapDerivedCategory_obj, F.bounded_of_bounded_mapDerivedCategory_obj⟩ ?_
  refine forall_congr' fun n ↦ ?_
  exact (constructible_comparison A T e _).trans
    (constructible_iso A T ((F.mapDerivedCategoryHomologyFunctorIso n).app K))

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
