/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictedTensorFiniteLocalConstancySupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Constructible cohomology of finite-coefficient derived tensors

Source: Stacks Project, Pro-etale Cohomology, Tag 09BQ, lemma-tensor-c
(blueprint: lem-pur-finite-tensor-constructible-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private def finiteLocalConstancy (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) : Prop :=
  IsLocallyConstantProEtaleModuleSheaf Y A F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)

private theorem finiteLocalConstancy_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : finiteLocalConstancy Y A F) : finiteLocalConstancy Y A G := by
  constructor
  · obtain ⟨I, U, f, hf, h⟩ := hF.1
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨eM⟩⟩ := h i
    exact ⟨M, ⟨((SheafOfModules.overFunctor _ (U i)).mapIso e).symm ≪≫ eM⟩⟩
  · intro Ω _ _ y
    let O := proEtaleConstantRing Y A
    let E := (SheafOfModules.forget _).mapIso e
    let D := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
      (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso E
    let s := (PresheafOfModules.colimitFunctor
      (colimit.isColimit (proEtaleGeometricStalkRingDiagram y O))).mapIso D
    exact @Finite.of_equiv _ _ (hF.2 Ω y) s.toLinearEquiv.toEquiv

private theorem finiteLocalConstancy_comp_pullback
    {T Y X : Scheme.{u}} (a : Y ⟶ T) (b : X ⟶ Y)
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules T (proEtaleConstantRing T A))
    (hF : finiteLocalConstancy Y A (proEtaleConstantModulePullback a A F)) :
    finiteLocalConstancy X A (proEtaleConstantModulePullback (b ≫ a) A F) := by
  obtain ⟨e⟩ := proEtaleConstantModulePullback_comp a b A
  exact finiteLocalConstancy_iso X A (e.app F).symm
    (proEtale_finiteLocalConstancy_pullback b A (proEtaleConstantModulePullback a A F) hF)

private theorem common_stratification {I : Type*} (s : Finset I)
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : I → proEtaleRingModules T (proEtaleConstantRing T A))
    (hF : ∀ k ∈ s, IsConstructibleProEtaleModuleSheaf T A (F k)) :
    ∃ S : Stratification T, 0 < S.n ∧
      ∀ k ∈ s, ∀ j : Fin S.n, finiteLocalConstancy (S.domain j) A
        (proEtaleConstantModulePullback (S.immersion j) A (F k)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let S : Stratification T :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
        iUnion_stratum_eq_univ := Set.iUnion_const Set.univ
        pairwise_disjoint_stratum := by intro i j h; exact (h (Subsingleton.elim i j)).elim
        domain := fun _ ↦ T
        immersion := fun _ ↦ 𝟙 T
        range_immersion := by intro i; simp }
    exact ⟨S, Nat.zero_lt_one, by simp⟩
  | @insert k s hk ih =>
    obtain ⟨S, hSn, hS⟩ := ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))
    obtain ⟨R, hRn, hR⟩ := hF k (Finset.mem_insert_self k s)
    refine ⟨S.inter R, Nat.mul_pos hSn hRn, ?_⟩
    intro j hj a
    rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      change finiteLocalConstancy _ A (proEtaleConstantModulePullback
        (pullback.fst _ _ ≫ S.immersion _) A (F k))
      rw [pullback.condition]
      exact finiteLocalConstancy_comp_pullback (R.immersion _)
        (pullback.snd _ _) A (F k) (hR _)
    · exact finiteLocalConstancy_comp_pullback (S.immersion _)
        (pullback.fst _ _) A (F j) (hS j hj _)

/-- Every cohomology sheaf of the derived tensor of bounded constructible
finite-torsion inputs is constructible. The tensor is computed on arbitrary
representatives by the recorded K-flat resolution; no lower bound is asserted.

Source: Stacks Project, Pro-etale Cohomology, Tag 09BQ, lemma-tensor-c
(blueprint: lem-pur-finite-tensor-constructible-cohomology).

Proof:
1. Use the proved finite coefficient-ring instance. A finite ring is Noetherian,
and finitely generated modules over it are finite.
2. The nonzero input cohomology sheaves form finite lists. Inductively intersect
chosen constructible stratifications. Their domains are actual fiber products;
pullback along the two projections transports the given finite local constancy.
The proved canonical composition comparison identifies the iterated restrictions;
local constancy and finite module stalks are transported along its isomorphism.
Retain the single whole-scheme stratum for the empty list, even on the empty scheme.
3. Finite cohomological support supplies upper bounds. The canonical inverse-image
map of coefficient rings is invertible, by uniqueness of the constant-sheaf
adjunction with global sections. Restriction is therefore exact, preserving the
upper bounds and commuting with cohomology.
4. The restricted finite-local-constancy tensor lemma applies on every stratum.
It combines exact restriction, derived tensor comparison, and Tag 094H over the
finite Noetherian coefficient ring; it asserts no lower bound on the output.
5. This partition and its finite locally constant restricted output cohomology
are precisely a witness for constructibility in each degree.
-/
theorem finiteTensor_constructible_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K L P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (hK : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj K))
    (hL : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj L))
    (i : ℤ) :
    @IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)
      ((DerivedCategory.homologyFunctor (proEtaleRingModules T
        (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
          (derivedTensor T (Padic.coefficientExtensionRing l E n) K L P f hf hP)) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let H := fun (M : CochainComplex (proEtaleRingModules T
    (proEtaleConstantRing T A)) ℤ) (j : ℤ) ↦
      (DerivedCategory.homologyFunctor (proEtaleRingModules T
        (proEtaleConstantRing T A)) j).obj (DerivedCategory.Q.obj M)
  change Set.Finite {j : ℤ | ¬ IsZero (H K j)} ∧
    (∀ j, IsConstructibleProEtaleModuleSheaf T A (H K j)) at hK
  change Set.Finite {j : ℤ | ¬ IsZero (H L j)} ∧
    (∀ j, IsConstructibleProEtaleModuleSheaf T A (H L j)) at hL
  let s := hK.1.toFinset.disjSum hL.1.toFinset
  let F : ℤ ⊕ ℤ → proEtaleRingModules T (proEtaleConstantRing T A) :=
    Sum.elim (H K) (H L)
  obtain ⟨S, hSn, hS⟩ := common_stratification s T A F (by
    intro j hj
    cases j with
    | inl j => exact hK.2 j
    | inr j => exact hL.2 j)
  have bounded (M : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T A)) ℤ) (h : Set.Finite {j : ℤ | ¬ IsZero (H M j)}) :
      ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (H M j) := by
    obtain ⟨b, hb⟩ := h.bddAbove
    refine ⟨b, fun j hj ↦ ?_⟩
    by_contra hz
    exact (not_le_of_gt hj) (hb hz)
  refine ⟨S, hSn, fun a ↦ ?_⟩
  apply proEtale_restrictedTensor_finiteLocalConstancy (S.immersion a) A K L P f hf hP
    (proEtaleConstantModulePullback_boundedAbove (S.immersion a) A K (bounded K hK.1))
    (proEtaleConstantModulePullback_boundedAbove (S.immersion a) A L (bounded L hL.1)) _ _ i
  · intro j hj
    apply hS (Sum.inl j) _ a
    exact Finset.mem_disjSum.mpr (Or.inl ⟨j, hK.1.mem_toFinset.mpr hj, rfl⟩)
  · intro j hj
    apply hS (Sum.inr j) _ a
    exact Finset.mem_disjSum.mpr (Or.inr ⟨j, hL.1.mem_toFinset.mpr hj, rfl⟩)

end AlgebraicGeometry.Scheme
