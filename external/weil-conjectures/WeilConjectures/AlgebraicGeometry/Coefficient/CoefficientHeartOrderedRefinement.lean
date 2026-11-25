/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.Topology.Irreducible

/-!
# Connected ordered common refinements

Source: blueprint common-stratification clause (1), with its Noetherian-induction proof.
(blueprint: new-det-lem-coefficient-heart-common-stratification-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

open Set TopologicalSpace in
private theorem exists_irreducible_open_piece
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [Nonempty X]
    {A : Type v} [Finite A] (P : A → Set X)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = univ) :
    ∃ U : Set X, IsOpen U ∧ IsIrreducible U ∧ ∃ a, U ⊆ P a := by
  classical
  let x : X := Classical.choice inferInstance
  let Z := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨O, hO, hOne, hOZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  let S : Finset (Set X) := (Set.finite_range fun a ↦ closure (P a)).toFinset
  have hcover : Z ⊆ ⋃₀ (S : Set (Set X)) := by
    intro y hy
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hc ▸ mem_univ y)
    exact mem_sUnion.mpr ⟨closure (P a), by simp [S], subset_closure ha⟩
  obtain ⟨D, hDS, hZD⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 S
    (by
      intro D hD
      obtain ⟨a, rfl⟩ : ∃ a, closure (P a) = D := by simpa [S] using hD
      exact isClosed_closure) hcover
  obtain ⟨a, ha⟩ : ∃ a, closure (P a) = D := by simpa [S] using hDS
  rw [← ha] at hZD
  obtain ⟨V, C, hV, hC, heq⟩ := hl a
  have hZC : Z ⊆ C := (hZD.trans (closure_minimal (heq ▸ inter_subset_right) hC))
  have hmeet : (O ∩ P a).Nonempty := by
    obtain ⟨y, hy⟩ := hOne
    exact (mem_closure_iff.mp (hZD (hOZ hy))) O hO hy
  have hne : (O ∩ V).Nonempty := by
    obtain ⟨y, hyO, hyP⟩ := hmeet
    exact ⟨y, hyO, (heq ▸ hyP).1⟩
  refine ⟨O ∩ V, hO.inter hV,
    hZ.1.2.subset_irreducible hne (hO.inter hV) Set.Subset.rfl
      (fun x hx ↦ hOZ hx.1), a, ?_⟩
  · intro y hy
    rw [heq]
    exact ⟨hy.2, hZC (hOZ hy.1)⟩

open Set TopologicalSpace in
private theorem exists_ordered_irreducible_refinement
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] (S : Closeds T) :
    ∀ {A : Type v} [Finite A] (P : A → Set T),
      (∀ a, IsLocallyClosed (P a)) → (⋃ a, P a) = (S : Set T) →
      ∃ (n : ℕ) (Q : Fin n → Set T),
        (∀ b, IsIrreducible (Q b)) ∧ (∀ b, IsLocallyClosed (Q b)) ∧
        (⋃ b, Q b) = (S : Set T) ∧ Pairwise (fun b c ↦ Disjoint (Q b) (Q c)) ∧
        (∀ b, ∃ a, Q b ⊆ P a) ∧
        (∀ k : ℕ, IsClosed ((S : Set T) \ ⋃ b, ⋃ (_ : b.val < k), Q b)) := by
  classical
  apply (wellFounded_lt (α := Closeds T)).induction S
  intro S ih A _ P hl hc
  by_cases hS : (S : Set T) = ∅
  · refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b; exact Fin.elim0 b
    · intro b; exact Fin.elim0 b
    · simpa using hS.symm
    · intro b; exact Fin.elim0 b
    · intro b; exact Fin.elim0 b
    · intro k; simpa using S.isClosed
  have : Nonempty (S : Set T) := (Set.nonempty_iff_ne_empty.mpr hS).to_subtype
  have : NoetherianSpace (S : Set T) :=
    (noetherianSpace_set_iff _).mpr (fun t _ ↦ NoetherianSpace.isCompact t)
  obtain ⟨W, hW, hWirr, a, hWa⟩ := exists_irreducible_open_piece
    (fun a ↦ (Subtype.val : S → T) ⁻¹' P a)
    (fun a ↦ (hl a).preimage continuous_subtype_val) (by
      ext x
      simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
      exact mem_iUnion.mp (hc.symm ▸ x.property))
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp hW
  let U : Set T := V ∩ (S : Set T)
  have hUeq : (Subtype.val : S → T) '' W = U := by
    rw [← hVW, image_preimage_eq_inter_range, Subtype.range_coe]
  have hUirr : IsIrreducible U :=
    hUeq ▸ hWirr.image Subtype.val continuous_subtype_val.continuousOn
  have hUa : U ⊆ P a := by
    intro x hx
    exact hWa ((congrArg (fun B ↦ (⟨x, hx.2⟩ : S) ∈ B) hVW).mp hx.1)
  have hUl : IsLocallyClosed U := ⟨V, S, hV, S.isClosed, rfl⟩
  let C : Closeds T := ⟨(S : Set T) ∩ Vᶜ, S.isClosed.inter hV.isClosed_compl⟩
  have hCS : C < S := by
    refine lt_iff_le_not_ge.mpr ⟨inter_subset_left, ?_⟩
    intro h
    obtain ⟨x, hxV, hxS⟩ := hUirr.nonempty
    exact (h hxS).2 hxV
  let P' : A → Set T := fun a ↦ P a ∩ (C : Set T)
  have hP'c : (⋃ a, P' a) = (C : Set T) := by
    rw [← iUnion_inter, hc]
    exact inter_eq_right.mpr (show (C : Set T) ⊆ S from inter_subset_left)
  obtain ⟨n, Q, hQi, hQl, hQc, hQd, hQr, hQtail⟩ :=
    ih C hCS P' (fun a ↦ (hl a).inter C.isClosed.isLocallyClosed) hP'c
  have hQsub (b : Fin n) : Q b ⊆ (C : Set T) := by
    intro x hx
    rw [← hQc]
    exact mem_iUnion.mpr ⟨b, hx⟩
  have hUQ (b : Fin n) : Disjoint U (Q b) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (hQsub b hy).2 hx.1
  let Q' : Fin (n + 1) → Set T := Fin.cases U Q
  refine ⟨n + 1, Q', Fin.cases hUirr hQi, Fin.cases hUl hQl, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      cases b using Fin.cases with
      | zero => exact hb.2
      | succ b => exact (hQsub b hb).1
    · intro hx
      by_cases hxV : x ∈ V
      · exact mem_iUnion.mpr ⟨0, hxV, hx⟩
      · obtain ⟨b, hb⟩ := mem_iUnion.mp
          (hQc ▸ (show x ∈ (C : Set T) from ⟨hx, hxV⟩))
        exact mem_iUnion.mpr ⟨b.succ, hb⟩
  · intro b c hbc
    cases b using Fin.cases with
    | zero =>
      cases c using Fin.cases with
      | zero => exact (hbc rfl).elim
      | succ c => exact hUQ c
    | succ b =>
      cases c using Fin.cases with
      | zero => exact (hUQ b).symm
      | succ c => exact hQd (fun h ↦ hbc (congrArg Fin.succ h))
  · intro b
    cases b using Fin.cases with
    | zero => exact ⟨a, hUa⟩
    | succ b =>
      obtain ⟨a, ha⟩ := hQr b
      exact ⟨a, fun x hx ↦ (ha hx).1⟩
  · intro k
    cases k with
    | zero => simpa using S.isClosed
    | succ k =>
      convert hQtail k using 1
      ext x
      simp only [mem_sdiff, mem_iUnion, not_exists, Q', Fin.exists_fin_succ,
        Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ,
        Nat.zero_lt_succ, exists_prop, Nat.succ_lt_succ_iff, true_and, not_or,
        not_and, U, C, mem_inter_iff]
      aesop

private theorem exists_locallyClosed_immersion (X : Scheme.{u}) (s : Set X)
    (hs : IsLocallyClosed s) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsImmersion f ∧ Set.range f = s := by
  classical
  let U : X.Opens := ⟨coborder s, hs.isOpen_coborder⟩
  let Z : TopologicalSpace.Closeds U.toScheme :=
    ⟨Subtype.val ⁻¹' s, isClosed_preimage_val_coborder⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι ≫ U.ι, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, I.range_subschemeι]
  change Subtype.val '' (Subtype.val ⁻¹' s) = s
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
  exact Set.inter_eq_left.mpr subset_coborder

/-- A finite family of locally closed scheme stratifications has a connected ordered
common refinement. Source: blueprint common-stratification clause (1); Stacks Project,
Topology, Tags 09Y5 and 0052.
(blueprint: new-det-lem-coefficient-heart-common-stratification-refinement).

Proof: intersect the input partitions, using tuples of indices. The empty product gives
X for zero inputs. Induct on closed subsets of the Noetherian space, uniformly for any
finite locally closed cover. On a nonempty closed subset, choose an irreducible component
and a nonempty relative open contained in it. Irreducibility places that component in
one of the finitely many closures of covering parts. Intersect the chosen open with the
open part of this locally closed covering part. This gives a nonempty irreducible open
contained in that part. Induct on its proper closed complement and prepend the chosen
open to the resulting list. Complements of prefixes are closed tails from induction,
so prefixes are open; distinct pieces are disjoint. The empty subset has no strata.
Realize each locally closed piece as the vanishing-ideal closed subscheme of its open
coborder. The composite inclusion is an immersion with the prescribed range. Its
embedding identifies its domain with that irreducible piece, giving connectedness.
No factorization through an input scheme stratum is inferred from image containment.
-/
theorem coefficientHeart_commonStratification_refinement
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X] :
    ∀ (n : ℕ) (P : Fin n → X.FiniteLocallyClosedStratification),
      ∃ R : X.FiniteLocallyClosedStratification,
        (∀ (j : Fin n) (a : Fin R.n), ∃ b : Fin (P j).n,
          R.stratum a ⊆ (P j).stratum b) ∧
        (∀ a : Fin R.n, ConnectedSpace (R.domain a)) ∧
        ∀ k : Fin (R.n + 1),
          IsOpen (⋃ a : Fin R.n, ⋃ (_ : a.val < k.val), R.stratum a) := by
  classical
  intro n P
  let A := (j : Fin n) → Fin (P j).n
  let B : A → Set X := fun b ↦ ⋂ j, (P j).stratum (b j)
  have hBl : ∀ b, IsLocallyClosed (B b) := by
    intro b
    choose O Z hO hZ he using fun j ↦ (P j).isLocallyClosed_stratum (b j)
    exact ⟨⋂ j, O j, ⋂ j, Z j, isOpen_iInter_of_finite hO, isClosed_iInter hZ,
      by simp only [B, he, Set.iInter_inter_distrib]⟩
  have hBc : (⋃ b, B b) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx (j : Fin n) : ∃ b, x ∈ (P j).stratum b :=
      Set.mem_iUnion.mp ((P j).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
    choose b hb using hx
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iInter.mpr hb⟩
  obtain ⟨m, Q, hQi, hQl, hQc, hQd, hQr, hQtail⟩ :=
    exists_ordered_irreducible_refinement (⊤ : TopologicalSpace.Closeds X) B hBl hBc
  choose D f hf hr using fun a ↦ exists_locallyClosed_immersion X (Q a) (hQl a)
  let R : X.FiniteLocallyClosedStratification := {
    n := m
    stratum := Q
    isLocallyClosed_stratum := hQl
    iUnion_stratum_eq_univ := hQc
    pairwise_disjoint_stratum := hQd
    domain := D
    immersion := f
    isImmersion := hf
    range_immersion := hr }
  refine ⟨R, ?_, ?_, ?_⟩
  · intro j a
    obtain ⟨b, hb⟩ := hQr a
    exact ⟨b j, fun x hx ↦ Set.mem_iInter.mp (hb hx) j⟩
  · intro a
    have : IsImmersion (f a) := hf a
    have : IrreducibleSpace (Set.range (f a)) :=
      Subtype.irreducibleSpace ((hr a).symm ▸ hQi a)
    have : IrreducibleSpace (D a) :=
      (f a).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance
    exact inferInstance
  · intro k
    have ht : IsClosed ((⋃ a : Fin m, ⋃ (_ : a.val < k.val), Q a)ᶜ) := by
      simpa only [TopologicalSpace.Closeds.coe_top, ← Set.compl_eq_univ_sdiff] using hQtail k.val
    simpa only [compl_compl] using ht.isOpen_compl

end AlgebraicGeometry.ProEtale
