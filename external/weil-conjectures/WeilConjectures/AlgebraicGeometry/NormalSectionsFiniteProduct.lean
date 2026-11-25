/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Sections on a quasi-compact open of a locally Noetherian normal scheme

Source: Stacks Project, Tags 0357 and 0358.
(blueprint: lem-sbc-normal-sections-finite-product)
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme

private theorem normal_stalks_open {X : Scheme.{u}}
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) :
    ∀ x : U.toScheme, IsDomain (U.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (U.toScheme.presheaf.stalk x) := by
  intro x
  obtain ⟨hd, hi⟩ := hX (U.ι x)
  let : IsDomain (X.presheaf.stalk (U.ι x)) := hd
  let : IsIntegrallyClosed (X.presheaf.stalk (U.ι x)) := hi
  let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv e⟩

private theorem sections_product {X : Scheme.{u}} {ι : Type v}
    (V : ι → X.Opens) (hd : Pairwise (fun i j ↦ Disjoint (V i) (V j))) (hc : (⨆ i, V i) = ⊤) :
    Nonempty (Γ(X, ⊤) ≃+* ∀ i, Γ(X, V i)) := by
  classical
  let g : Γ(X, ⊤) →+* ∀ i, Γ(X, V i) :=
    RingHom.pi fun i ↦ (X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op).hom
  have hcompat (sf : ∀ i, Γ(X, V i)) :
      TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hb : V i ⊓ V j = ⊥ := (hd hij).eq_bot
      have ht := X.sheaf.isTerminalOfEqEmpty hb
      let : Subsingleton Γ(X, V i ⊓ V j) := CommRingCat.subsingleton_of_isTerminal ht
      exact Subsingleton.elim _ _
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      apply X.sheaf.eq_of_locally_eq' V ⊤ (fun i ↦ homOfLE le_top) (by rw [hc])
      intro i
      exact congrFun hab i
    · intro sf
      obtain ⟨a, ha, -⟩ := X.sheaf.existsUnique_gluing' V ⊤
        (fun i ↦ homOfLE le_top) (by rw [hc]) sf (hcompat sf)
      exact ⟨a, funext ha⟩
  exact ⟨RingEquiv.ofBijective g hg⟩

/-- Sections on a quasi-compact open of a locally Noetherian normal scheme form a
finite product of integrally closed domains.

Source: Stacks Project, Tags 0357 and 0358, and Tag 035L, first paragraph of its proof.
(blueprint: lem-sbc-normal-sections-finite-product)

Proof: The open subscheme U is locally Noetherian, so it is locally connected. Its
connected components are clopen. Quasi-compactness implies that their discrete quotient
space is finite; index it by Fin n. Normality passes to each component through its open
immersion. The theorem irreducibleSpace_of_isDomain_stalk makes each connected component
irreducible. Domain stalks imply reducedness, so each component is integral. Its ring of
global sections is then a domain, and isIntegrallyClosed_of_isIntegrallyClosed_stalk
makes it integrally closed. Restriction to the disjoint open covering is injective by
uniqueness in the sheaf axiom. Every family of sections is compatible, since different
components have empty intersection; existence of gluing makes restriction surjective.
The resulting ring equivalence gives the asserted finite product. If U is empty,
n = 0 and both its section ring and the empty product are the zero ring. -/
theorem normal_sections_finite_product {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ (n : ℕ) (B : Fin n → CommRingCat.{u}),
      (∀ i, IsDomain (B i) ∧ IsIntegrallyClosed (B i)) ∧
      Nonempty (Γ(X, U) ≃+* ∀ i, B i) := by
  classical
  let S := U.toScheme
  have hS := normal_stalks_open hX U
  let : CompactSpace S := isCompact_iff_compactSpace.mp hU
  let I := ConnectedComponents S
  let := Fintype.ofFinite I
  let n := Fintype.card I
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let V (i : Fin n) : S.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {e i},
      (isOpen_discrete {e i}).preimage ConnectedComponents.continuous_coe⟩
  have hvconn (i : Fin n) : _root_.IsConnected (V i : Set S) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e i)
    change _root_.IsConnected (ConnectedComponents.mk ⁻¹' {e i})
    rw [← hx, connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  have hvnormal (i : Fin n) := normal_stalks_open hS (V i)
  have hvirr (i : Fin n) : IsIntegral (V i).toScheme := by
    let : ConnectedSpace (V i).toScheme := isConnected_iff_connectedSpace.mp (hvconn i)
    let : IrreducibleSpace (V i).toScheme :=
      irreducibleSpace_of_isDomain_stalk _ (fun x ↦ (hvnormal i x).1)
    let (x : (V i).toScheme) : IsDomain ((V i).toScheme.presheaf.stalk x) :=
      (hvnormal i x).1
    let : IsReduced (V i).toScheme := isReduced_of_isReduced_stalk _
    exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  let (i : Fin n) : IsIntegral (V i).toScheme := hvirr i
  let B (i : Fin n) := Γ(S, V i)
  have hB (i : Fin n) : IsDomain (B i) ∧ IsIntegrallyClosed (B i) := by
    let ei := (V i).topIso.commRingCatIsoToRingEquiv
    let : Nonempty (⊤ : (V i).toScheme.Opens) :=
      ⟨⟨Classical.arbitrary _, trivial⟩⟩
    have : IsIntegrallyClosed Γ((V i).toScheme, ⊤) :=
      isIntegrallyClosed_of_isIntegrallyClosed_stalk (fun x ↦ (hvnormal i x).2) ⊤
    exact ⟨ei.symm.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv ei⟩
  have hd : Pairwise (fun i j ↦ Disjoint (V i) (V j)) := by
    intro i j hij
    rw [disjoint_iff_inf_le]
    intro x hx
    exact hij (e.injective ((Set.mem_singleton_iff.mp hx.1).symm.trans
      (Set.mem_singleton_iff.mp hx.2)))
  have hc : (⨆ i, V i) = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨e.symm (ConnectedComponents.mk x), by simp [V]⟩
  obtain ⟨ep⟩ := sections_product V hd hc
  exact ⟨n, B, hB, ⟨U.topIso.commRingCatIsoToRingEquiv.symm.trans ep⟩⟩

end AlgebraicGeometry.Scheme
