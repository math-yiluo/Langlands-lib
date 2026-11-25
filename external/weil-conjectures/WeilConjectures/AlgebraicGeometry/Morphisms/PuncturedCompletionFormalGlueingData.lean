/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingH0
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingPrime

/-! # Finite affine charts as module glueing data

## References

* Stacks Project, Lemma 0BLH, first two paragraphs of its proof, and Remark 05EL, the definition of
  H0
* Stacks Project, Lemma 0BLH, first two paragraphs
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine chart sections give a module glueing datum and a map from compatible
families to the explicit matching ring, preserving the completed coordinate. -/
theorem exists_formalGlueingData_matching_projection
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hgen : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (k : FormalGlueing.h0 φ f X → D.matchingRing),
      ∀ h, pullback.snd
        (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop
          (k h) = e h.val.1 := by
  dsimp
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
  let : Module C Γ(E, ⊤) := Module.compHom _ g.hom
  obtain ⟨X, e, V, hcover, r, hcompat, hmatch⟩ :=
    exists_formalGlueingData_prime hU D t f hgen
  let O := pullback q (completionSpecMap A ∣_ U)
  let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
  have hcover' : (⊤ : O.Opens) ≤ iSup (fun i ↦ p ⁻¹ᵁ V i) := by
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover (show p x ∈ ⊤ from trivial))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hglobal : ∀ h : FormalGlueing.h0 (algebraMap A C) f X,
      ∃ a : Γ(Y, ⊤), p.appTop a = D.toCompleted.appTop (e h.val.1) := by
    intro h
    obtain ⟨a, ha, _⟩ := Y.sheaf.existsUnique_gluing' V ⊤
      (fun _ ↦ homOfLE le_top) hcover (fun i ↦ r i h) (hcompat h)
    refine ⟨a, ?_⟩
    apply O.sheaf.eq_of_locally_eq' (fun i ↦ p ⁻¹ᵁ V i) ⊤
      (fun _ ↦ homOfLE le_top) hcover'
    intro i
    have hn := ConcreteCategory.congr_hom (p.naturality
      (homOfLE (le_top : V i ≤ ⊤)).op) a
    change p.app (V i) (Y.presheaf.map (homOfLE le_top).op a) =
      O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op (p.appTop a) at hn
    exact hn.symm.trans ((congrArg (fun b ↦ p.app (V i) b) (ha i)).trans (hmatch h i))
  classical
  choose a ha using hglobal
  let F := p.appTop
  let G := D.toCompleted.appTop
  let c := CommRingCat.pullbackCone F G
  let j := (CommRingCat.pullbackConeIsLimit F G).conePointUniqueUpToIso
    (pullback.isLimit F G)
  let z : FormalGlueing.h0 (algebraMap A C) f X → c.pt :=
    fun h ↦ ⟨(a h, e h.val.1), ha h⟩
  refine ⟨X, e, fun h ↦ j.hom (z h), ?_⟩
  intro h
  have hj := ConcreteCategory.congr_hom
    ((CommRingCat.pullbackConeIsLimit F G).conePointUniqueUpToIso_hom_comp
      (pullback.isLimit F G) WalkingCospan.right) (z h)
  exact hj

end AlgebraicGeometry.Scheme.CompletionGluingData
