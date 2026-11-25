/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartCoherence

/-!
# Realizing formal glueing data on affine principal charts

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, item (1)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

private theorem empty_chart_transitions
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y E : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {s : E ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : Fin 0 → A) :
    Nonempty (AffineChartTransitions D 0 f) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : Module C Γ(E, ⊤) := completedChartModule s
  let F : FormalGlueing.Transitions (algebraMap A C) f :=
    { M' := ModuleCat.of C Γ(E, ⊤)
      M := fun i ↦ Fin.elim0 i
      alpha := fun i ↦ Fin.elim0 i
      alpha_smul := fun i ↦ Fin.elim0 i
      alpha_overlap := fun i ↦ Fin.elim0 i }
  exact ⟨{
    F := F
    e := LinearEquiv.refl C Γ(E, ⊤)
    c := fun i ↦ Fin.elim0 i
    b := fun i ↦ Fin.elim0 i
    d := fun i ↦ Fin.elim0 i
    b_left := fun i ↦ Fin.elim0 i
    b_right := fun i ↦ Fin.elim0 i
    d_prime := fun i ↦ Fin.elim0 i
    d_chart := fun i ↦ Fin.elim0 i
    b_scalar := fun i ↦ Fin.elim0 i
    d_scalar := fun i ↦ Fin.elim0 i }⟩

/-- Realize the localization and scalar-extension maps as actual restrictions on
principal affine charts. This statement concerns arbitrary chart and prime elements;
it neither constructs an H0 family nor asserts that the charts cover.
-/
theorem exists_affine_chart_realization
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    letI : Algebra A C := φ.toAlgebra
    let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
    letI : Module C Γ(E, ⊤) := Module.compHom _ g.hom
    let V := fun i ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let O := pullback q (completionSpecMap A ∣_ U)
    let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
    ∃ (X : FormalGlueing.Data.{u, u, u} φ f) (e : X.M' ≃ₗ[C] Γ(E, ⊤))
      (c : ∀ i, FormalGlueing.piece (f i) (X.M i) ≃+ Γ(Y, V i))
      (b : ∀ i j, FormalGlueing.localize (f i) (FormalGlueing.piece (f j) (X.M j)) ≃+
        Γ(Y, V i ⊓ V j))
      (d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (X.M i)) ≃+
        Γ(O, p ⁻¹ᵁ V i)),
      (∀ i j m, b i j (X.alpha_overlap i j (LocalizedModule.mk m 1)) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i m)) ∧
      (∀ i j m, b i j (LocalizedModule.mk m 1) =
        Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j m)) ∧
      (∀ i m, d i (X.alpha i (LocalizedModule.mk m 1)) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V i ≤ ⊤)).op
          (D.toCompleted.appTop (e m))) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : C) m) = p.app (V i) (c i m)) := by
  let : IsAffine E := isAffine_of_isAffineHom s
  have hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) := by
    intro i
    rw [Scheme.Hom.comp_preimage]
    have hbase : IsAffineOpen (X := Spec (.of A)) (PrimeSpectrum.basicOpen (f i)) :=
      IsAffineOpen.Spec_basicOpen (R := .of A) (f i)
    have hsub : PrimeSpectrum.basicOpen (f i) ≤ U.ι.opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact hf i
    exact (hbase.preimage_of_isOpenImmersion U.ι hsub).preimage q
  have hT : Nonempty (AffineChartTransitions D t f) := by
    cases t with
    | zero => exact empty_chart_transitions D f
    | succ t => exact exists_affine_chart_transitions D (t + 1) f hf hV
  obtain ⟨T⟩ := hT
  obtain ⟨hsquare, hcocycle⟩ := affine_chart_transition_coherence D t f hf hV T
  let X : FormalGlueing.Data (algebraMap A
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) f :=
    { M' := T.F.M'
      M := T.F.M
      alpha := T.F.alpha
      alpha_smul := T.F.alpha_smul
      alpha_overlap := T.F.alpha_overlap
      square := hsquare
      cocycle := hcocycle }
  refine ⟨X, T.e, T.c, T.b, T.d, ?_⟩
  exact ⟨T.b_left, T.b_right, T.d_prime, T.d_chart⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
