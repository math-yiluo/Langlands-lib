/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Base change of the generic root cover

## References

* Stacks Project, Tag 01JT (fibre products of affine schemes), Tag 00PD (discrete valuation rings)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem fractionRing_away_uniformizer
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing R) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
    (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero)
  · intro x hx
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedVariables false in
/-- The explicit generic model is the pullback of the original root-cover morphism. -/
theorem root_cover_generic_pullback
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (H B : CommRingCat.{u}) [Algebra H B] (g : H)
    [(Ideal.span {g}).IsPrime] [IsLocalization.AtPrime B (Ideal.span {g})]
    [IsDomain B] [IsDiscreteValuationRing B]
    (hpi : Irreducible (algebraMap H B g))
    (ψ : Spec H ⟶ L)
    (k : Spec (CommRingCat.of (FractionRing B)) ⟶ U)
    (hk : k ≫ i = Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ)
    (hbranch : IsPullback k (𝟙 _) i
      (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H B)) ≫ ψ))
    (T : GaloisCover G (Spec (CommRingCat.of (FractionRing B))))
    (ρ : T.P ⟶ W.P) (hT : IsPullback ρ T.π W.π k) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    let a := p ≫ V.ι
    let pi := algebraMap H B g
    let A0 := AdjoinRoot
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi)
    let q0 := Spec.map (CommRingCat.ofHom (algebraMap B A0))
    let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a0 := pullback.snd (T.π ≫ j0) q0
    let γ := AdjoinRoot.map (algebraMap H B)
      ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
      ((Polynomial.X : Polynomial B) ^ Nat.card G - Polynomial.C pi) (by simp [pi])
    ∃ m : pullback (T.π ≫ j0) q0 ⟶
        pullback (W.π ≫ i) (V.ι ≫ q ≫ ψ),
      IsPullback m a0 a (Spec.map (CommRingCat.ofHom γ)) := by
  let F := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let F0 := (Polynomial.X : Polynomial B) ^ Nat.card G -
    Polynomial.C (algebraMap H B g)
  let N := Spec (CommRingCat.of (AdjoinRoot F))
  let N0 := Spec (CommRingCat.of (AdjoinRoot F0))
  let q := Spec.map (CommRingCat.ofHom (algebraMap H (AdjoinRoot F)))
  let q0 := Spec.map (CommRingCat.ofHom (algebraMap B (AdjoinRoot F0)))
  let j0 := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  let b := Spec.map (CommRingCat.ofHom (algebraMap H B))
  let β := Spec.map (CommRingCat.ofHom
    (AdjoinRoot.map (algebraMap H B) F F0 (by simp [F, F0])))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H (AdjoinRoot F) g)
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ ψ)
  let a := p ≫ V.ι
  let a0 := pullback.snd (T.π ≫ j0) q0
  let t0 := pullback.fst (T.π ≫ j0) q0
  have : IsLocalization.Away (algebraMap H B g) (FractionRing B) :=
    fractionRing_away_uniformizer B (algebraMap H B g) hpi
  have : IsOpenImmersion j0 := IsOpenImmersion.of_isLocalization (algebraMap H B g)
  have hβ : β ≫ q = q0 ≫ b := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact AdjoinRoot.map_of (algebraMap H B) F F0 (by simp [F, F0]) r
  have hpre : β ⁻¹ᵁ V = q0 ⁻¹ᵁ j0.opensRange := by
    ext x
    change _ ∉ x.asIdeal ↔ q0 x ∈ Set.range j0
    change _ ∉ x.asIdeal ↔ q0 x ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (FractionRing B)))
    rw [PrimeSpectrum.localization_away_comap_range (FractionRing B) (algebraMap H B g)]
    change AdjoinRoot.map (algebraMap H B) F F0 (by simp [F, F0])
        (AdjoinRoot.of F g) ∉ x.asIdeal ↔
      AdjoinRoot.of F0 (algebraMap H B g) ∉ x.asIdeal
    rw [AdjoinRoot.map_of]
  have ha0 : a0 ≫ q0 = t0 ≫ T.π ≫ j0 := by
    exact (pullback.condition (f := T.π ≫ j0) (g := q0)).symm
  have hfactor : Set.range (a0 ≫ β) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    change a0 x ∈ β ⁻¹ᵁ V
    rw [hpre]
    change q0 (a0 x) ∈ Set.range j0
    rw [← Hom.comp_apply, ha0, Hom.comp_apply, Hom.comp_apply]
    exact Set.mem_range_self _
  let v := IsOpenImmersion.lift V.ι (a0 ≫ β) hfactor
  have hv : v ≫ V.ι = a0 ≫ β := IsOpenImmersion.lift_fac _ _ hfactor
  let l := t0 ≫ ρ
  have hl : l ≫ (W.π ≫ i) = v ≫ (V.ι ≫ q ≫ ψ) := by
    simp only [l, Category.assoc, hT.w_assoc, hk]
    rw [← reassoc_of% ha0, ← reassoc_of% hβ, ← reassoc_of% hv]
  let m := pullback.lift l v hl
  have hm : m ≫ a = a0 ≫ β := by
    simp only [m, a, p, pullback.lift_snd_assoc, hv]
  classical
  have hex (s : PullbackCone a β) :
      ∃ d : s.pt ⟶ pullback (T.π ≫ j0) q0, d ≫ m = s.fst ∧ d ≫ a0 = s.snd := by
    have hsfactor : Set.range (s.snd ≫ q0) ⊆ Set.range j0 := by
      rintro _ ⟨x, rfl⟩
      change q0 (s.snd x) ∈ j0.opensRange
      change s.snd x ∈ q0 ⁻¹ᵁ j0.opensRange
      rw [← hpre]
      change β (s.snd x) ∈ V
      rw [← Hom.comp_apply, ← s.condition]
      exact (p (s.fst x)).property
    let r := IsOpenImmersion.lift j0 (s.snd ≫ q0) hsfactor
    have hr : r ≫ j0 = s.snd ≫ q0 := IsOpenImmersion.lift_fac _ _ hsfactor
    let l' := s.fst ≫ pullback.fst (W.π ≫ i) (V.ι ≫ q ≫ ψ)
    have hl' : l' ≫ W.π = r ≫ k := by
      have hcomm : (l' ≫ W.π) ≫ i = r ≫ (j0 ≫ b ≫ ψ) := by
        calc
          (l' ≫ W.π) ≫ i = s.fst ≫ a ≫ q ≫ ψ := by
            simpa only [l', a, p, Category.assoc] using
              congrArg (fun z ↦ s.fst ≫ z)
                (pullback.condition (f := W.π ≫ i) (g := V.ι ≫ q ≫ ψ))
          _ = s.snd ≫ β ≫ q ≫ ψ := by rw [reassoc_of% s.condition]
          _ = s.snd ≫ q0 ≫ b ≫ ψ := by rw [reassoc_of% hβ]
          _ = r ≫ (j0 ≫ b ≫ ψ) := by rw [reassoc_of% hr]
      have he := hbranch.lift_fst (l' ≫ W.π) r hcomm
      have he' : hbranch.lift (l' ≫ W.π) r hcomm = r := by
        simpa using hbranch.lift_snd (l' ≫ W.π) r hcomm
      rw [he'] at he
      exact he.symm
    let t := hT.lift l' r hl'
    have ht : t ≫ T.π = r := hT.lift_snd _ _ _
    let d := pullback.lift t s.snd (by simpa only [Category.assoc] using
      (congrArg (fun z ↦ z ≫ j0) ht).trans hr)
    have hd : d ≫ a0 = s.snd := pullback.lift_snd _ _ _
    refine ⟨d, ?_, hd⟩
    apply pullback.hom_ext
    · simp only [d, m, l, t0, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, t, hT.lift_fst]
      rfl
    · apply (cancel_mono V.ι).mp
      calc
        (d ≫ m) ≫ p ≫ V.ι = d ≫ a0 ≫ β := by
          simpa only [a, Category.assoc] using congrArg (fun z ↦ d ≫ z) hm
        _ = s.snd ≫ β := by rw [reassoc_of% hd]
        _ = s.fst ≫ p ≫ V.ι := s.condition.symm
  choose desc hfst hsnd using hex
  refine ⟨m, IsPullback.of_isLimit (c := PullbackCone.mk m a0 hm)
    (PullbackCone.IsLimit.mk hm desc hfst hsnd ?_)⟩
  intro s d hd₁ hd₂
  apply pullback.hom_ext
  · apply hT.hom_ext
    · calc
        (d ≫ t0) ≫ ρ = d ≫ m ≫ pullback.fst _ _ := by
          simp only [m, l, Category.assoc, pullback.lift_fst]
        _ = s.fst ≫ pullback.fst _ _ := by rw [reassoc_of% hd₁]
        _ = desc s ≫ m ≫ pullback.fst _ _ := by rw [reassoc_of% hfst s]
        _ = (desc s ≫ t0) ≫ ρ := by
          simp only [m, l, Category.assoc, pullback.lift_fst]
    · apply (cancel_mono j0).mp
      calc
        (d ≫ t0 ≫ T.π) ≫ j0 = d ≫ a0 ≫ q0 := by
          simpa only [Category.assoc] using
            (congrArg (fun z ↦ d ≫ z) ha0).symm
        _ = s.snd ≫ q0 := by rw [reassoc_of% hd₂]
        _ = desc s ≫ a0 ≫ q0 := by rw [reassoc_of% hsnd s]
        _ = (desc s ≫ t0 ≫ T.π) ≫ j0 := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ desc s ≫ z) ha0
  · exact hd₂.trans (hsnd s).symm

end AlgebraicGeometry.Scheme
