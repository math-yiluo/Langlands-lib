/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing

/-!
# Extending finite étale schemes over finitely many closed points

Let `S` be a finite set of closed points of a scheme `X` and `U = X \ S`. A finite étale
`U`-scheme which extends over `U ∪ {z} = X \ (S \ {z})` for every `z ∈ S` extends over `X`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_iso_of_forall_mem`): the extensions are
glued one point at a time, the opens `X \ (S \ T)` and `X \ (S \ {z})` meeting in `U` for
`z ∉ T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X : Scheme.{u}} [DecidableEq X] (S : Finset X) (hS : ∀ z ∈ S, IsClosed ({z} : Set X))

include hS in
/-- The open complement `X \ (S \ T)` of the points of `S` outside `T`. -/
def complOpens (T : Finset X) : X.Opens :=
  ⟨(↑(S \ T) : Set X)ᶜ, by
    have : (↑(S \ T) : Set X) = ⋃ z ∈ (↑(S \ T) : Set X), {z} :=
      (Set.biUnion_of_singleton _).symm
    have hc : IsClosed (↑(S \ T) : Set X) := by
      rw [this]
      exact (S \ T).finite_toSet.isClosed_biUnion fun z hz ↦ hS z (Finset.mem_sdiff.1 hz).1
    exact hc.isOpen_compl⟩

lemma mem_complOpens {T : Finset X} {x : X} :
    x ∈ complOpens S hS T ↔ x ∉ S ∨ x ∈ T := by
  change x ∉ (↑(S \ T) : Set X) ↔ _
  rw [Finset.mem_coe, Finset.mem_sdiff]
  tauto

lemma complOpens_mono {T T' : Finset X} (h : T ⊆ T') : complOpens S hS T ≤ complOpens S hS T' :=
  fun x hx ↦ by
    rw [mem_complOpens] at hx ⊢
    exact hx.imp_right fun hx ↦ h hx

lemma complOpens_inf {T : Finset X} {z : X} (hz : z ∉ T) :
    complOpens S hS T ⊓ complOpens S hS {z} = complOpens S hS ∅ := by
  ext x
  change x ∈ complOpens S hS T ∧ x ∈ complOpens S hS {z} ↔ x ∈ complOpens S hS ∅
  rw [mem_complOpens, mem_complOpens, mem_complOpens, Finset.mem_singleton]
  constructor
  · rintro ⟨h₁ | h₁, h₂ | rfl⟩
    exacts [Or.inl h₁, Or.inl h₁, Or.inl h₂, absurd h₁ hz]
  · rintro (h | h)
    · exact ⟨Or.inl h, Or.inl h⟩
    · exact absurd h (Finset.notMem_empty x)

lemma complOpens_sup {T : Finset X} {z : X} :
    complOpens S hS T ⊔ complOpens S hS {z} = complOpens S hS (insert z T) := by
  ext x
  change x ∈ complOpens S hS T ∨ x ∈ complOpens S hS {z} ↔ x ∈ complOpens S hS (insert z T)
  rw [mem_complOpens, mem_complOpens, mem_complOpens, Finset.mem_singleton, Finset.mem_insert]
  tauto

lemma complOpens_self : complOpens S hS S = ⊤ := by
  ext x
  change x ∈ complOpens S hS S ↔ True
  rw [mem_complOpens, iff_true]
  tauto

/-- **Extension over finitely many closed points**: a finite étale scheme over `X \ S` which
extends over `X \ (S \ {z})` for every `z ∈ S` extends over `X`. -/
theorem exists_pullback_iso_of_forall_mem (Z : (complOpens S hS ∅).toScheme.FiniteEtale)
    (hZ : ∀ z ∈ S, ∃ Zz : (complOpens S hS {z}).toScheme.FiniteEtale,
      Nonempty ((pullback (X.homOfLE (complOpens_mono S hS (Finset.empty_subset _)))).obj Zz ≅
        Z)) :
    ∃ P : X.FiniteEtale, Nonempty ((pullback (complOpens S hS ∅).ι).obj P ≅ Z) := by
  classical
  have key : ∀ T : Finset X, T ⊆ S → ∃ ZT : (complOpens S hS T).toScheme.FiniteEtale,
      Nonempty ((pullback (X.homOfLE (complOpens_mono S hS (Finset.empty_subset T)))).obj ZT ≅
        Z) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨Z, ⟨eqToIso (by rw [Scheme.homOfLE_rfl]) ≪≫ pullbackIdIso Z⟩⟩
    | @insert z T hzT ih =>
      intro hT
      obtain ⟨ZT, ⟨eT⟩⟩ := ih ((Finset.subset_insert z T).trans hT)
      obtain ⟨Zz, ⟨ez⟩⟩ := hZ z (hT (Finset.mem_insert_self z T))
      let iA := X.homOfLE (complOpens_mono S hS (Finset.subset_insert z T))
      let iB := X.homOfLE (complOpens_mono S hS
        (Finset.singleton_subset_iff.2 (Finset.mem_insert_self z T)))
      let dA := X.homOfLE (complOpens_mono S hS (Finset.empty_subset T))
      let dB := X.homOfLE (complOpens_mono S hS (Finset.empty_subset {z}))
      have H : IsPullback dA dB iA iB := by
        refine IsOpenImmersion.isPullback dA dB iA iB (by simp [dA, dB, iA, iB]) ?_
        simp only [iA, iB, dB, Scheme.opensRange_homOfLE]
        ext x
        simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe]
        rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
        rw [← complOpens_inf S hS hzT]
        exact ⟨fun hx ↦ ⟨hx, x.2⟩, fun hx ↦ hx.1⟩
      have hcov (x) : x ∈ Set.range iA ∨ x ∈ Set.range iB := by
        have hx : (complOpens S hS (insert z T)).ι x ∈
            complOpens S hS T ⊔ complOpens S hS {z} := by
          rw [complOpens_sup]
          exact x.2
        rcases hx with hx | hx
        · left
          rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
          exact hx
        · right
          rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
          exact hx
      obtain ⟨P, ⟨eP⟩⟩ := exists_pullback_iso_of_isPullback dA dB iA iB H hcov ZT Zz (eT ≪≫ ez.symm)
      refine ⟨P, ⟨?_⟩⟩
      have h : X.homOfLE (complOpens_mono S hS (Finset.empty_subset (insert z T))) = dA ≫ iA := by
        simp [dA, iA]
      exact eqToIso (by rw [h]) ≪≫ pullbackCompIso dA iA P ≪≫ (pullback dA).mapIso eP ≪≫ eT
  obtain ⟨ZS, ⟨eS⟩⟩ := key S subset_rfl
  have htop : ⊤ ≤ complOpens S hS S := (complOpens_self S hS).ge
  let φ : X ⟶ (complOpens S hS S).toScheme := X.topIso.inv ≫ X.homOfLE htop
  refine ⟨(pullback φ).obj ZS, ⟨?_⟩⟩
  have h : (complOpens S hS ∅).ι ≫ φ =
      X.homOfLE (complOpens_mono S hS (Finset.empty_subset S)) := by
    rw [← cancel_mono (complOpens S hS S).ι]
    simp [φ]
  exact (pullbackCompIso _ _ _).symm ≪≫ eqToIso (by rw [h]) ≪≫ eS

end AlgebraicGeometry.Scheme.FiniteEtale
