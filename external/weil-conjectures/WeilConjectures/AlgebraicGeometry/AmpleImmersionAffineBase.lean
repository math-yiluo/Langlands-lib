/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.AmpleFinitePowerCover
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso

/-! # An ample module gives an immersion into projective space over an affine base

Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph, and Lemma 01VT
(blueprint: lem-weil-pbc-ample-very-ample-immersion-affine-base).

The node's `P_n = Proj(A[x₀,…,xₙ])` over `Spec A` is `ℙ(ULift (Fin (n + 1)); Spec A)`, the
projective space `ℙⁿ_{Spec A}` (identified with `Proj(A[x₀,…,xₙ])` over `Spec A` by Stacks,
Constructions, Lemma 01O3), with structure morphism `ℙ(…; Spec A) ↘ Spec A` and twisting
module `ProjectiveSpace.twist` (the recorded declaration of `def-pc-projective-space-twist`),
as in `IsHProjective` and `IsVeryAmple`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem closure_div_eq_top_of_eq_one {V S : Scheme.{u}} (g : V ⟶ S)
    (W : S.Opens) {b : Γ(V, ⊤)} (hb : b = 1) {μ : Type*} (t : μ → Γ(V, ⊤))
    (hle : V.basicOpen b ≤ g ⁻¹ᵁ W) (hle₁ : V.basicOpen (1 : Γ(V, ⊤)) ≤ g ⁻¹ᵁ W)
    (h : Subring.closure (Set.range (g.resLE W (V.basicOpen 1) hle₁).appTop ∪
      Set.range fun i ↦ V.divBasicOpen (t i) 1) = ⊤) :
    Subring.closure (Set.range (g.resLE W (V.basicOpen b) hle).appTop ∪
      Set.range fun i ↦ V.divBasicOpen (t i) b) = ⊤ := by
  subst hb
  exact h

private theorem exists_immersion_power_of_affine_cover {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsSeparated f] [LocallyOfFiniteType f] (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L] {ι : Type u} [Finite ι] [Nonempty ι]
    (s : ι → (𝟙_ X.Modules ⟶ L))
    (hs : ∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl)
    (hcov : ⨆ i, (Hom.zeroLocus (s i)).support.compl = ⊤) :
    ∃ (N : ℕ) (_ : 0 < N) (β : Type u) (_ : Finite β) (_ : Nonempty β)
      (φ : X ⟶ ℙ(β; S)), IsImmersion φ ∧ φ ≫ ℙ(β; S) ↘ S = f ∧
      Nonempty (L.tensorPow N ≅ ProjectiveSpace.twistRestrict φ 1) := by
  classical
  set U : ι → X.Opens := fun i ↦ (Hom.zeroLocus (s i)).support.compl
  have hUa (i : ι) : IsAffine (U i).toScheme := hs i
  have : CompactSpace X := by
    refine ⟨?_⟩
    have h := isCompact_iUnion fun i ↦ (hs i).isCompact
    rwa [← TopologicalSpace.Opens.coe_iSup, hcov, TopologicalSpace.Opens.coe_top] at h
  -- generators of `Γ(X_{s i}, 𝒪_X)` over `Γ(S, 𝒪_S)`
  choose m hm t ht using fun i ↦ exists_finite_subring_closure_divBasicOpen_eq_top
    ((U i).ι ≫ f) 1 ⊤ (isAffineOpen_top S) fun _ _ ↦ trivial
  have : ∀ i, Finite (m i) := hm
  -- clearing denominators with a common exponent `N + 1`
  choose k v hv using fun p : Σ i, m i ↦
    exists_restrict_eq_smul_tensorPowSectionOne f L (s p.1) ((U p.1).topIso.hom (t p.1 p.2))
  obtain ⟨N, hN⟩ := Finite.exists_le k
  choose w hw using fun p : Σ i, m i ↦
    exists_restrict_eq_smul_tensorPowSectionOne_of_le (s p.1) (v p) (hv p)
      ((hN p).trans N.le_succ)
  set n : Type u := ι ⊕ Σ i, m i
  set s' : n → Γ(L.tensorPow (N + 1), ⊤) :=
    Sum.elim (fun i ↦ tensorPowSectionOne (s i) (N + 1) ⊤) w
  set U' : n → X.Opens := Sum.elim U fun _ ↦ ⊥
  have hs' (j : n) : IsFreeGenerator
      ((L.tensorPow (N + 1)).presheaf.map (homOfLE (le_top : U' j ≤ ⊤)).op (s' j)) := by
    rcases j with i | p
    · simp only [s', U', Sum.elim_inl]
      rw [presheaf_map_tensorPowSectionOne]
      exact isFreeGenerator_tensorPowSectionOne _ (isFreeGenerator_app_one_of_le _ le_rfl) _
    · exact isFreeGenerator_bot _
  have hU' : ⨆ j, U' j = ⊤ :=
    eq_top_iff.mpr (hcov.ge.trans (iSup_le fun i ↦ le_iSup U' (Sum.inl i)))
  set φ := ProjectiveSpace.homOfIsFreeGenerator s' U' hs' f hU'
  have hpre (i : ι) : φ ⁻¹ᵁ ProjectiveSpace.standardOpen n S (Sum.inl i) = U i := by
    refine le_antisymm (le_compl_support_zeroLocus_of_isFreeGenerator (s i) N.succ_ne_zero ?_)
      (ProjectiveSpace.le_preimage_standardOpen s' U' hs' f hU' (Sum.inl i))
    have h := ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso
      (ProjectiveSpace.twistRestrictHom s' U' hs' f hU')
      (ProjectiveSpace.twistRestrictHom_app_pullbackSection s' U' hs' f hU') (Sum.inl i)
    simp only [s', Sum.elim_inl] at h
    rwa [presheaf_map_tensorPowSectionOne] at h
  refine ⟨N + 1, Nat.succ_pos _, n, inferInstance, inferInstance, φ, ?_,
    ProjectiveSpace.homOfIsFreeGenerator_over s' U' hs' f hU',
    ⟨(asIso (ProjectiveSpace.twistRestrictHom s' U' hs' f hU')).symm⟩⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun i : ι ↦ ProjectiveSpace.standardOpen n S (Sum.inl i)) ?_ fun i ↦ ?_
  · rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ i, U i := by rw [hcov]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (hpre i).ge hxi⟩)
  -- on `X_{s i}`, `φ` is the immersion classified by the generators `t i μ`
  set s'' := ProjectiveSpace.localSections s' U' hs' (Sum.inl i)
  have h₁ : s'' (Sum.inl i) = 1 := by
    simp [s'', ProjectiveSpace.localSections]
  have ht' (μ : m i) : s'' (Sum.inr ⟨i, μ⟩) = t i μ := by
    have h : ProjectiveSpace.sectionRatio s' U' hs' (Sum.inl i) (Sum.inr ⟨i, μ⟩) =
        (U i).topIso.hom (t i μ) := by
      refine ((hs' (Sum.inl i)).coeff_eq_iff _ _).mpr ?_
      simp only [s', U', Sum.elim_inl, Sum.elim_inr]
      rw [presheaf_map_tensorPowSectionOne]
      exact (hw ⟨i, μ⟩).symm
    simp only [s'', ProjectiveSpace.localSections, h]
    exact Iso.hom_inv_id_apply _ _
  set B := (U i).toScheme.basicOpen (s'' (Sum.inl i))
  have : IsIso B.ι := Scheme.Opens.isIso_ι_of_eq_top (by simp [B, h₁])
  have key : B.ι ≫ φ.resLE (ProjectiveSpace.standardOpen n S (Sum.inl i)) (U i) (hpre i).ge =
      (ProjectiveSpace.homOfSections ((U i).ι ≫ f) s''
        (ProjectiveSpace.span_range_localSections s' U' hs' (Sum.inl i))).resLE
        (ProjectiveSpace.standardOpen n S (Sum.inl i)) B
        (ProjectiveSpace.homOfSections_preimage_standardOpen _ _ _ _).ge := by
    rw [← cancel_mono (ProjectiveSpace.standardOpen n S (Sum.inl i)).ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact congrArg (B.ι ≫ ·) (ProjectiveSpace.ι_homOfIsFreeGenerator s' U' hs' f hU' (Sum.inl i))
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr φ (U := ProjectiveSpace.standardOpen n S (Sum.inl i)) le_rfl rfl
      (hpre i) @IsImmersion,
    ← MorphismProperty.cancel_left_of_respectsIso @IsImmersion B.ι, key,
    ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
      (ProjectiveSpace.standardOpenIso n S (Sum.inl i)).hom,
    ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom]
  refine isImmersion_homOfVector_divBasicOpen ((U i).ι ≫ f) s'' (Sum.inl i) ⊤
    (isAffineOpen_top S) (fun _ _ ↦ trivial) (eq_top_iff.mpr
      ((closure_div_eq_top_of_eq_one _ _ h₁ (t i) _ _ (ht i)).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
  rintro _ ⟨μ, rfl⟩
  exact ⟨⟨Sum.inr ⟨i, μ⟩, Sum.inr_ne_inl⟩,
    congrArg (fun x ↦ (U i).toScheme.divBasicOpen x (s'' (Sum.inl i))) (ht' μ)⟩


private theorem positiveTensorPower_iso_tensorPow (X : Scheme.{u}) (L : X.Modules) :
    ∀ (d : ℕ) (hd : 0 < d),
      Nonempty (SheafOfModules.positiveTensorPower X.sheaf L d hd ≅ L.tensorPow d) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  intro d
  induction d using Nat.twoStepInduction with
  | zero => intro hd; omega
  | one =>
    intro hd
    exact ⟨(ρ_ L).symm⟩
  | more d _ ih' =>
    intro hd
    obtain ⟨e⟩ := ih' (by omega)
    exact ⟨(e ⊗ᵢ Iso.refl L) ≪≫ β_ _ _⟩

/-- An ample invertible module on a scheme locally of finite type over `Spec A` has a
positive tensor power obtained by pulling back `𝒪(1)` along an immersion into projective
space `ℙⁿ_{Spec A} = Proj(A[x₀,…,xₙ])` over `Spec A`.
Source: Stacks Project, Morphisms, Lemma 01VS, first proof paragraph; Lemma 01VT (1) ⇒ (5)
(blueprint: lem-weil-pbc-ample-very-ample-immersion-affine-base).

Proof:
1. Ampleness (`def-weil-pbc-ample-invertible-module`) gives quasi-compactness and a finite
   affine cover by nonvanishing loci of sections of positive powers. The scheme is separated
   by `lem-weil-pbc-ample-scheme-separated`. Raise the sections to powers to put them all in
   one power `L^m`; their nonvanishing loci stay the same by the local rank-one calculation
   (`def-sc-invertible-module`, `def-pur-sheaf-tensor-product`). If `X` is empty, choose
   `d = 1`, `n = 0`, and the empty immersion; the modules are uniquely isomorphic.
2. By `lem-weil-pbc-lft-affine-pairs`, each affine piece has a finitely generated `A`-algebra
   of functions. Choose a finite set of generators for each piece.
3. By `lem-pc-section-clearing-denominators`, express these generators as quotients of global
   sections by powers of the covering sections. Choose one sufficiently large common power
   `L^d`, and multiply numerators and denominators to obtain sections `b_k`, `b_kl` with
   `b_kl / b_k` equal to the chosen generators. Tensor exponent laws identify these powers.
4. The sections generate `L^d`, so `lem-weil-pbc-sections-morphism-to-proj-polynomial-ring`
   gives `j` over `Spec A`, an isomorphism `j^*𝒪(1) ≅ L^d`, and the prescribed coordinate
   ratios and inverse images of standard opens.
5. Let `U` be the union of the standard opens indexed by the covering sections. Factor `j`
   through `U` by `lem-weil-pbc-morphism-factors-through-open-subscheme`. The coordinate
   ratios generate the affine-piece rings, so the induced ring maps are surjective.
   By `lem-weil-pbc-closed-immersion-affine-cover-criterion` this factor is a closed immersion.
   Following it by the open inclusion gives an immersion (`def-weil-closed-immersion`,
   `def-weil-open-immersion`).
6. Set `i = j` and invert the module isomorphism from step 4. This supplies all conclusions.
-/
theorem IsAmple.exists_immersion_affine_base (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (L : X.Modules) [L.IsInvertible]
    (hL : IsAmple X L) :
    ∃ (d : ℕ) (hd : 0 < d) (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A))),
      IsImmersion i ∧
      i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A) = f ∧
      Nonempty (SheafOfModules.positiveTensorPower X.sheaf L d hd ≅
        (tensorPullback i).obj
          (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) 1)) := by
  classical
  obtain ⟨m, hm, r, s, hs, hcov⟩ := hL.exists_finite_common_power_cover X L
  let : CompactSpace X := hL.1
  let : X.IsSeparated := AlgebraicGeometry.isSeparated_of_isAmple X L hL
  let : IsSeparated f := inferInstance
  let : SheafOfModules.IsInvertible.{u, u, u} (L.tensorPow m) :=
    IsInvertible.sheafOfModules_isInvertible _
  obtain ⟨N, hN, β, hβ, hβne, j, hj, hjf, ⟨ej⟩⟩ :=
    exists_immersion_power_of_affine_cover f (L.tensorPow m) s hs hcov
  let : Finite β := hβ
  let : Nonempty β := hβne
  let : IsImmersion j := hj
  obtain ⟨n, e, he, ⟨etwist⟩⟩ := ProjectiveSpace.exists_finite_index_iso β (Spec (.of A))
  let i := j ≫ e.hom
  have hi : IsImmersion i := inferInstance
  have hif : i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of A)) ↘ Spec (.of A) = f := by
    dsimp [i]
    rw [Category.assoc, he, hjf]
  have hd : 0 < m * N := Nat.mul_pos hm hN
  obtain ⟨epow⟩ := positiveTensorPower_iso_tensorPow X L (m * N) hd
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction i
  let epb := (adj.leftAdjointUniq (pullbackPushforwardAdjunction i)).app
    (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of A)) 1)
  exact ⟨m * N, hd, n, i, hi, hif,
    ⟨epow ≪≫ L.tensorPowMulIso m N ≪≫ ej ≪≫
      (pullback j).mapIso etwist.symm ≪≫
      (pullbackComp j e.hom).app _ ≪≫ epb.symm⟩⟩

end AlgebraicGeometry.Scheme.Modules
