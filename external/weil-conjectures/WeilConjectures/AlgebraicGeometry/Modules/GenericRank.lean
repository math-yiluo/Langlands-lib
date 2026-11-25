/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Determinant
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import WeilConjectures.AlgebraicGeometry.Modules.Torsion

/-!
# The generic rank of an `𝒪_X`-module

For an `𝒪_X`-module `M` on an irreducible scheme `X` with generic point `η`, the *rank* of `M` is
`rk M = dim_{k(X)} M_η`, the dimension of the stalk at the generic point over the function field
(`AlgebraicGeometry.Scheme.Modules.rank`).

If `M` is free with basis `e₁, …, e_n` on an open `Y`, then the germs of the `eᵢ` form a basis of
the stalk `M_x` over `𝒪_{X,x}` for every `x ∈ Y`
(`AlgebraicGeometry.Scheme.Modules.exists_basis_stalk_of_over_iso_free`). Hence a finite locally
free module of rank `r` has rank `r`, and conversely a finite locally free module on an
irreducible scheme is finite locally free of rank `rk M`
(`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_rank`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.rank`: the generic rank `dim_{k(X)} M_η`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section StalkBasis

variable {M : X.Modules} {Y : X.Opens} {I : Type u} [Fintype I] [DecidableEq I]
  (e : M.over Y ≅ SheafOfModules.free I)

/-- The `i`-th section of the frame of `M` over `Y` given by a trivialisation
`M.over Y ≅ 𝒪_Y^I`. -/
noncomputable def frameSection (i : I) : Γ(M, Y) :=
  (sectionsLinearEquivOfOverIsoFree e le_rfl).symm (Pi.single i 1)

lemma sectionsLinearEquivOfOverIsoFree_frameSection {W : X.Opens} (h : W ≤ Y) (i : I) :
    sectionsLinearEquivOfOverIsoFree e h (M.presheaf.map (homOfLE h).op (frameSection e i)) =
      Pi.single i 1 := by
  ext j
  have := sectionsLinearEquivOfOverIsoFree_map e (le_refl Y) h (frameSection e i) j
  refine this.trans ?_
  rw [frameSection, LinearEquiv.apply_symm_apply]
  by_cases hij : j = i
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero]

/-- Every section over `W ⊆ Y` is a linear combination of the restricted frame. -/
lemma eq_sum_smul_frameSection {W : X.Opens} (h : W ≤ Y) (s : Γ(M, W)) :
    s = ∑ i, sectionsLinearEquivOfOverIsoFree e h s i •
      M.presheaf.map (homOfLE h).op (frameSection e i) := by
  apply (sectionsLinearEquivOfOverIsoFree e h).injective
  rw [map_sum]
  simp_rw [_root_.map_smul, sectionsLinearEquivOfOverIsoFree_frameSection]
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- **The stalk of a free module.** If `M.over Y ≅ 𝒪_Y^I`, then for `x ∈ Y` the germs of the
frame form a basis of the stalk `M_x` over `𝒪_{X,x}`. -/
theorem exists_basis_stalk_of_over_iso_free {x : X} (hx : x ∈ Y) :
    ∃ b : Module.Basis I (X.presheaf.stalk x) (M.presheaf.stalk x),
      ∀ i, b i = M.presheaf.germ Y x hx (frameSection e i) := by
  classical
  let v : I → M.presheaf.stalk x := fun i ↦ M.presheaf.germ Y x hx (frameSection e i)
  have hli : LinearIndependent (X.presheaf.stalk x) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose U hxU a ha using fun i ↦ X.presheaf.exists_germ_eq (g i)
    let W : X.Opens := ⟨(Y : Set X) ∩ ⋂ i, (U i : Set X),
      Y.isOpen.inter (isOpen_iInter_of_finite fun i ↦ (U i).isOpen)⟩
    have hWY : W ≤ Y := fun _ h ↦ h.1
    have hWU (i : I) : W ≤ U i := fun _ h ↦ Set.mem_iInter.mp h.2 i
    have hxW : x ∈ W := ⟨hx, Set.mem_iInter.mpr hxU⟩
    let c (i : I) : Γ(X, W) := X.presheaf.map (homOfLE (hWU i)).op (a i)
    have hgi (i : I) : g i = X.presheaf.germ W x hxW (c i) := by
      rw [TopCat.Presheaf.germ_res_apply, ha]
    have hvi (i : I) : v i = M.presheaf.germ W x hxW
        (M.presheaf.map (homOfLE hWY).op (frameSection e i)) :=
      (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    let s : Γ(M, W) := ∑ i, c i • M.presheaf.map (homOfLE hWY).op (frameSection e i)
    have hs : M.presheaf.germ W x hxW s = M.presheaf.germ W x hxW 0 := by
      rw [map_zero, map_sum]
      simp_rw [germ_smul]
      rw [← hg]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hgi, hvi]
    obtain ⟨W', hxW', i₁, i₂, hW'⟩ := M.presheaf.germ_eq x hxW hxW s 0 hs
    rw [map_zero] at hW'
    have hc : X.presheaf.map i₁.op (c i) = 0 := by
      have h1 := congrArg (fun t ↦ sectionsLinearEquivOfOverIsoFree e
        ((leOfHom i₁).trans hWY) t i) hW'
      simp only [map_zero, Pi.zero_apply] at h1
      rw [← h1, map_sum, map_sum, Finset.sum_apply]
      simp_rw [Modules.map_smul, _root_.map_smul]
      rw [Finset.sum_eq_single i]
      · rw [show i₁ = homOfLE (leOfHom i₁) from rfl, presheaf_map_homOfLE_map_homOfLE,
          sectionsLinearEquivOfOverIsoFree_frameSection]
        simp
      · intro j _ hji
        rw [show i₁ = homOfLE (leOfHom i₁) from rfl, presheaf_map_homOfLE_map_homOfLE,
          sectionsLinearEquivOfOverIsoFree_frameSection]
        simp [Ne.symm hji]
      · simp
    rw [hgi, ← TopCat.Presheaf.germ_res_apply X.presheaf i₁ x hxW', hc, map_zero]
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.stalk x) (Set.range v) := by
    intro m _
    obtain ⟨V, hxV, s, rfl⟩ := M.presheaf.exists_germ_eq m
    have hW : V ⊓ Y ≤ Y := inf_le_right
    have hxW : x ∈ V ⊓ Y := ⟨hxV, hx⟩
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_left : V ⊓ Y ⟶ V) x hxW,
      eq_sum_smul_frameSection e hW (M.presheaf.map (homOfLE inf_le_left).op s), map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [germ_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, ?_⟩)
    exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  exact ⟨Module.Basis.mk hli hsp, fun i ↦ Module.Basis.mk_apply hli hsp i⟩

omit [DecidableEq I] in
/-- If `M.over Y ≅ 𝒪_Y^I`, then for `x ∈ Y` the stalk `M_x` is free of rank `|I|`. -/
theorem finrank_stalk_of_over_iso_free (h : Nonempty (M.over Y ≅ SheafOfModules.free I)) {x : X}
    (hx : x ∈ Y) : Module.finrank (X.presheaf.stalk x) (M.presheaf.stalk x) = Fintype.card I := by
  classical
  obtain ⟨e⟩ := h
  exact Module.finrank_eq_card_basis (exists_basis_stalk_of_over_iso_free e hx).choose

end StalkBasis

section Rank

variable [IrreducibleSpace X]

variable (M) in
/-- **The rank of an `𝒪_X`-module** on an irreducible scheme: the dimension
`rk M = dim_{k(X)} M_η` of its stalk at the generic point `η` over the function field. -/
noncomputable def rank (M : X.Modules) : ℕ :=
  Module.finrank X.functionField (M.presheaf.stalk (genericPoint X))

lemma genericPoint_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  (genericPoint_specializes x).mem_open U.isOpen hx

/-- A module which is free of rank `|I|` on a nonempty open has rank `|I|`. -/
theorem rank_eq_card_of_over_iso_free {M : X.Modules} {Y : X.Opens} {I : Type u} [Fintype I]
    (e : M.over Y ≅ SheafOfModules.free I) {x : X} (hx : x ∈ Y) : M.rank = Fintype.card I := by
  classical
  exact finrank_stalk_of_over_iso_free ⟨e⟩ (genericPoint_mem hx)

/-- A finite locally free module of rank `r` on an irreducible scheme has rank `r`. -/
theorem rank_eq_of_isFiniteLocallyFreeOfRank (M : X.Modules) {r : ℕ}
    [M.IsFiniteLocallyFreeOfRank r] : M.rank = r := by
  obtain ⟨I, Y, hY, h⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.1
      ‹M.IsFiniteLocallyFreeOfRank r›
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 hY).exists_mem (genericPoint X)
  rw [rank_eq_card_of_over_iso_free (h i).some hi, Fintype.card_ulift, Fintype.card_fin]

/-- **A finite locally free module on an irreducible scheme has constant rank** `rk M`. -/
theorem isFiniteLocallyFreeOfRank_rank (M : X.Modules) [M.IsFiniteLocallyFree] :
    M.IsFiniteLocallyFreeOfRank M.rank := by
  choose Y I hI hx e using exists_mem_over_iso_free M
  refine SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}.2
    ⟨X, Y, ?_, fun x ↦ ⟨(e x).some ≪≫ SheafOfModules.freeFunctor.mapIso ?_⟩⟩
  · rw [Opens.coversTop_iff]
    exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
  · have h := rank_eq_card_of_over_iso_free (e x).some (hx x)
    exact (((Fintype.equivFin (I x)).trans (finCongr h.symm)).trans Equiv.ulift.symm).toIso

end Rank

section Exact

variable {S : ShortComplex X.Modules}

/-- **Stalks of a short exact sequence.** At every point `x`, a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of `𝒪_X`-modules gives an exact sequence of `𝒪_{X,x}`-modules
`0 → M₁,ₓ → M₂,ₓ → M₃,ₓ → 0`. -/
lemma injective_surjective_exact_stalkLinearMap (hS : S.ShortExact) (x : X) :
    Function.Injective (S.f.stalkLinearMap x) ∧ Function.Surjective (S.g.stalkLinearMap x) ∧
      Function.Exact (S.f.stalkLinearMap x) (S.g.stalkLinearMap x) := by
  have h := hS.map_of_exact (stalkFunctor x)
  refine ⟨?_, ?_, ?_⟩
  · have := h.mono_f
    exact (AddCommGrpCat.mono_iff_injective _).1 this
  · have := h.epi_g
    exact (AddCommGrpCat.epi_iff_surjective _).1 this
  · exact (ShortComplex.ab_exact_iff_function_exact _).1 h.exact

variable [IrreducibleSpace X]

/-- The stalk of the torsion subsheaf at the generic point vanishes. -/
lemma subsingleton_stalk_torsion (M : X.Modules) :
    Subsingleton ((torsion M).presheaf.stalk (genericPoint X)) := by
  refine ⟨fun a b ↦ ?_⟩
  suffices h : ∀ a : (torsion M).presheaf.stalk (genericPoint X), a = 0 from
    (h a).trans (h b).symm
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (torsion M).presheaf.exists_germ_eq a
  obtain ⟨V, hV, hd, hs⟩ := s.2
  have hVne : (V : Set X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hd hU
    rw [h, closure_empty] at this
    exact this
  obtain ⟨y, hy⟩ := hVne
  have hη : genericPoint X ∈ V := genericPoint_mem hy
  rw [← TopCat.Presheaf.germ_res_apply (torsion M).presheaf (homOfLE hV) _ hη]
  have : (torsion M).presheaf.map (homOfLE hV).op s = 0 := Subtype.ext hs
  rw [this, map_zero]

/-- The torsion subsheaf has rank zero. -/
lemma rank_torsion (M : X.Modules) : (torsion M).rank = 0 := by
  have := subsingleton_stalk_torsion M
  exact Module.finrank_zero_of_subsingleton

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` whose first term has zero generic stalk,
the generic stalks of `M₂` and `M₃` are isomorphic, so `rk M₂ = rk M₃`. -/
lemma rank_eq_of_shortExact_of_subsingleton (hS : S.ShortExact)
    [Subsingleton (S.X₁.presheaf.stalk (genericPoint X))] : S.X₂.rank = S.X₃.rank := by
  obtain ⟨-, hsurj, hex⟩ := injective_surjective_exact_stalkLinearMap hS (genericPoint X)
  have hinj : Function.Injective (S.g.stalkLinearMap (genericPoint X)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp hex]
    exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

end Exact

section ExactIntegral

variable {S : ShortComplex X.Modules} [IsIntegral X]

/-- **The rank is additive in short exact sequences** whose middle term has finite-dimensional
generic stalk. -/
lemma rank_eq_add_of_shortExact (hS : S.ShortExact)
    [FiniteDimensional X.functionField (S.X₂.presheaf.stalk (genericPoint X))] :
    S.X₂.rank = S.X₁.rank + S.X₃.rank := by
  obtain ⟨hinj, hsurj, hex⟩ := injective_surjective_exact_stalkLinearMap hS (genericPoint X)
  have := LinearMap.finrank_range_add_finrank_ker (S.g.stalkLinearMap (genericPoint X))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, LinearMap.exact_iff.mp hex,
    LinearMap.finrank_range_of_inj hinj] at this
  rw [rank, rank, rank, ← this]
  ring

/-- The generic stalk of a finite locally free module is finite-dimensional. -/
lemma finiteDimensional_stalk_of_isFiniteLocallyFree (M : X.Modules) [M.IsFiniteLocallyFree] :
    FiniteDimensional X.functionField (M.presheaf.stalk (genericPoint X)) := by
  classical
  obtain ⟨Y, I, _, hx, ⟨e⟩⟩ := exists_mem_over_iso_free M (genericPoint X)
  exact Module.Finite.of_basis (exists_basis_stalk_of_over_iso_free e hx).choose

end ExactIntegral

end AlgebraicGeometry.Scheme.Modules
