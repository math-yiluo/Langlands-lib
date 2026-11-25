/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Bounded complexes of finite free modules and their perfect locus

A bounded complex `P` of finite free `𝒪_Y`-modules represents a perfect object of the derived
category of `Y`. For integers `i r : ℕ` there is an open subscheme `U` of `Y` such that a morphism
`g : Y' ⟶ Y` factors through `U` if and only if `g^* P` has cohomology a finite locally free
module of rank `r` placed in degree `i`
(`AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex`: bounded complexes of finite free
  modules.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`: a family of modules is that of
  a finite locally free module of rank `r` placed in degree `i`.

## Implementation details

There is no derived category of `X.Modules` with derived pullback and pushforward available, so
`IsFiniteLocallyFreeInDegree` is stated on the cohomology sheaves. For an object represented by a
complex this is the same as being isomorphic to `ℰ[-i]` with `ℰ` finite locally free of rank `r`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- `IsFiniteFreeComplex P d` says that the cochain complex `P` of `𝒪_X`-modules is a **bounded
complex of finite free modules in degrees `[0, d]`**: it vanishes outside `[0, d]`, and each
`P.X n` is isomorphic to a free module `𝒪_X^r` of finite rank. -/
structure IsFiniteFreeComplex (P : CochainComplex X.Modules ℤ) (d : ℕ) : Prop where
  isStrictlyGE : P.IsStrictlyGE 0
  isStrictlyLE : P.IsStrictlyLE d
  exists_iso_free (n : ℤ) :
    ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))

/-- `IsFiniteLocallyFreeInDegree M i r` says that the family `M = (M q)_{q: ℕ}` of `𝒪_X`-modules,
thought of as the cohomology sheaves `H^q(E)` of an object `E` of the derived category of
`𝒪_X`-modules, is that of a **finite locally free module of rank `r` placed in degree `i`**:
`M q = 0` for `q ≠ i`, and `M i` is finite locally free of rank `r`. -/
structure IsFiniteLocallyFreeInDegree (M : ℕ → X.Modules) (i r : ℕ) : Prop where
  isZero (q : ℕ) (hq : q ≠ i) : IsZero (M q)
  isFiniteLocallyFreeOfRank : (M i).IsFiniteLocallyFreeOfRank r

/-- A family of modules is that of an invertible module placed in degree `0` if and only if it
vanishes in nonzero degrees and is invertible in degree `0`. -/
theorem isFiniteLocallyFreeInDegree_zero_one_iff (M : ℕ → X.Modules) :
    IsFiniteLocallyFreeInDegree M 0 1 ↔
      (∀ q ≠ 0, IsZero (M q)) ∧ SheafOfModules.IsInvertible (R := X.ringCatSheaf) (M 0) :=
  ⟨fun h ↦ ⟨h.isZero, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).2
      h.isFiniteLocallyFreeOfRank⟩,
    fun h ↦ ⟨h.1, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).1 h.2⟩⟩

/-- The terms of a bounded complex of finite free modules can be trivialised with ranks vanishing
outside the bounds. -/
lemma IsFiniteFreeComplex.exists_iso_free_of_rank_eq_zero {P : CochainComplex X.Modules ℤ}
    {d : ℕ} (hP : IsFiniteFreeComplex P d) :
    ∃ r : ℤ → ℕ, (∀ n : ℤ, n < 0 ∨ d < n → r n = 0) ∧
      Nonempty (∀ n, P.X n ≅
        SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r n)))) := by
  classical
  choose r₀ e₀ using hP.exists_iso_free
  have := hP.isStrictlyGE
  have := hP.isStrictlyLE
  refine ⟨fun n ↦ if n < 0 ∨ (d : ℤ) < n then 0 else r₀ n, fun n hn ↦ ite_eq_left hn, ⟨fun n ↦ ?_⟩⟩
  by_cases hn : n < 0 ∨ (d : ℤ) < n
  · have h₁ : IsZero (P.X n) := by
      rcases hn with hn | hn
      · exact CochainComplex.isZero_of_isStrictlyGE P 0 n hn
      · exact CochainComplex.isZero_of_isStrictlyLE P d n hn
    refine h₁.iso ?_
    simp only [ite_eq_left hn]
    exact isZero_free_of_isEmpty _
  · simp only [ite_eq_right hn]
    exact (e₀ n).some

/-- **The perfect locus of a bounded complex of finite free modules.** Let `P` be a bounded complex
of finite free `𝒪_Y`-modules, representing a perfect object `E` of the derived category of `Y`, and
fix `i r: ℕ`. There is an open subscheme `U` of `Y` such that a morphism `g: Y' ⟶ Y` factors
through `U` if and only if `L g^* E = g^* P` is a finite locally free module of rank `r` placed in
degree `i` (`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`). -/
theorem IsFiniteFreeComplex.exists_opens_range_subset_iff {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    ∃ U : Y.Opens, ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y), Set.range g.base ⊆ U ↔
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r := by
  classical
  obtain ⟨rk, hrk, ⟨e⟩⟩ := hP.exists_iso_free_of_rank_eq_zero
  -- the matrices of the differentials
  set C : ∀ n m : ℤ, Matrix (ULift.{u} (Fin (rk m))) (ULift.{u} (Fin (rk n))) Γ(Y, ⊤) :=
    fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom) with hCdef
  have hC (n m l : ℤ) : C m l * C n m = 0 := by
    simp only [hCdef]
    rw [← freeMatrix_comp]
    simp
  have hN (n : ℤ) (hn : n < 0 ∨ d < n) : IsEmpty (ULift.{u} (Fin (rk n))) := by
    rw [hrk n hn]
    infer_instance
  refine ⟨⟨{y | Scheme.RankCondition C i r y}, Scheme.isOpen_setOf_rankCondition hC d hN i r⟩,
    fun {Y'} g ↦ ?_⟩
  -- the pullback complex, its trivialisations and the matrices of its further pullbacks
  set Pg := ((Modules.pullback g).mapHomologicalComplex _).obj P with hPg
  let eg (n : ℤ) : Pg.X n ≅ SheafOfModules.free (ULift.{u} (Fin (rk n))) :=
    (Modules.pullback g).mapIso (e n) ≪≫ pullbackFreeIso g _
  have hCg (n m : ℤ) {Z : Scheme.{u}} (j : Z ⟶ Y') :
      freeMatrix ((((Modules.pullback j).mapIso (eg n) ≪≫ pullbackFreeIso j _).inv ≫
        (((Modules.pullback j).mapHomologicalComplex _).obj Pg).d n m ≫
        ((Modules.pullback j).mapIso (eg m) ≪≫ pullbackFreeIso j _).hom)) =
        (C n m).map (j ≫ g).appTop := by
    rw [freeMatrix_pullback_d, freeMatrix_pullback_d, map_appTop_comp]
  constructor
  · -- near every point of `Y'`, the complex `g^* P` is split with the right cohomology
    intro hg
    have hy (y' : Y') : Scheme.RankCondition C i r (g y') := hg ⟨y', rfl⟩
    choose W hyW hW using fun y' ↦ Scheme.exists_opens_hasSplitHomology hC d hN (hy y')
    set V : Y' → Y'.Opens := fun y' ↦ g ⁻¹ᵁ W y' with hVdef
    have hV : ⨆ y', V y' = ⊤ :=
      eq_top_iff.2 fun y' _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y', hyW y'⟩
    have key (y' : Y') (q : ℤ) : Nonempty ((Pg.homology q).restrict (V y').ι ≅
        SheafOfModules.free (ULift.{u} (Fin (if q = i then r else 0)))) := by
      set j := (V y').ι
      obtain ⟨I, Pm, σ, τ, h₁, h₂, h₃, h₄⟩ :=
        (hW y' (j ≫ g) (by rintro _ ⟨z, rfl⟩; exact z.2) q).of_equiv Equiv.ulift.symm
      let E (n : ℤ) := (Modules.pullback j).mapIso (eg n) ≪≫
        pullbackFreeIso j (ULift.{u} (Fin (rk n)))
      obtain ⟨φ⟩ := nonempty_homology_iso_free_of_split
        (((Modules.pullback j).mapHomologicalComplex _).obj Pg) q (E (q - 1)) (E q) (E (q + 1))
        σ τ I Pm h₁ (by rw [hCg]; exact h₂) (by rw [hCg]; exact h₃)
        (by rw [hCg, hCg]; exact h₄)
      exact ⟨(restrictFunctorIsoPullback j).app _ ≪≫
        ((Pg.sc q).mapHomologyIso (Modules.pullback j)).symm ≪≫ φ⟩
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · refine isZero_of_iSup_eq_top _ V hV fun y' ↦ ?_
      have : IsEmpty (ULift.{u} (Fin (if (q : ℤ) = i then r else 0))) := by
        rw [ite_eq_right (by exact_mod_cast hq)]
        infer_instance
      exact (isZero_free_of_isEmpty _).of_iso (key y' q).some
    · exact isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun y' ↦ (V y').ι)
        (by simpa using hV) fun y' ↦ ⟨(key y' i).some ≪≫ eqToIso (by rw [ite_eq_left rfl])⟩
  · -- pull back to the spectrum of the local ring at a point of `Y'`
    intro h
    rintro _ ⟨y', rfl⟩
    set s := Y'.fromSpecStalk y'
    set x₀ := IsLocalRing.closedPoint (Y'.presheaf.stalk y')
    have hx (W : (Spec (Y'.presheaf.stalk y')).Opens) (hW : x₀ ∈ W) : W = ⊤ :=
      IsLocalRing.closed_point_mem_iff.mp hW
    let E (n : ℤ) := (Modules.pullback s).mapIso (eg n) ≪≫
      pullbackFreeIso s (ULift.{u} (Fin (rk n)))
    set Q := ((Modules.pullback s).mapHomologicalComplex _).obj Pg
    let hQ (q : ℤ) : Q.homology q ≅ (Modules.pullback s).obj (Pg.homology q) :=
      (Pg.sc q).mapHomologyIso (Modules.pullback s)
    have hzero (q : ℤ) (hq : q ≠ i) (hne : Nonempty (ULift.{u} (Fin (rk q)))) :
        IsZero (Q.homology q) := by
      have hq0 : 0 ≤ q := by
        obtain ⟨⟨a⟩⟩ := hne
        have := a.pos
        by_contra h'
        have := hrk q (Or.inl (by omega))
        omega
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq0
      exact ((Modules.pullback s).map_isZero (h.isZero n (by exact_mod_cast hq))).of_iso (hQ n)
    -- the cohomology in degree `i` pulls back to a free module
    have := h.isFiniteLocallyFreeOfRank
    obtain ⟨J, U, hU, eU⟩ :=
      IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (Pg.homology i) (r := r)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial : y' ∈ ⨆ j, U j)
    have hs : Set.range s ⊆ Set.range (U j).ι := by
      rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
      exact fun z hz ↦ hz.mem_open (U j).isOpen hj
    set s' := IsOpenImmersion.lift (U j).ι s hs
    have hfac : s' ≫ (U j).ι = s := IsOpenImmersion.lift_fac _ _ _
    let φ : (Modules.pullback s).obj (Pg.homology i) ≅
        SheafOfModules.free (ULift.{u} (Fin r)) :=
      ((Modules.pullbackCongr hfac).app _).symm ≪≫ ((Modules.pullbackComp s' (U j).ι).app _).symm ≪≫
        (Modules.pullback s').mapIso (((restrictFunctorIsoPullback (U j).ι).app _).symm ≪≫
          (eU j).some) ≪≫ pullbackFreeIso s' _
    have hrank := rankCondition_of_homology hx Q E d
      (fun n hn ↦ hN n (Or.inr (by exact_mod_cast hn))) i hzero (hQ i ≪≫ φ)
    have hfun : (fun n m ↦ freeMatrix ((E n).inv ≫ Q.d n m ≫ (E m).hom)) =
        fun n m ↦ (C n m).map (s ≫ g).appTop := by
      funext n m
      exact hCg n m s
    rw [hfun, Fintype.card_ulift, Fintype.card_fin] at hrank
    have := Scheme.RankCondition.of_map (s ≫ g) hrank
    rwa [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at this

end AlgebraicGeometry.Scheme.Modules
