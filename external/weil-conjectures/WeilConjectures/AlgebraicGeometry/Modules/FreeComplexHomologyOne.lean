/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexSplitDegree
public import WeilConjectures.LinearAlgebra.Matrix.KernelVectorOfMinor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Local freeness of the first cohomology of a finite free complex

Let `P` be a bounded complex of finite free `𝒪_Y`-modules in nonnegative degrees such that
`H⁰(g^* P) ≅ 𝒪_Z` for every `g : Z ⟶ Y`, and whose fibres `P ⊗ κ(y)` are exact in degrees `≥ 2`.
Then `H¹(P)` is finite locally free
(`AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.isFiniteLocallyFree_homology_one`).

This is the algebra behind cohomology and base change in top degree for families of curves
[Hartshorne, III.12.11], [Stacks, Tag 0BDJ]: no reducedness of `Y` is needed, because the
isomorphisms `H⁰(P|_W) ≅ 𝒪_W` over the opens `W` of `Y` produce, near every point, a global
cycle of degree `0` with a unit coordinate. Adding it as a differential in degree `-1` makes the
fibres exact in degrees `≤ 0`, and the complex splits near the point with free `H¹`.

## References

* [R. Hartshorne, *Algebraic Geometry*, III.12.11]
* [Stacks: Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **A cycle with a unit coordinate.** Let `Q` be a complex of free `𝒪_W`-modules with
`Q^{-1} = 0`, `Q^0 ≅ 𝒪^{ι₀}`, `Q^1 ≅ 𝒪^{ι₁}`, whose cohomology `H⁰(Q)` is isomorphic to `𝒪_W`.
If the matrix `B` of `d⁰` has an invertible minor of size `|ι₀| - 1`, then there is a vector
`w ∈ Γ(W, 𝒪)^{ι₀}` with `B w = 0` and a coordinate equal to `1`. -/
theorem exists_mulVec_eq_zero_and_eq_one_of_homology_iso_unit {W : Scheme.{u}}
    (Q : CochainComplex W.Modules ℤ) {ι₀ ι₁ : Type u} [Fintype ι₀]
    [DecidableEq ι₁] (hQ : IsZero (Q.X (-1)))
    (e₀ : Q.X 0 ≅ free (R := W.ringCatSheaf) ι₀) (e₁ : Q.X 1 ≅ free (R := W.ringCatSheaf) ι₁)
    (ψ : Q.homology 0 ≅ SheafOfModules.unit W.ringCatSheaf) {a : ℕ} (r : Fin a → ι₁)
    (c : Fin a → ι₀) (hB : IsUnit ((freeMatrix (e₀.inv ≫ Q.d 0 1 ≫ e₁.hom)).submatrix r c).det)
    (hcard : Fintype.card ι₀ = a + 1) :
    ∃ (w : ι₀ → Γ(W, ⊤)) (j : ι₀),
      (freeMatrix (e₀.inv ≫ Q.d 0 1 ≫ e₁.hom)).mulVec w = 0 ∧ w j = 1 := by
  classical
  have hd : Q.d (-1) 0 = 0 := hQ.eq_of_src _ _
  -- the cycle `u`, as a morphism from a free module of rank one
  let k : free (R := W.ringCatSheaf) PUnit.{u + 1} ⟶ free ι₀ :=
    (freeUniqueIso PUnit).hom ≫ ψ.inv ≫ (Q.isoHomologyπ (-1) 0 (by simp) hd).inv ≫
      Q.iCycles 0 ≫ e₀.hom
  have hk : Mono k := by
    dsimp only [k]
    infer_instance
  let u : ι₀ → Γ(W, ⊤) := fun i ↦ freeMatrix k i PUnit.unit
  have hku : k ≫ e₀.inv ≫ Q.d 0 1 ≫ e₁.hom = 0 := by
    simp [k]
  refine Matrix.exists_mulVec_eq_zero_and_eq_one_of_isUnit_det_submatrix _ r c hB hcard u ?_ ?_
  · funext i
    have := congrFun (congrFun (congrArg freeMatrix hku) i) PUnit.unit
    rw [freeMatrix_comp, freeMatrix_zero] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, u] using this
  · intro s hs
    let φ : free (R := W.ringCatSheaf) PUnit.{u + 1} ⟶ free PUnit.{u + 1} :=
      freeHomOfMatrix (Matrix.of fun _ _ ↦ s)
    have hφ : φ ≫ k = 0 := by
      refine freeMatrix_injective ?_
      rw [freeMatrix_comp, freeMatrix_zero]
      ext i p
      have := congrFun hs i
      simpa [φ, Matrix.mul_apply, u, mul_comm] using this
    have : φ = 0 := by
      rw [← cancel_mono k, hφ, zero_comp]
    have h := congrFun (congrFun (congrArg freeMatrix this) PUnit.unit) PUnit.unit
    simpa [φ] using h

set_option backward.isDefEq.respectTransparency false in
/-- **The first cohomology of a finite free complex is finite locally free.** Let `P` be a
bounded complex of finite free `𝒪_Y`-modules in degrees `[0, d]` such that `H⁰(g^* P) ≅ 𝒪_Z` for
every morphism `g : Z ⟶ Y`, and whose fibres `P ⊗ κ(y)` are exact in degrees `q ≥ 2`. Then
`H¹(P)` is finite locally free. -/
@[stacks 0BDJ]
theorem IsFiniteFreeComplex.isFiniteLocallyFree_homology_one {P : CochainComplex Y.Modules ℤ}
    {d : ℕ} (hP : IsFiniteFreeComplex P d)
    (h₀ : ∀ {Z : Scheme.{u}} (g : Z ⟶ Y),
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology 0 ≅
        SheafOfModules.unit Z.ringCatSheaf))
    (h₂ : ∀ (y : Y) (q : ℤ), 2 ≤ q → IsZero ((((Modules.pullback
      (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj P).homology q)) :
    (P.homology 1).IsFiniteLocallyFree := by
  classical
  obtain ⟨rk, hrk, ⟨e⟩⟩ := hP.exists_iso_free_of_rank_eq_zero
  set C : ∀ n m : ℤ, Matrix (ULift.{u} (Fin (rk m))) (ULift.{u} (Fin (rk n))) Γ(Y, ⊤) :=
    fun n m ↦ freeMatrix ((e n).inv ≫ P.d n m ≫ (e m).hom) with hCdef
  have hC (n m l : ℤ) : C m l * C n m = 0 := by
    simp only [hCdef]
    rw [← freeMatrix_comp]
    simp
  have key (y : Y) : ∃ V : Y.Opens, y ∈ V ∧ ∃ k : ℕ,
      Nonempty ((P.homology 1).restrict V.ι ≅ free (ULift.{u} (Fin k))) := by
    set g := Y.fromSpecResidueField y with hg
    have hκ : IsField (Y.residueField y) := Field.toIsField _
    -- the ranks of the differentials at `y`
    have F (q : ℤ) := finrank_homology_pullback_add_rank_add_rank e hκ g q
    have F₀ : _ + ((C 0 1).map g.appTop).rank + ((C (-1) 0).map g.appTop).rank = rk 0 := F 0
    have F₁ : _ + ((C 1 2).map g.appTop).rank + ((C 0 1).map g.appTop).rank = rk 1 := F 1
    have F₂ : _ + ((C 2 3).map g.appTop).rank + ((C 1 2).map g.appTop).rank = rk 2 := F 2
    have hfin₀ : Module.finrank (Y.residueField y) ((moduleSpecΓFunctor
        (R := Y.residueField y)).obj ((((Modules.pullback g).mapHomologicalComplex _).obj
          P).homology 0)) = 1 := by
      obtain ⟨ψ⟩ := h₀ g
      exact (finrank_moduleSpecΓFunctor_obj_free hκ
        (ψ ≪≫ (freeUniqueIso PUnit.{u + 1}).symm)).1.trans Fintype.card_unique
    have hfin₂ : Module.finrank (Y.residueField y) ((moduleSpecΓFunctor
        (R := Y.residueField y)).obj ((((Modules.pullback g).mapHomologicalComplex _).obj
          P).homology 2)) = 0 := by
      have := finite_moduleSpecΓFunctor_obj_homology_pullback hP.exists_iso_free hκ g 2
      exact (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).1 (h₂ y 2 le_rfl)
    have hm : ((C (-1) 0).map g.appTop).rank = 0 := by
      refine Nat.eq_zero_of_le_zero ((Matrix.rank_le_card_width _).trans ?_)
      simp [hrk (-1) (Or.inl (by norm_num))]
    set k := Module.finrank (Y.residueField y) ((moduleSpecΓFunctor
        (R := Y.residueField y)).obj ((((Modules.pullback g).mapHomologicalComplex _).obj
          P).homology 1)) with hk
    have r₀ : ((C 0 1).map g.appTop).rank + 1 = rk 0 := by
      have := F₀
      rw [hfin₀] at this
      omega
    have r₁ : ((C 0 1).map g.appTop).rank + ((C 1 2).map g.appTop).rank + k = rk 1 := by
      have := F₁
      omega
    have r₂ : ((C 1 2).map g.appTop).rank + ((C 2 3).map g.appTop).rank = rk 2 := by
      have := F₂
      rw [hfin₂] at this
      omega
    -- an invertible minor of size `rk 0 - 1` of the matrix of `d⁰` near `y`
    obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
    obtain ⟨r, c, hrc⟩ := (le_rank_map_appTop_iff (isField_Γ_Spec_residueField y) g x (C 0 1)
      (rk 0 - 1)).1 (by omega)
    rw [hg, Scheme.fromSpecResidueField_apply] at hrc
    set W := Y.basicOpen ((C 0 1).submatrix r c).det with hW
    set Q := ((Modules.pullback W.ι).mapHomologicalComplex _).obj P
    let E (n : ℤ) : Q.X n ≅ free (ULift.{u} (Fin (rk n))) :=
      (Modules.pullback W.ι).mapIso (e n) ≪≫ pullbackFreeIso W.ι _
    have hE (n m : ℤ) : freeMatrix ((E n).inv ≫ Q.d n m ≫ (E m).hom) = (C n m).map W.ι.appTop :=
      freeMatrix_pullback_d _ _ _ _
    have : IsEmpty (ULift.{u} (Fin (rk (-1)))) := by
      rw [hrk (-1) (Or.inl (by norm_num))]
      infer_instance
    have hQ : IsZero (Q.X (-1)) := (isZero_free_of_isEmpty _).of_iso (E (-1))
    obtain ⟨ψ⟩ := h₀ W.ι
    have hunit : IsUnit ((freeMatrix ((E 0).inv ≫ Q.d 0 1 ≫ (E 1).hom)).submatrix r c).det := by
      rw [hE, Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact Y.isUnit_ι_appTop_basicOpen _
    obtain ⟨w, j, hw, hwj⟩ := exists_mulVec_eq_zero_and_eq_one_of_homology_iso_unit Q hQ (E 0)
      (E 1) ψ r c hunit (by simp; omega)
    rw [hE] at hw
    -- splitting near `y` with the cycle `w` as incoming differential
    set yW : W.toScheme := ⟨y, hrc⟩
    have hrW (n m : ℤ) : (((C n m).map W.ι.appTop).map
        (W.toScheme.fromSpecResidueField yW).appTop).rank = ((C n m).map g.appTop).rank :=
      rank_map_appTop_restrict W yW (C n m)
    have hw₁ : ((Matrix.replicateCol PUnit.{1} w).map
        (W.toScheme.fromSpecResidueField yW).appTop).rank = 1 := by
      obtain ⟨xW⟩ : Nonempty (Spec (W.toScheme.residueField yW)) := inferInstance
      refine le_antisymm ((Matrix.rank_le_card_width _).trans (by simp)) ?_
      refine (le_rank_map_appTop_iff (isField_Γ_Spec_residueField yW) _ xW _ 1).2
        ⟨fun _ ↦ j, fun _ ↦ PUnit.unit, ?_⟩
      simp [Matrix.det_unique, hwj]
    obtain ⟨W', hyW', hsplit⟩ := Scheme.exists_opens_hasSplitHomology_of_rank_add_eq
      (Matrix.replicateCol PUnit.{1} w) ((C 0 1).map W.ι.appTop) ((C 1 2).map W.ι.appTop)
      ((C 2 3).map W.ι.appTop)
      (by rw [← Matrix.replicateCol_mulVec, hw, Matrix.replicateCol_zero])
      (by rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero _)])
      (by rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero _)]) (y := yW) (k := k)
      (by rw [hw₁, hrW]; simp; omega) (by rw [hrW, hrW]; simpa using r₁)
      (by rw [hrW, hrW]; simpa using r₂)
    set V : Y.Opens := W.ι ''ᵁ W' with hV
    have hVW : Set.range V.ι ⊆ Set.range W.ι := by
      rw [Opens.range_ι, Opens.range_ι]
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    set gV := IsOpenImmersion.lift W.ι V.ι hVW
    have hfac : gV ≫ W.ι = V.ι := IsOpenImmersion.lift_fac _ _ _
    have hgV : Set.range gV ⊆ W' := by
      rintro _ ⟨z, rfl⟩
      rw [← Scheme.Hom.preimage_image_eq W.ι W']
      change W.ι (gV z) ∈ W.ι ''ᵁ W'
      rw [← Scheme.Hom.comp_apply, hfac]
      exact z.2
    have hs := hsplit gV hgV
    rw [← map_appTop_comp, ← map_appTop_comp, hfac] at hs
    obtain ⟨I, Pm, σ, τ, s₁, s₂, s₃, s₄⟩ := hs.of_equiv Equiv.ulift.symm
    let E' (n : ℤ) := (Modules.pullback V.ι).mapIso (e n) ≪≫
      pullbackFreeIso V.ι (ULift.{u} (Fin (rk n)))
    have hE' (n m : ℤ) : freeMatrix ((E' n).inv ≫
        (((Modules.pullback V.ι).mapHomologicalComplex _).obj P).d n m ≫ (E' m).hom) =
        (C n m).map V.ι.appTop :=
      freeMatrix_pullback_d _ _ _ _
    obtain ⟨φ⟩ := nonempty_homology_iso_free_of_split
      (((Modules.pullback V.ι).mapHomologicalComplex _).obj P) 1 (E' (1 - 1)) (E' 1)
      (E' (1 + 1)) σ τ I Pm s₁ (by rw [hE']; exact s₂) (by rw [hE']; exact s₃)
      (by rw [hE', hE']; exact s₄)
    exact ⟨V, ⟨yW, hyW', rfl⟩, k, ⟨(restrictFunctorIsoPullback V.ι).app _ ≪≫
      ((P.sc 1).mapHomologyIso (Modules.pullback V.ι)).symm ≪≫ φ⟩⟩
  choose V hV k e' using key
  refine isFiniteLocallyFree_of_restrict_iso_free _ (fun y ↦ (V y).ι) ?_
    (fun y ↦ ULift.{u} (Fin (k y))) e'
  refine eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, ?_⟩
  rw [Scheme.Opens.opensRange_ι]
  exact hV y

end AlgebraicGeometry.Scheme.Modules
