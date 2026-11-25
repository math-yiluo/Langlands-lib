/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Gluing sections modulo a submodule with vanishing `H¹`

Let `ι : 𝒢 ⟶ ℒ` be a morphism of `𝒪_X`-modules on a scheme `X` separated over an affine
scheme, with `𝒢` quasi-coherent and `H¹(X, 𝒢) = 0`. Local sections `sᵢ` of `ℒ` over an affine
open cover `(Ωᵢ)` whose differences on the overlaps come from `𝒢` can be modified by sections of
`𝒢` so that they glue to a global section of `ℒ`.

This is the Čech form of the surjectivity of `H⁰(X, ℒ) → H⁰(X, ℒ / 𝒢)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_forall_exists_app_eq_sub_of_subsingleton_H_one`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- **Gluing modulo a submodule with vanishing `H¹`.** Let `X` be separated over an affine
scheme, `ι : 𝒢 ⟶ ℒ` a morphism of `𝒪_X`-modules with `𝒢` quasi-coherent and `H¹(X, 𝒢) = 0`,
and `(Ωᵢ)` an affine open cover of `X` such that `ι` is injective on the triple intersections.
If `sᵢ ∈ ℒ(Ωᵢ)` are sections whose differences on the double intersections lie in the image of
`𝒢`, then there is a global section `t` of `ℒ` with `t - sᵢ` in the image of `𝒢(Ωᵢ)` for
every `i`. -/
theorem exists_forall_exists_app_eq_sub_of_subsingleton_H_one (g : X ⟶ S) [IsSeparated g]
    [IsAffine S] {𝒢 ℒ : X.Modules} [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢]
    (ι : 𝒢 ⟶ ℒ) (hH : Subsingleton (𝒢.H 1)) {σ : Type u} (Ω : σ → X.Opens)
    (hΩ : ∀ i, IsAffineOpen (Ω i)) (hcov : iSup Ω = ⊤)
    (hinj : ∀ y : Fin 3 → σ, Function.Injective (ι.app (⨅ l, Ω (y l))))
    (s : ∀ i, Γ(ℒ, Ω i))
    (hs : ∀ y : Fin 2 → σ, ∃ c : Γ(𝒢, ⨅ l, Ω (y l)), ι.app _ c =
      ℒ.presheaf.map (homOfLE (iInf_le (fun l ↦ Ω (y l)) 1)).op (s (y 1)) -
        ℒ.presheaf.map (homOfLE (iInf_le (fun l ↦ Ω (y l)) 0)).op (s (y 0))) :
    ∃ t : Γ(ℒ, ⊤), ∀ i, ∃ b : Γ(𝒢, Ω i),
      ι.app _ b = ℒ.presheaf.map (homOfLE le_top).op t - s i := by
  classical
  choose c hc using hs
  set P := ((SheafOfModules.toSheaf _).obj 𝒢).obj
  -- the first Čech cohomology of the cover vanishes
  obtain ⟨e⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated g Ω hΩ hcov 𝒢 1
  have : Subsingleton ((TopCat.Sheaf.cechCohomologyFunctor Ω 1).obj
      ((SheafOfModules.toSheaf _).obj 𝒢)) := by
    have := e.toEquiv.subsingleton
    exact (cechComplexHomologyAddEquiv Ω 𝒢 1).symm.toEquiv.subsingleton
  have hex : ((TopCat.Presheaf.cechComplex Ω).obj P).ExactAt (0 + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (@AddCommGrpCat.isZero_of_subsingleton _ this)
  rw [TopCat.Presheaf.exactAt_cechComplex_iff Ω P 0] at hex
  have hιmap {O O' : X.Opens} (hO : O' ≤ O) (x : Γ(𝒢, O)) :
      ι.app O' (P.map (homOfLE hO).op x) = ℒ.presheaf.map (homOfLE hO).op (ι.app O x) :=
    Hom.app_presheaf_map _ _ _
  -- `c` is a cocycle
  obtain ⟨b, hb⟩ := hex c (by
    funext y
    refine hinj y ?_
    rw [TopCat.Presheaf.cechComplex_zero_apply, map_zero, TopCat.Presheaf.cechComplex_d_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, map_add, map_zsmul, hιmap, hc,
      map_sub, presheaf_map_homOfLE_map_homOfLE]
    change (-1 : ℤ) ^ 0 • (ℒ.presheaf.map (homOfLE _).op (s (y 2)) -
        ℒ.presheaf.map (homOfLE _).op (s (y 1))) +
      ((-1 : ℤ) ^ 1 • (ℒ.presheaf.map (homOfLE _).op (s (y 2)) -
        ℒ.presheaf.map (homOfLE _).op (s (y 0))) +
      (-1 : ℤ) ^ 2 • (ℒ.presheaf.map (homOfLE _).op (s (y 1)) -
        ℒ.presheaf.map (homOfLE _).op (s (y 0)))) = 0
    simp only [pow_zero, pow_one, neg_one_sq, one_smul, neg_smul]
    abel)
  -- the corrected sections agree on the overlaps
  have hle (i : σ) : Ω i ≤ ⨅ l : Fin 1, Ω ((fun _ ↦ i) l) := le_iInf fun _ ↦ le_rfl
  let b' (i : σ) : Γ(𝒢, Ω i) := P.map (homOfLE (hle i)).op (b fun _ ↦ i)
  have hcompat : TopCat.Presheaf.IsCompatible ((SheafOfModules.toSheaf _).obj ℒ).obj Ω
      fun i ↦ s i - ι.app _ (b' i) := by
    intro i j
    have hij : Ω i ⊓ Ω j ≤ ⨅ l, Ω (![i, j] l) := by
      refine le_iInf fun l ↦ ?_
      fin_cases l
      exacts [inf_le_left, inf_le_right]
    have h1 := congrArg (fun x ↦ ι.app _ (P.map (homOfLE hij).op x)) (congr_fun hb ![i, j])
    simp only [TopCat.Presheaf.cechComplex_d_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
      add_zero, map_add, map_zsmul, TopCat.Presheaf.map_homOfLE_map_homOfLE_apply] at h1
    rw [TopCat.Presheaf.map_homOfLE_apply_congr Ω P (k := 0) b (y := ![i, j] ∘ Fin.succAbove 0)
        (y' := fun _ ↦ j)
        (by funext l; fin_cases l; rfl) _ ((inf_le_right : Ω i ⊓ Ω j ≤ Ω j).trans (hle j)),
      TopCat.Presheaf.map_homOfLE_apply_congr Ω P (k := 0) b
        (y := ![i, j] ∘ (Fin.succ 0).succAbove) (y' := fun _ ↦ i)
        (by funext l; fin_cases l; rfl) _ ((inf_le_left : Ω i ⊓ Ω j ≤ Ω i).trans (hle i))] at h1
    simp only [hιmap, hc, map_sub, presheaf_map_homOfLE_map_homOfLE] at h1
    change (-1 : ℤ) ^ 0 • ℒ.presheaf.map (homOfLE _).op (ι.app _ (b fun _ ↦ j)) +
      (-1 : ℤ) ^ 1 • ℒ.presheaf.map (homOfLE _).op (ι.app _ (b fun _ ↦ i)) =
        ℒ.presheaf.map (homOfLE _).op (s j) - ℒ.presheaf.map (homOfLE _).op (s i) at h1
    simp only [pow_zero, pow_one, one_smul, neg_smul] at h1
    change ℒ.presheaf.map (homOfLE inf_le_left).op (s i - ι.app _ (b' i)) =
      ℒ.presheaf.map (homOfLE inf_le_right).op (s j - ι.app _ (b' j))
    simp only [b', map_sub, hιmap, presheaf_map_homOfLE_map_homOfLE]
    rw [← sub_eq_zero]
    have h3 := sub_eq_zero.mpr h1
    rw [← h3]
    abel
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' ((SheafOfModules.toSheaf _).obj ℒ) Ω ⊤
    (fun i ↦ homOfLE le_top) hcov.ge _ hcompat
  refine ⟨t, fun i ↦ ⟨-b' i, ?_⟩⟩
  rw [map_neg]
  have h := ht i
  change ℒ.presheaf.map (homOfLE le_top).op t = s i - ι.app _ (b' i) at h
  rw [h]
  abel

end AlgebraicGeometry.Scheme.Modules
