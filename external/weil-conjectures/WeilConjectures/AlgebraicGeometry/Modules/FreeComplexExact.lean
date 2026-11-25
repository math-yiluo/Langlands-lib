/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exactness of a complex of finite free modules from invertible minors

Let `Q` be a cochain complex of `𝒪_Y`-modules whose terms are free of finite rank, with
differentials given by matrices of global functions. If in degree `q` the incoming matrix has an
invertible `a × a` minor and the outgoing matrix an invertible `b × b` minor with `a + b` the rank
of `Q^q`, then `H^q(Q) = 0`. Over every open `W` the sections of the complex form a complex of
free `Γ(Y, W)`-modules with the restricted matrices, which is exact by linear algebra
(`Matrix.exists_mulVec_eq_of_isUnit_det_submatrix`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.freeSectionsEquivOpens`: coordinates of the sections over an
  open of a free module of finite rank.
- `AlgebraicGeometry.Scheme.Modules.freeSectionsEquivOpens_app`: a morphism of free modules acts
  on these coordinates by its restricted matrix.
- `AlgebraicGeometry.Scheme.Modules.isZero_homology_of_isUnit_det_submatrix`: the vanishing of
  `H^q(Q)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules Matrix

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

lemma freeπ_app_ιFree_app_opens (W : Y.Opens) {I : Type u} [DecidableEq I] (i j : I)
    (a : Γ(Y, W)) :
    Hom.app (freeπ j) W (Hom.app (ιFree (R := Y.ringCatSheaf) (I := I) i) W a) =
      if i = j then a else 0 := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, ιFree_freeπ]
  split_ifs <;> rfl

/-- The `Γ(Y, W)`-linear coordinates `Γ(W, 𝒪_Y^{(I)}) ≃ Γ(Y, W)^I` of the sections over an
open `W` of a free module of finite rank. -/
noncomputable def freeSectionsEquivOpens (W : Y.Opens) (I : Type u) [Fintype I]
    [DecidableEq I] :
    Γ(free (R := Y.ringCatSheaf) I, W) ≃ₗ[Γ(Y, W)] (I → Γ(Y, W)) where
  toFun x i := Hom.app (freeπ i) W x
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp
  invFun c := ∑ i, Hom.app (ιFree (R := Y.ringCatSheaf) i) W (c i)
  left_inv x := by
    dsimp only
    simp_rw [← ConcreteCategory.comp_apply, ← Hom.comp_app]
    rw [← Hom.sum_app_apply, sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    dsimp only
    rw [map_sum, Finset.sum_eq_single j (fun i _ hi ↦ ?_) (by simp)]
    · rw [freeπ_app_ιFree_app_opens, ite_eq_left rfl]
    · rw [freeπ_app_ιFree_app_opens, ite_eq_right hi]

/-- An endomorphism of `𝒪_Y` multiplies sections over `W` by the restriction of its value at
`1`. -/
lemma unit_hom_app_opens (e : Modules.unit Y ⟶ Modules.unit Y) (W : Y.Opens) (c : Γ(Y, W)) :
    Hom.app e W c = c * Y.presheaf.map (homOfLE le_top).op (Hom.app e ⊤ (1 : Γ(Y, ⊤))) := by
  have h1 : Hom.app e W c = c • Hom.app e W (1 : Γ(Y, W)) := by
    rw [← Hom.app_smul]
    congr 1
    exact (mul_one c).symm
  rw [h1]
  congr 1
  have h2 := Hom.app_presheaf_map e (homOfLE (le_top : W ≤ ⊤)) (1 : Γ(Y, ⊤))
  rw [show (Modules.unit Y).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(Y, ⊤)) =
    (1 : Γ(Y, W)) from map_one (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom] at h2
  exact h2

/-- In the coordinates `freeSectionsEquivOpens`, a morphism of free modules acts on sections over
`W` as multiplication by its matrix, restricted to `W`. -/
lemma freeSectionsEquivOpens_app (W : Y.Opens) {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (φ : free (R := Y.ringCatSheaf) I ⟶ free J)
    (x : Γ(free I, W)) :
    freeSectionsEquivOpens W J (Hom.app φ W x) =
      (freeMatrix φ).map (Y.presheaf.map (homOfLE le_top).op).hom *ᵥ
        freeSectionsEquivOpens W I x := by
  obtain ⟨c, rfl⟩ := (freeSectionsEquivOpens W I).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change Hom.app (freeπ j) W (Hom.app φ W
    (∑ i, Hom.app (ιFree (R := Y.ringCatSheaf) i) W (c i))) = _
  rw [map_sum, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change Hom.app (ιFree i ≫ φ ≫ freeπ j) W (c i) = _
  rw [unit_hom_app_opens, mul_comm]
  rfl

/-- **Vanishing of the cohomology of a complex of finite free modules.** Let `Q` be a cochain
complex of `𝒪_Y`-modules with `Q^n ≅ 𝒪_Y^{r_n}`. If the matrix of `d^{q-1}` has an invertible
`a × a` minor and the matrix of `d^q` an invertible `b × b` minor, with `a + b = r_q`, then
`H^q(Q) = 0`. -/
theorem isZero_homology_of_isUnit_det_submatrix (Q : CochainComplex Y.Modules ℤ) {r : ℤ → ℕ}
    (e : ∀ n, Q.X n ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n)))) (q : ℤ)
    {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e₁ : α → ULift.{u} (Fin (r q))) (e₀ : α → ULift.{u} (Fin (r (q - 1))))
    (hA : IsUnit ((freeMatrix ((e (q - 1)).inv ≫ Q.d (q - 1) q ≫ (e q).hom)).submatrix
      e₁ e₀).det)
    (f₂ : β → ULift.{u} (Fin (r (q + 1)))) (f₁ : β → ULift.{u} (Fin (r q)))
    (hB : IsUnit ((freeMatrix ((e q).inv ≫ Q.d q (q + 1) ≫ (e (q + 1)).hom)).submatrix
      f₂ f₁).det)
    (hcard : Fintype.card α + Fintype.card β = r q) : IsZero (Q.homology q) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' Q (q - 1) q (q + 1) (by simp) (by simp),
    ShortComplex.exact_iff_epi_kernel_lift]
  set S := Q.sc' (q - 1) q (q + 1)
  set D₀ := (e (q - 1)).inv ≫ Q.d (q - 1) q ≫ (e q).hom
  set D₁ := (e q).inv ≫ Q.d q (q + 1) ≫ (e (q + 1)).hom
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ⟨W, le_rfl, hx, ?_⟩
  set ρ := (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  set A := (freeMatrix D₀).map ρ
  set B := (freeMatrix D₁).map ρ
  set cW := fun n ↦ freeSectionsEquivOpens W (ULift.{u} (Fin (r n)))
  -- coordinates of the sections of the terms of `Q` over `W`
  have hcoord (n m : ℤ) (D : free (R := Y.ringCatSheaf) (ULift.{u} (Fin (r n))) ⟶
      free (ULift.{u} (Fin (r m)))) (hD : D = (e n).inv ≫ Q.d n m ≫ (e m).hom)
      (z : Γ(Q.X n, W)) :
      cW m (Hom.app (e m).hom W (Hom.app (Q.d n m) W z)) =
        (freeMatrix D).map ρ *ᵥ cW n (Hom.app (e n).hom W z) := by
    rw [← freeSectionsEquivOpens_app, hD]
    have h : Hom.app (e n).inv W (Hom.app (e n).hom W z) = z := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
      rfl
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, h]
    rfl
  have hBA : B * A = 0 := by
    suffices key : ∀ w, (B * A) *ᵥ w = 0 by
      ext i j
      simpa using congrFun (key (Pi.single j 1)) i
    intro w
    obtain ⟨z, hz⟩ := (cW (q - 1)).surjective w
    obtain ⟨z, rfl⟩ := (appLinearEquivOfIso (e (q - 1)) W).surjective z
    rw [← Matrix.mulVec_mulVec, ← hz]
    change B *ᵥ (A *ᵥ cW (q - 1) (Hom.app (e (q - 1)).hom W z)) = 0
    rw [← hcoord (q - 1) q D₀ rfl, ← hcoord q (q + 1) D₁ rfl]
    rw [← ConcreteCategory.comp_apply (Hom.app (Q.d (q - 1) q) W), ← Hom.comp_app,
      Q.d_comp_d, Hom.zero_app]
    simp
  -- the section `y` of the kernel of `d^q`
  set v := (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map (kernel.ι S.g) y
  have hv : Hom.app (Q.d q (q + 1)) W v = 0 := by
    have := (range_map_kernelι W S.g).le ⟨y, rfl⟩
    exact this
  have hBv : B *ᵥ cW q (Hom.app (e q).hom W v) = 0 := by
    rw [← hcoord q (q + 1) D₁ rfl, hv, map_zero, map_zero]
  have hA' : IsUnit (A.submatrix e₁ e₀).det := by
    have h := hA.map ρ
    rwa [RingHom.map_det] at h
  have hB' : IsUnit (B.submatrix f₂ f₁).det := by
    have h := hB.map ρ
    rwa [RingHom.map_det] at h
  obtain ⟨w, hw⟩ := Matrix.exists_mulVec_eq_of_isUnit_det_submatrix A B hBA e₁ e₀ hA' f₂ f₁ hB'
    (by simpa using hcard) hBv
  set z := Hom.app (e (q - 1)).inv W ((cW (q - 1)).symm w)
  refine ⟨z, ?_⟩
  refine injective_map_kernelι W S.g ?_
  change (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map (kernel.lift S.g S.f S.zero ≫
    kernel.ι S.g) z = (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map (kernel.ι S.g)
      ((kernel S.g).presheaf.map (homOfLE le_rfl).op y)
  rw [kernel.lift_ι, presheaf_map_id_apply]
  change Hom.app (Q.d (q - 1) q) W z = v
  apply (cW q).injective.comp (appLinearEquivOfIso (e q) W).injective
  change cW q (Hom.app (e q).hom W (Hom.app (Q.d (q - 1) q) W z)) =
    cW q (Hom.app (e q).hom W v)
  rw [hcoord (q - 1) q D₀ rfl, ← hw]
  congr 1
  change cW (q - 1) (Hom.app ((e (q - 1)).inv ≫ (e (q - 1)).hom) W _) = w
  rw [Iso.inv_hom_id, Hom.id_app]
  exact (cW (q - 1)).apply_symm_apply w

end AlgebraicGeometry.Scheme.Modules
