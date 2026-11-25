/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.RingTheory.Flat.Stability

/-!
# Flatness over the base: locality and pullbacks from a factor

* `AlgebraicGeometry.Scheme.Modules.isFlatOver_of_forall_exists_nhds`: flatness of a
  quasi-coherent module over the base is local on the source.
* `AlgebraicGeometry.Scheme.Modules.flat_sections_pullback_fst_of_flat_baseChange` and
  `AlgebraicGeometry.Scheme.Modules.flat_baseChange_of_flat_sections_pullback_fst`: for
  `Y ⟶ S ⟵ Z` with `S` affine, affine opens `W ⊆ Y`, `V ⊆ Z` and a quasi-coherent module `ℱ` on
  `Y`, the sections of `pr_Y^* ℱ` over affine opens of `pr_Y⁻¹ W ∩ pr_Z⁻¹ V` are flat over
  `Γ(Z, V)` if `Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W)` is, and conversely over `pr_Y⁻¹ W ∩ pr_Z⁻¹ V`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- **Flatness over the base is local.** Let `ℱ` be a quasi-coherent `𝒪_X`-module and
`f : X ⟶ T`. Suppose that for every affine open `V` of `T`, every point `x` of `f⁻¹ V` has an
open neighbourhood `N` such that the sections of `ℱ` over every affine open `U ⊆ N ∩ f⁻¹ V` are
flat over `Γ(T, V)`. Then `ℱ` is flat over `T`. -/
theorem isFlatOver_of_forall_exists_nhds (f : X ⟶ T) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (h : ∀ (V : T.affineOpens) (x : X), x ∈ f ⁻¹ᵁ V.1 → ∃ N : X.Opens, x ∈ N ∧
      ∀ (U : X.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1), U.1 ≤ N →
        letI : Module Γ(T, V.1) Γ(ℱ, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
        Module.Flat Γ(T, V.1) Γ(ℱ, U.1)) :
    ℱ.IsFlatOver f := by
  intro V W e
  let : Algebra Γ(T, V.1) Γ(X, W.1) := (f.appLE V.1 W.1 e).hom.toAlgebra
  let : Module Γ(T, V.1) Γ(ℱ, W.1) := Module.compHom _ (f.appLE V.1 W.1 e).hom
  have : IsScalarTower Γ(T, V.1) Γ(X, W.1) Γ(ℱ, W.1) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  choose N hxN hN using fun x : W.1 ↦ h V x (e x.2)
  choose g hgN hxg using fun x : W.1 ↦ W.2.exists_basicOpen_le ⟨x.1, hxN x⟩ x.2
  let s : Set Γ(X, W.1) := Set.range g
  have spn : Ideal.span s = ⊤ := by
    rw [← W.2.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun r ↦ X.basicOpen_le _) fun x hx ↦ ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxg ⟨x, hx⟩⟩
  let Mₛ (r : s) : Type u := Γ(ℱ, X.basicOpen r.1)
  have hle (r : s) : X.basicOpen r.1 ≤ f ⁻¹ᵁ V.1 := (X.basicOpen_le _).trans e
  let (r : s) : Module Γ(X, W.1) (Mₛ r) :=
    Module.compHom _ (algebraMap Γ(X, W.1) Γ(X, X.basicOpen r.1))
  let (r : s) : Module Γ(T, V.1) (Mₛ r) := Module.compHom _ (f.appLE V.1 _ (hle r)).hom
  have (r : s) : IsScalarTower Γ(T, V.1) Γ(X, W.1) (Mₛ r) := by
    refine ⟨fun a b m ↦ ?_⟩
    change (algebraMap Γ(X, W.1) Γ(X, X.basicOpen r.1) ((f.appLE V.1 W.1 e).hom a * b)) • m =
      (f.appLE V.1 _ (hle r)).hom a • (algebraMap Γ(X, W.1) Γ(X, X.basicOpen r.1) b • m)
    rw [map_mul, mul_smul]
    congr 1
    rw [← f.appLE_map e (homOfLE (X.basicOpen_le r.1)).op]
    rfl
  let gₛ (r : s) : Γ(ℱ, W.1) →ₗ[Γ(X, W.1)] Mₛ r :=
    { toFun := ℱ.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
      map_add' := map_add _
      map_smul' := map_smul ℱ _ }
  have (r : s) : IsLocalizedModule.Away r.1 (gₛ r) := isLocalizedModule_basicOpen ℱ W.2 r.1
  refine Module.flat_of_isLocalized_span Γ(X, W.1) Γ(ℱ, W.1) s spn Mₛ gₛ fun r ↦ ?_
  obtain ⟨_, ⟨x, rfl⟩⟩ := r
  exact hN x ⟨_, W.2.basicOpen _⟩ (hle _) (hgN x)

section PullbackFst

variable {S Y Z : Scheme.{u}} [IsAffine S] (gY : Y ⟶ S) (gZ : Z ⟶ S) (ℱ : Y.Modules)
  [ℱ.IsQuasicoherent] {W : Y.Opens} {V : Z.Opens}

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of a pullback from a factor, flat case.** Let `gY : Y ⟶ S`, `gZ : Z ⟶ S` with `S`
affine, `ℱ` a quasi-coherent `𝒪_Y`-module and `W ⊆ Y`, `V ⊆ Z` affine opens. If
`Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W)` is flat over `Γ(Z, V)`, then for every affine open
`U ⊆ pr_Y⁻¹ W ∩ pr_Z⁻¹ V` of `Y ×_S Z` the sections of `pr_Y^* ℱ` over `U` are flat over
`Γ(Z, V)`. -/
theorem flat_sections_pullback_fst_of_flat_baseChange
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    {U : (Limits.pullback gY gZ).Opens} (hU : IsAffineOpen U)
    (hUle : U ≤ pullback.fst gY gZ ⁻¹ᵁ W ⊓ pullback.snd gY gZ ⁻¹ᵁ V)
    (hflat : letI := (gZ.appLE ⊤ V le_top).hom.toAlgebra
      letI : Module Γ(S, ⊤) Γ(ℱ, W) := Module.compHom _ (gY.appLE ⊤ W le_top).hom
      Module.Flat Γ(Z, V) (Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W))) :
    letI : Module Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj ℱ, U) :=
      Module.compHom _ ((pullback.snd gY gZ).appLE V U (hUle.trans inf_le_right)).hom
    Module.Flat Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj ℱ, U) := by
  set π := pullback.fst gY gZ
  set f := pullback.snd gY gZ
  set Ω := π ⁻¹ᵁ W ⊓ f ⁻¹ᵁ V
  have hΩ : IsAffineOpen Ω := isAffineOpen_preimage_inf_preimage_pullback gY gZ hW hV
  have hUV : U ≤ f ⁻¹ᵁ V := hUle.trans inf_le_right
  have hUW' : U ≤ π ⁻¹ᵁ W := hUle.trans inf_le_left
  let : Algebra Γ(S, ⊤) Γ(Y, W) := (gY.appLE ⊤ W le_top).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Z, V) := (gZ.appLE ⊤ V le_top).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) := (π.appLE W Ω inf_le_left).hom.toAlgebra
  let : Algebra Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := (f.appLE V Ω inf_le_right).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Limits.pullback gY gZ, Ω) :=
    (gY.appLE ⊤ W le_top ≫ π.appLE W Ω inf_le_left).hom.toAlgebra
  let : Algebra Γ(Limits.pullback gY gZ, Ω) Γ(Limits.pullback gY gZ, U) :=
    ((Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op).hom.toAlgebra
  let : Algebra Γ(Z, V) Γ(Limits.pullback gY gZ, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(Limits.pullback gY gZ, U) := (π.appLE W U hUW').hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(S, ⊤) Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (gY.appLE ⊤ W le_top ≫ π.appLE W Ω inf_le_left) r =
      (gZ.appLE ⊤ V le_top ≫ f.appLE V Ω inf_le_right) r
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [pullback.condition, π, f]
  have : IsScalarTower Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) Γ(Limits.pullback gY gZ, U) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (f.appLE V U hUV) r = (f.appLE V Ω inf_le_right ≫
      (Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op) r
    rw [Scheme.Hom.appLE_map]
  have : IsScalarTower Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) Γ(Limits.pullback gY gZ, U) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (π.appLE W U hUW') r = (π.appLE W Ω inf_le_left ≫
      (Limits.pullback gY gZ).presheaf.map (homOfLE hUle).op) r
    rw [Scheme.Hom.appLE_map]
  -- `Γ(Ω) = Γ(Y, W) ⊗[Γ(S, ⊤)] Γ(Z, V)`
  have hpush : Algebra.IsPushout Γ(S, ⊤) Γ(Y, W) Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback gY gZ)
      (le_top : V ≤ gZ ⁻¹ᵁ ⊤) (le_top : W ≤ gY ⁻¹ᵁ ⊤) (UY := Ω) rfl (isAffineOpen_top _) hV hW
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have hpush' := hpush.symm
  -- the sections of `π^* ℱ` over `U` are `Γ(U) ⊗[Γ(Ω)] (Γ(Ω) ⊗[Γ(W)] Γ(ℱ, W))`
  obtain ⟨e, -⟩ := exists_linearEquiv_pullback_sections π ℱ hW hU hUW'
  let : Module Γ(S, ⊤) Γ(ℱ, W) := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(Y, W))
  have : IsScalarTower Γ(S, ⊤) Γ(Y, W) Γ(ℱ, W) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  have hN : Module.Flat Γ(Z, V) (Γ(Limits.pullback gY gZ, Ω) ⊗[Γ(Y, W)] Γ(ℱ, W)) :=
    @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat (Algebra.IsPushout.cancelBaseChange Γ(S, ⊤)
      Γ(Z, V) Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) Γ(ℱ, W))
  have hΩU : Module.Flat Γ(Limits.pullback gY gZ, Ω) Γ(Limits.pullback gY gZ, U) :=
    Scheme.Hom.flat_appLE (𝟙 (Limits.pullback gY gZ)) hΩ hU hUle
  have := Module.Flat.tensorProduct_of_flat Γ(Z, V) Γ(Limits.pullback gY gZ, Ω)
    Γ(Limits.pullback gY gZ, U) (Γ(Limits.pullback gY gZ, Ω) ⊗[Γ(Y, W)] Γ(ℱ, W))
  let : Module Γ(Z, V) Γ((Modules.pullback π).obj ℱ, U) :=
    Module.compHom _ (f.appLE V U hUV).hom
  have : IsScalarTower Γ(Z, V) Γ(Limits.pullback gY gZ, U) Γ((Modules.pullback π).obj ℱ, U) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.of_linearEquiv (((AlgebraTensorModule.cancelBaseChange Γ(Y, W)
    Γ(Limits.pullback gY gZ, Ω) Γ(Limits.pullback gY gZ, U) Γ(Limits.pullback gY gZ, U)
    Γ(ℱ, W)).trans e).restrictScalars Γ(Z, V)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of a pullback from a factor, converse.** In the situation of
`flat_sections_pullback_fst_of_flat_baseChange`, if the sections of `pr_Y^* ℱ` over
`pr_Y⁻¹ W ∩ pr_Z⁻¹ V` are flat over `Γ(Z, V)`, then so is `Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W)`. -/
theorem flat_baseChange_of_flat_sections_pullback_fst
    (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (hflat : letI : Module Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj ℱ,
        pullback.fst gY gZ ⁻¹ᵁ W ⊓ pullback.snd gY gZ ⁻¹ᵁ V) :=
      Module.compHom _ ((pullback.snd gY gZ).appLE V
        (pullback.fst gY gZ ⁻¹ᵁ W ⊓ pullback.snd gY gZ ⁻¹ᵁ V) inf_le_right).hom
      Module.Flat Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gY gZ)).obj ℱ,
        pullback.fst gY gZ ⁻¹ᵁ W ⊓ pullback.snd gY gZ ⁻¹ᵁ V)) :
    letI := (gZ.appLE ⊤ V le_top).hom.toAlgebra
    letI : Module Γ(S, ⊤) Γ(ℱ, W) := Module.compHom _ (gY.appLE ⊤ W le_top).hom
    Module.Flat Γ(Z, V) (Γ(Z, V) ⊗[Γ(S, ⊤)] Γ(ℱ, W)) := by
  set π := pullback.fst gY gZ
  set f := pullback.snd gY gZ
  set Ω := π ⁻¹ᵁ W ⊓ f ⁻¹ᵁ V
  have hΩ : IsAffineOpen Ω := isAffineOpen_preimage_inf_preimage_pullback gY gZ hW hV
  let : Algebra Γ(S, ⊤) Γ(Y, W) := (gY.appLE ⊤ W le_top).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Z, V) := (gZ.appLE ⊤ V le_top).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) := (π.appLE W Ω inf_le_left).hom.toAlgebra
  let : Algebra Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := (f.appLE V Ω inf_le_right).hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(Limits.pullback gY gZ, Ω) :=
    (gY.appLE ⊤ W le_top ≫ π.appLE W Ω inf_le_left).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Y, W) Γ(Limits.pullback gY gZ, Ω) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(S, ⊤) Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (gY.appLE ⊤ W le_top ≫ π.appLE W Ω inf_le_left) r =
      (gZ.appLE ⊤ V le_top ≫ f.appLE V Ω inf_le_right) r
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [pullback.condition, π, f]
  have hpush : Algebra.IsPushout Γ(S, ⊤) Γ(Y, W) Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback gY gZ)
      (le_top : V ≤ gZ ⁻¹ᵁ ⊤) (le_top : W ≤ gY ⁻¹ᵁ ⊤) (UY := Ω) rfl (isAffineOpen_top _) hV hW
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have hpush' := hpush.symm
  obtain ⟨e, -⟩ := exists_linearEquiv_pullback_sections π ℱ hW hΩ inf_le_left
  let : Module Γ(S, ⊤) Γ(ℱ, W) := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(Y, W))
  have : IsScalarTower Γ(S, ⊤) Γ(Y, W) Γ(ℱ, W) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  let : Module Γ(Z, V) Γ((Modules.pullback π).obj ℱ, Ω) :=
    Module.compHom _ (f.appLE V Ω inf_le_right).hom
  have : IsScalarTower Γ(Z, V) Γ(Limits.pullback gY gZ, Ω) Γ((Modules.pullback π).obj ℱ, Ω) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hflat
    ((Algebra.IsPushout.cancelBaseChange Γ(S, ⊤) Γ(Z, V) Γ(Y, W) Γ(Limits.pullback gY gZ, Ω)
      Γ(ℱ, W)).symm.trans (e.restrictScalars Γ(Z, V)))

end PullbackFst

end AlgebraicGeometry.Scheme.Modules
