/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.RingTheory.Flat.Stability
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Flatness of a module over the base is local

For a quasi-coherent `𝒪_X`-module `ℱ` and `f : X ⟶ T`, flatness of `ℱ` over `T`
(`AlgebraicGeometry.Scheme.Modules.IsFlatOver`) is a condition on all pairs of affine opens
`U ⊆ f⁻¹ V`. It suffices to check it on the affine opens contained in the members of an open
cover of each `f⁻¹ V`: the sections over an arbitrary affine open `U` are glued from their
localizations at a family of functions generating the unit ideal
(`Module.flat_of_isLocalized_span`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isFlatOver_of_forall_exists`
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
theorem isFlatOver_of_forall_exists (f : X ⟶ T) (ℱ : X.Modules) [ℱ.IsQuasicoherent]
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


set_option backward.isDefEq.respectTransparency false in
/-- **Sections of a pullback from a factor of a product over a field.** Let `W` and `Z` be schemes
over a field `K`, with projections `π : W ×_K Z ⟶ W` and `f : W ×_K Z ⟶ Z`, and let `ℱ` be a
quasi-coherent `𝒪_W`-module. For affine opens `U_W ⊆ W`, `V ⊆ Z` and an affine open
`U ⊆ π⁻¹ U_W ∩ f⁻¹ V`, the sections of `π^* ℱ` over `U` are flat over `Γ(Z, V)`. -/
theorem flat_sections_pullback_fst {K : Type u} [Field K] {W Z : Scheme.{u}}
    (gW : W ⟶ Spec (.of K)) (gZ : Z ⟶ Spec (.of K)) (ℱ : W.Modules) [ℱ.IsQuasicoherent]
    {UW : W.Opens} (hUW : IsAffineOpen UW) {V : Z.Opens} (hV : IsAffineOpen V)
    {U : (Limits.pullback gW gZ).Opens} (hU : IsAffineOpen U)
    (hUle : U ≤ pullback.fst gW gZ ⁻¹ᵁ UW ⊓ pullback.snd gW gZ ⁻¹ᵁ V) :
    letI : Module Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gW gZ)).obj ℱ, U) :=
      Module.compHom _ ((pullback.snd gW gZ).appLE V U (hUle.trans inf_le_right)).hom
    Module.Flat Γ(Z, V) Γ((Modules.pullback (Limits.pullback.fst gW gZ)).obj ℱ, U) := by
  set π := pullback.fst gW gZ
  set f := pullback.snd gW gZ
  set Ω := π ⁻¹ᵁ UW ⊓ f ⁻¹ᵁ V
  have hΩ : IsAffineOpen Ω := isAffineOpen_preimage_inf_preimage_pullback gW gZ hUW hV
  have hUV : U ≤ f ⁻¹ᵁ V := hUle.trans inf_le_right
  have hUW' : U ≤ π ⁻¹ᵁ UW := hUle.trans inf_le_left
  -- the ring maps `Γ(K) → Γ(W, U_W)`, `Γ(K) → Γ(Z, V)`, `→ Γ(Ω) → Γ(U)`
  let : Algebra Γ(Spec (.of K), ⊤) Γ(W, UW) := (gW.appLE ⊤ UW le_top).hom.toAlgebra
  let : Algebra Γ(Spec (.of K), ⊤) Γ(Z, V) := (gZ.appLE ⊤ V le_top).hom.toAlgebra
  let : Algebra Γ(W, UW) Γ(Limits.pullback gW gZ, Ω) := (π.appLE UW Ω inf_le_left).hom.toAlgebra
  let : Algebra Γ(Z, V) Γ(Limits.pullback gW gZ, Ω) := (f.appLE V Ω inf_le_right).hom.toAlgebra
  let : Algebra Γ(Spec (.of K), ⊤) Γ(Limits.pullback gW gZ, Ω) :=
    (gW.appLE ⊤ UW le_top ≫ π.appLE UW Ω inf_le_left).hom.toAlgebra
  let : Algebra Γ(Limits.pullback gW gZ, Ω) Γ(Limits.pullback gW gZ, U) :=
    ((Limits.pullback gW gZ).presheaf.map (homOfLE hUle).op).hom.toAlgebra
  let : Algebra Γ(Z, V) Γ(Limits.pullback gW gZ, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(W, UW) Γ(Limits.pullback gW gZ, U) := (π.appLE UW U hUW').hom.toAlgebra
  have : IsScalarTower Γ(Spec (.of K), ⊤) Γ(W, UW) Γ(Limits.pullback gW gZ, Ω) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Spec (.of K), ⊤) Γ(Z, V) Γ(Limits.pullback gW gZ, Ω) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (gW.appLE ⊤ UW le_top ≫ π.appLE UW Ω inf_le_left) r =
      (gZ.appLE ⊤ V le_top ≫ f.appLE V Ω inf_le_right) r
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [pullback.condition, π, f]
  have : IsScalarTower Γ(Z, V) Γ(Limits.pullback gW gZ, Ω) Γ(Limits.pullback gW gZ, U) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (f.appLE V U hUV) r = (f.appLE V Ω inf_le_right ≫
      (Limits.pullback gW gZ).presheaf.map (homOfLE hUle).op) r
    rw [Scheme.Hom.appLE_map]
  have : IsScalarTower Γ(W, UW) Γ(Limits.pullback gW gZ, Ω) Γ(Limits.pullback gW gZ, U) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change (π.appLE UW U hUW') r = (π.appLE UW Ω inf_le_left ≫
      (Limits.pullback gW gZ).presheaf.map (homOfLE hUle).op) r
    rw [Scheme.Hom.appLE_map]
  -- `Γ(Ω) = Γ(W, U_W) ⊗[K] Γ(Z, V)`
  have hpush : Algebra.IsPushout Γ(Spec (.of K), ⊤) Γ(W, UW) Γ(Z, V)
      Γ(Limits.pullback gW gZ, Ω) := by
    have hiso := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback gW gZ)
      (le_top : V ≤ gZ ⁻¹ᵁ ⊤) (le_top : UW ≤ gW ⁻¹ᵁ ⊤) (UY := Ω) rfl (isAffineOpen_top _) hV hUW
    exact CommRingCat.isPushout_iff_isPushout.mp ((isIso_pushoutSection_iff ..).mp hiso)
  have hpush' := hpush.symm
  -- the sections of `π^* ℱ` over `U` are `Γ(U) ⊗[Γ(Ω)] (Γ(Ω) ⊗[Γ(U_W)] Γ(ℱ, U_W))`
  obtain ⟨e, -⟩ := exists_linearEquiv_pullback_sections π ℱ hUW hU hUW'
  let : Module Γ(Spec (.of K), ⊤) Γ(ℱ, UW) :=
    Module.compHom _ (algebraMap Γ(Spec (.of K), ⊤) Γ(W, UW))
  have : IsScalarTower Γ(Spec (.of K), ⊤) Γ(W, UW) Γ(ℱ, UW) := ⟨fun a b m ↦ mul_smul _ _ _⟩
  let := (isField_Γ_Spec (R := .of K) (Field.toIsField K)).toField
  have hN : Module.Flat Γ(Z, V) (Γ(Limits.pullback gW gZ, Ω) ⊗[Γ(W, UW)] Γ(ℱ, UW)) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange Γ(Spec (.of K), ⊤) Γ(Z, V)
      Γ(W, UW) Γ(Limits.pullback gW gZ, Ω) Γ(ℱ, UW))
  have hΩU : Module.Flat Γ(Limits.pullback gW gZ, Ω) Γ(Limits.pullback gW gZ, U) := by
    have := Scheme.Hom.flat_appLE (𝟙 (Limits.pullback gW gZ)) hΩ hU hUle
    exact this
  have := Module.Flat.tensorProduct_of_flat Γ(Z, V) Γ(Limits.pullback gW gZ, Ω)
    Γ(Limits.pullback gW gZ, U) (Γ(Limits.pullback gW gZ, Ω) ⊗[Γ(W, UW)] Γ(ℱ, UW))
  let : Module Γ(Z, V) Γ((Modules.pullback π).obj ℱ, U) :=
    Module.compHom _ (f.appLE V U hUV).hom
  have : IsScalarTower Γ(Z, V) Γ(Limits.pullback gW gZ, U) Γ((Modules.pullback π).obj ℱ, U) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.of_linearEquiv (((AlgebraTensorModule.cancelBaseChange Γ(W, UW)
    Γ(Limits.pullback gW gZ, Ω) Γ(Limits.pullback gW gZ, U) Γ(Limits.pullback gW gZ, U)
    Γ(ℱ, UW)).trans e).restrictScalars Γ(Z, V)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Twists of pullbacks from a factor are flat over the other factor.** Let `W`, `Z` be schemes
over a field `K`, `ℱ` a quasi-coherent module on `W` and `L` an invertible module on
`W ×_K Z`. Then `pr_W^* ℱ ⊗ L` is flat over `Z`. -/
theorem isFlatOver_pullback_fst_tensorObj {K : Type u} [Field K] {W Z : Scheme.{u}}
    (gW : W ⟶ Spec (.of K)) (gZ : Z ⟶ Spec (.of K)) (ℱ : W.Modules) [ℱ.IsQuasicoherent]
    (L : (Limits.pullback gW gZ).Modules) [L.IsInvertible] :
    (MonoidalCategory.tensorObj ((Modules.pullback (Limits.pullback.fst gW gZ)).obj ℱ) L).IsFlatOver
      (Limits.pullback.snd gW gZ) := by
  set F := (Modules.pullback (Limits.pullback.fst gW gZ)).obj ℱ
  have : SheafOfModules.IsInvertible.{u, u, u} L := IsInvertible.sheafOfModules_isInvertible L
  have : (MonoidalCategory.tensorObj F L).IsQuasicoherent := isQuasicoherent_tensorObj F L
  refine isFlatOver_of_forall_exists _ _ fun V p _ ↦ ?_
  have : SheafOfModules.IsInvertible.{u, u, u} (Modules.unit W) :=
    IsInvertible.sheafOfModules_isInvertible (MonoidalCategory.tensorUnit W.Modules)
  obtain ⟨UW, hpUW, -, -⟩ := exists_isFreeGenerator (Modules.unit W)
    (TopologicalSpace.Opens.mem_top (Limits.pullback.fst gW gZ p))
  obtain ⟨N, hpN, -, ℓ, hℓ⟩ := exists_isFreeGenerator L (TopologicalSpace.Opens.mem_top p)
  refine ⟨N.1 ⊓ Limits.pullback.fst gW gZ ⁻¹ᵁ UW.1, ⟨hpN, hpUW⟩, fun U e hUN ↦ ?_⟩
  have hUN' : U.1 ≤ N.1 := hUN.trans inf_le_left
  have hflat := flat_sections_pullback_fst gW gZ ℱ UW.2 V.2 U.2
    (le_inf (hUN.trans inf_le_right) e)
  let : Module Γ(Z, V.1) Γ(F, U.1) :=
    Module.compHom _ ((Limits.pullback.snd gW gZ).appLE V.1 U.1 e).hom
  let : Module Γ(Z, V.1) Γ(MonoidalCategory.tensorObj F L, U.1) :=
    Module.compHom _ ((Limits.pullback.snd gW gZ).appLE V.1 U.1 e).hom
  let φ : Γ(F, U.1) →ₗ[Γ(Z, V.1)] Γ(MonoidalCategory.tensorObj F L, U.1) :=
    { toFun t := tmulSection t (L.presheaf.map (homOfLE hUN').op ℓ)
      map_add' a b := add_tmulSection a b _
      map_smul' r a := smul_tmulSection _ a _ }
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective φ (hℓ.bijective_tmulSection_right hUN')).symm


end AlgebraicGeometry.Scheme.Modules
