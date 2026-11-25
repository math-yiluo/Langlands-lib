/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-! # Clearing denominators for a local map from a finite free module

## References

* Stacks Project, Tag 01PW, specialized to the structure sheaf on a quasi-affine open
* Stacks Project, Tag 01PW, applied with the invertible module O_V, as in the global-generation
  input cited in Tag 0EKP, proof of (2) to (3)
-/

@[expose] public section
noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory Opposite in
private theorem scalar_nonvanishing {X : Scheme.{u}} (f : Γ(X, ⊤))
    (s : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (hs : ∀ U : X.Opens, s.app U (unitSectionsEquiv U 1) =
      unitSectionsEquiv U (X.presheaf.map (homOfLE le_top).op f)) :
    (Hom.zeroLocus s).support.compl = X.basicOpen f := by
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  ext x
  obtain ⟨O, hO, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let V : X.affineOpens := ⟨O, hO⟩
  have h := basicOpen_coeff_eq s V (isFreeGenerator_one V.1)
  have hf : (isFreeGenerator_one V.1).coeff (s.app V.1 (unitSectionsEquiv V.1 1)) =
      X.presheaf.map (homOfLE le_top).op f := by
    rw [hs, unitSectionsEquiv_eq_smul_one]
    exact (isFreeGenerator_one V.1).coeff_smul_self _
  rw [hf, X.basicOpen_res] at h
  have hxO : x ∈ V.1 := hxV
  constructor
  · intro hx
    exact (h.ge ⟨hxO, hx⟩).2
  · intro hx
    exact (h.le ⟨hxO, hx⟩).2

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory Opposite in
private theorem clear_scalar_section {X S : Scheme.{u}} (g : X ⟶ S)
    [IsSeparated g] [IsAffine S] [CompactSpace X]
    (N : X.Modules) [N.IsQuasicoherent] (f : Γ(X, ⊤))
    (t : Γ(N, X.basicOpen f)) :
    ∃ (m : ℕ) (v : Γ(N, ⊤)),
      N.presheaf.map (homOfLE le_top).op v =
        X.presheaf.map (homOfLE (show X.basicOpen f ≤ ⊤ from le_top)).op f ^ m • t := by
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  let s : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules := homOfGlobalSection (𝟙_ X.Modules) (unitSectionsEquiv ⊤ f)
  have hD : (Hom.zeroLocus s).support.compl = X.basicOpen f := by
    apply scalar_nonvanishing f s
    intro U
    dsimp only [s]
    erw [homOfGlobalSection_app_one]
    rfl
  obtain ⟨m, u, hu⟩ := exists_tensorPowSection_eq_restrict g (𝟙_ X.Modules) s N
    (N.presheaf.map (eqToHom hD).op t)
  have hf : s.app ⊤ (unitSectionsEquiv ⊤ 1) = f • unitSectionsEquiv ⊤ 1 := by
    dsimp only [s]
    erw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    exact unitSectionsEquiv_eq_smul_one f
  obtain ⟨E, hE, hpow⟩ := exists_tensorPowSectionOne_eq_pow_smul s
    (isFreeGenerator_one ⊤) hf m
  obtain ⟨v, hv⟩ := (hE.bijective_tmulSection_right (M := N) le_rfl).2 u
  rw [presheaf_map_id_apply] at hv
  refine ⟨m, v, ?_⟩
  apply (hE.bijective_tmulSection_right (M := N) le_top).1
  dsimp only at hv ⊢
  rw [← tmulSection_map, hv]
  rw [rightUnitor_inv_comp_whiskerLeft_app] at hu
  have hu' := congrArg ((N ⊗ (𝟙_ X.Modules).tensorPow m).presheaf.map
    (homOfLE hD.ge).op) hu
  rw [tmulSection_map, presheaf_map_tensorPowSectionOne] at hu'
  simp only [← Functor.map_comp_apply, ← op_comp] at hu'
  have hid : homOfLE hD.ge ≫ eqToHom hD = 𝟙 (X.basicOpen f) := Subsingleton.elim _ _
  rw [hid, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hu'
  have htop : homOfLE hD.ge ≫
      homOfLE (show (Hom.zeroLocus s).support.compl ≤ ⊤ from le_top) =
        homOfLE (show X.basicOpen f ≤ ⊤ from le_top) := Subsingleton.elim _ _
  rw [htop] at hu'
  rw [hu', ← presheaf_map_tensorPowSectionOne s m (homOfLE le_top), hpow,
    map_smul, map_pow, tmulSection_smul, smul_tmulSection]

private theorem unit_map_ext {X : Scheme.{u}} {N : X.Modules}
    (σ τ : unit X ⟶ N) (h : σ.app ⊤ (1 : Γ(X, ⊤)) = τ.app ⊤ (1 : Γ(X, ⊤))) : σ = τ := by
  refine hom_ext _ _ fun U ↦ ?_
  ext r
  obtain ⟨a, rfl⟩ := ((isFreeGenerator_one (X := X) ⊤).map
    (le_top : U ≤ ⊤)).exists_smul_eq r
  rw [Hom.app_smul, Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, h]

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory Opposite in
private theorem extend_on_basicOpen {X S : Scheme.{u}} (g : X ⟶ S)
    [IsSeparated g] [IsAffine S] [CompactSpace X]
    (N : X.Modules) [N.IsQuasicoherent] (f : Γ(X, ⊤)) (I : Type u) [Finite I]
    (τ : (restrictFunctor (X.basicOpen f).ι).obj (free (R := X.ringCatSheaf) I) ⟶
      N.restrict (X.basicOpen f).ι) :
    ∃ (φ : free (R := X.ringCatSheaf) I ⟶ N)
      (a : (restrictFunctor (X.basicOpen f).ι).obj (free (R := X.ringCatSheaf) I) ≅
        (restrictFunctor (X.basicOpen f).ι).obj (free (R := X.ringCatSheaf) I)),
      (restrictFunctor (X.basicOpen f).ι).map φ = a.hom ≫ τ := by
  classical
  have := Fintype.ofFinite I
  let W := X.basicOpen f
  let β (i : I) : Γ(N, W.ι ''ᵁ ⊤) :=
    Hom.app ((restrictUnitIso W.ι).inv ≫ (restrictFunctor W.ι).map (ιFree i) ≫ τ)
      ⊤ (1 : Γ(W.toScheme, ⊤))
  have hle : W ≤ W.ι ''ᵁ ⊤ := by simp
  have hle' : W.ι ''ᵁ ⊤ ≤ W := by simp
  choose n v hv using fun i ↦ clear_scalar_section g N f
    (N.presheaf.map (homOfLE hle).op (β i))
  let m := Finset.univ.sup n
  have hnm (i : I) : n i ≤ m := Finset.le_sup (Finset.mem_univ i)
  let v' (i : I) : Γ(N, ⊤) := f ^ (m - n i) • v i
  have hv' (i : I) : N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (v' i) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f ^ m •
        N.presheaf.map (homOfLE hle).op (β i) := by
    dsimp only [v']
    rw [map_smul, hv, map_pow, smul_smul, ← pow_add, Nat.sub_add_cancel (hnm i)]
  let φ : free (R := X.ringCatSheaf) I ⟶ N :=
    Sigma.desc fun i ↦ homOfGlobalSection N (v' i)
  let M := (restrictFunctor W.ι).obj (free (R := X.ringCatSheaf) I)
  have hunit : IsUnit (W.ι.appTop f ^ m) := (X.isUnit_ι_appTop_basicOpen f).pow m
  obtain ⟨c, hc⟩ := hunit
  let a : M ≅ M := {
    hom := M.smulHom (c : Γ(W.toScheme, ⊤))
    inv := M.smulHom (↑c⁻¹)
    hom_inv_id := by rw [← smulHom_mul, Units.inv_mul, smulHom_one]
    inv_hom_id := by rw [← smulHom_mul, Units.mul_inv, smulHom_one] }
  refine ⟨φ, a, ?_⟩
  have h : (restrictFunctor W.ι).map φ = τ ≫
      (N.restrict W.ι).smulHom (W.ι.appTop f ^ m) := by
    refine (isColimitOfPreserves (restrictFunctor W.ι)
      (SheafOfModules.isColimitFreeCofan I)).hom_ext fun ⟨i⟩ ↦ ?_
    change (restrictFunctor W.ι).map (ιFree i) ≫ _ =
      (restrictFunctor W.ι).map (ιFree i) ≫ _
    rw [← Functor.map_comp, show ιFree i ≫ φ = homOfGlobalSection N (v' i) from
      Sigma.ι_comp_desc _ _, ← cancel_epi (restrictUnitIso W.ι).inv]
    apply unit_map_ext
    have hi := congrArg (N.presheaf.map (homOfLE hle').op) (hv' i)
    simp only [map_smul, map_pow, presheaf_map_homOfLE_map_homOfLE,
      Scheme.presheaf_map_map_apply] at hi
    rw [presheaf_map_id_apply] at hi
    rw [Hom.comp_app, ConcreteCategory.comp_apply]
    have hA : Hom.app ((restrictFunctor W.ι).map (homOfGlobalSection N (v' i))) ⊤
        (Hom.app (restrictUnitIso W.ι).inv ⊤ (1 : Γ(W.toScheme, ⊤))) =
        N.presheaf.map (homOfLE le_top).op (v' i) := by
      exact (congrArg (Hom.app (homOfGlobalSection N (v' i)) (W.ι ''ᵁ ⊤))
        (map_one (W.ι.appIso ⊤).inv.hom)).trans (homOfGlobalSection_app_one _ _ _)
    rw [hA]
    have hB : Hom.app ((restrictUnitIso W.ι).inv ≫ (restrictFunctor W.ι).map
        (ιFree i) ≫ τ ≫ (N.restrict W.ι).smulHom (W.ι.appTop f ^ m)) ⊤
        (1 : Γ(W.toScheme, ⊤)) =
        ((N.restrict W.ι).smulHom (W.ι.appTop f ^ m)).app ⊤ (β i) := by
      rw [← Category.assoc, ← Category.assoc, Hom.comp_app, ConcreteCategory.comp_apply]
      rfl
    rw [hB, smulHom_app_top_apply]
    have hres : (W.ι.appIso ⊤).inv (W.ι.appTop f) =
        X.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op f := by
      have happ : W.ι.appLE ⊤ ⊤ le_top = W.ι.appTop := by
        exact W.ι.appLE_eq_app
      have hr := ConcreteCategory.congr_hom (W.ι.appLE_appIso_inv
        (U := ⊤) (V := ⊤) le_top) f
      rw [happ, ConcreteCategory.comp_apply] at hr
      exact hr
    have hsmul : ((N.restrict W.ι).smul (W.ι.appTop f ^ m)).asHom.hom (β i) =
        (W.ι.appIso ⊤).inv (W.ι.appTop f ^ m) • (β i : Γ(N, W.ι ''ᵁ ⊤)) := rfl
    change N.presheaf.map (homOfLE le_top).op (v' i) =
      ((N.restrict W.ι).smul (W.ι.appTop f ^ m)).asHom.hom (β i)
    rw [hsmul, map_pow, hres]
    exact hi
  rw [h, ← hc]
  exact (smulHom_naturality τ _).symm

/-- A local map from a finite free module extends after an invertible change of its source
on a smaller neighbourhood. The local map need not be an isomorphism. -/
theorem exists_global_map_of_local_free_map
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (V : (Spec (.of R)).Opens) (N : V.toScheme.Modules) [N.IsQuasicoherent]
    (U : V.toScheme.Opens) (x : V.toScheme) (hx : x ∈ U)
    (I : Type u) [Finite I]
    (ψ : (restrictFunctor U.ι).obj (free (R := V.toScheme.ringCatSheaf) I) ⟶
      N.restrict U.ι) :
    ∃ (W : V.toScheme.Opens) (hWU : W ≤ U), x ∈ W ∧
      ∃ (φ : free (R := V.toScheme.ringCatSheaf) I ⟶ N),
        ∃ (a : (restrictFunctor W.ι).obj (free (R := V.toScheme.ringCatSheaf) I) ≅
          (restrictFunctor W.ι).obj (free (R := V.toScheme.ringCatSheaf) I)),
          let g := V.toScheme.homOfLE hWU
          let c := restrictFunctorCongr (V.toScheme.homOfLE_ι hWU).symm ≪≫
            restrictFunctorComp g U.ι
          (restrictFunctor W.ι).map φ = a.hom ≫
            c.hom.app (free (R := V.toScheme.ringCatSheaf) I) ≫
            (restrictFunctor g).map ψ ≫ c.inv.app N := by
  classical
  have hx' : V.ι x ∈ V.ι ''ᵁ U := by
    exact ⟨x, hx, rfl⟩
  obtain ⟨f, hfU, hxf⟩ := (isAffineOpen_top (Spec (.of R))).exists_basicOpen_le
    ⟨V.ι x, hx'⟩ trivial
  let fV := V.ι.appTop f
  let W := V.toScheme.basicOpen fV
  have hWU : W ≤ U := by
    rw [show W = V.ι ⁻¹ᵁ (Spec (.of R)).basicOpen f from
      (Scheme.preimage_basicOpen_top V.ι f).symm]
    exact (V.ι.preimage_mono hfU).trans (V.ι.preimage_image_eq U).le
  have hxW : x ∈ W := by
    rw [show W = V.ι ⁻¹ᵁ (Spec (.of R)).basicOpen f from
      (Scheme.preimage_basicOpen_top V.ι f).symm]
    exact hxf
  let g := V.toScheme.homOfLE hWU
  let c := restrictFunctorCongr (V.toScheme.homOfLE_ι hWU).symm ≪≫
    restrictFunctorComp g U.ι
  let τ := c.hom.app (free (R := V.toScheme.ringCatSheaf) I) ≫
    (restrictFunctor g).map ψ ≫ c.inv.app N
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (V : Set (Spec (.of R))))
  have : CompactSpace V.toScheme :=
    TopologicalSpace.NoetherianSpace.compactSpace V.toScheme
  obtain ⟨φ, a, hφ⟩ := extend_on_basicOpen V.ι N fV I τ
  exact ⟨W, hWU, hxW, φ, a, hφ⟩

end AlgebraicGeometry.Scheme.Modules
