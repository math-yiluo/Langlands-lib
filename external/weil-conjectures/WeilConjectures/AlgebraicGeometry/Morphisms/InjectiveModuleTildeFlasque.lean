/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension

/-! # Flasqueness of the sheaf associated to an injective module

## References

* Stacks Project, Tag 09T2, Lemma 36.8.1
* Stacks Project, Tags 01YB and 09T2
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- For a section `s` of `M^~` over an open `U` of `Spec R` with `R` Noetherian, there are an
ideal `J` of `R` not contained in any prime of `U` and a linear map `φ : J →ₗ[R] M` such that
`φ a` restricts to `a • s` on `U` for all `a ∈ J` (Stacks, Tag 01YB). -/
private theorem affine_section_ideal_presentation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) (U : (Spec (.of R)).Opens)
    (s : (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf.obj (.op U)) :
    ∃ (J : Ideal R) (φ : J →ₗ[R] M),
      (∀ x : Spec (.of R), x ∈ U → ¬ J ≤ x.asIdeal) ∧
      (∀ a : J, tilde.toOpen (R := .of R) M U (φ a) = (a : R) • s) := by
  classical
  let X := Spec (.of R)
  let E := tilde (R := .of R) M
  let I : X.IdealSheafData := IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hI : (I.support : Set X) = (U : Set X)ᶜ := by
    simp [I]
  obtain ⟨n, α, hα⟩ := Modules.quasicoherent_open_section_ideal_extension I E U hI s
  let K := I ^ n
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let J : Ideal R := (K.ideal T).comap (ΓSpecIso (.of R)).inv.hom
  let B := (modulesSpecToSheaf.obj K.toModules).presheaf.obj (.op ⊤)
  let k : B →ₗ[R] R :=
    { toFun := fun b ↦ (ΓSpecIso (.of R)).hom (K.toModulesι.app ⊤ b)
      map_add' := by intros; simp
      map_smul' := by
        intro r b
        have hh := ((modulesSpecToSheaf.map K.toModulesι).hom.app (.op ⊤)).hom.map_smul r b
        let c : Γ(Spec (.of R), ⊤) := K.toModulesι.app ⊤ b
        change K.toModulesι.app ⊤ (r • b) = (ΓSpecIso (.of R)).inv r * c at hh
        rw [hh]
        change (ΓSpecIso (.of R)).hom ((ΓSpecIso (.of R)).inv r * c) = _
        simp only [map_mul, RingHom.id_apply, smul_eq_mul]
        simp [c] }
  have hk : Function.Injective k :=
    (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).hom).injective.comp
      (K.injective_toModulesι_app ⊤)
  have hrange : k.range = J := by
    ext a
    change (∃ b, (ΓSpecIso (.of R)).hom (K.toModulesι.app ⊤ b) = a) ↔
      (ΓSpecIso (.of R)).inv a ∈ (K.ideal T : Set Γ(X, T.1))
    rw [← K.range_toModulesι_app T]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, by simp [T]⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, by rw [hb]; simp⟩
  let e : B ≃ₗ[R] J := (LinearEquiv.ofInjective k hk).trans
    (LinearEquiv.ofEq _ _ hrange)
  let g : B →ₗ[R] M := (tilde.isoTop (R := .of R) M).inv.hom.comp
    ((modulesSpecToSheaf.map α).hom.app (.op ⊤)).hom
  refine ⟨J, g.comp e.symm.toLinearMap, ?_, ?_⟩
  · intro x hx hxJ
    have hK : (K.support : Set X) = PrimeSpectrum.zeroLocus (J : Set R) := by
      have he : IdealSheafData.ofIdealTop (K.ideal T) = K := by
        apply IdealSheafData.ext_of_isAffine
        simp [T]
      rw [← he, IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
      rfl
    have hxK : x ∈ (K.support : Set X) := by
      rw [hK]
      exact hxJ
    cases n with
    | zero => simp [K] at hxK
    | succ n =>
      have he : (K.support : Set X) = (U : Set X)ᶜ := by
        simpa only [K, IdealSheafData.support_pow_succ] using hI
      exact (he ▸ hxK) hx
  · intro a
    let b := e.symm a
    have hb : K.toModulesι.app ⊤ b = (ΓSpecIso (.of R)).inv (a : R) := by
      have he := congrArg Subtype.val (e.apply_symm_apply a)
      change k b = (a : R) at he
      apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).hom).injective
      simpa [k, ← CommRingCat.comp_apply] using he
    have htop : tilde.toOpen (R := .of R) M ⊤ (g b) = α.app ⊤ b := by
      change (tilde.isoTop (R := .of R) M).hom
        ((tilde.isoTop (R := .of R) M).inv (α.app ⊤ b)) = α.app ⊤ b
      exact ConcreteCategory.congr_hom (tilde.isoTop (R := .of R) M).inv_hom_id _
    have he := congrArg (fun f ↦ f (g b)) (tilde.toOpen_res (R := .of R) M ⊤ U (homOfLE le_top))
    simp only [ConcreteCategory.comp_apply] at he
    rw [htop] at he
    let bU := K.toModules.val.map (homOfLE (show U ≤ ⊤ from le_top)).op b
    let sE : Γ(E, U) := s
    let : Module R Γ(E, U) :=
      inferInstanceAs (Module R ((modulesSpecToSheaf.obj E).presheaf.obj (.op U)))
    have hn := PresheafOfModules.naturality_apply α.val
      (homOfLE (show U ≤ ⊤ from le_top)).op b
    have hi := PresheafOfModules.naturality_apply K.toModulesι.val
      (homOfLE (show U ≤ ⊤ from le_top)).op b
    have hi' : K.toModulesι.app U bU =
        X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          ((ΓSpecIso (.of R)).inv (a : R)) := by
      exact hi.trans (congrArg (X.presheaf.map (homOfLE le_top).op) hb)
    let cU : Γ(X, U) := K.toModulesι.app U bU
    change tilde.toOpen (R := .of R) M U (g b) = (a : R) • sE
    calc
      _ = E.presheaf.map (homOfLE le_top).op (α.app ⊤ b) := he.symm
      _ = α.app U bU := hn.symm
      _ = cU • sE := hα U le_rfl bU
      _ = (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
          ((ΓSpecIso (.of R)).inv (a : R))) • sE :=
        congrArg (fun c : Γ(X, U) ↦ c • sE) hi'
      _ = (a : R) • sE := (Modules.smul_Spec_def (M := E) (a : R) sE).symm

/-- The associated sheaf of an injective module over a Noetherian ring is flasque. -/
theorem injective_tilde_isFlasque
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Injective M] :
    TopCat.Presheaf.IsFlasque (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf := by
  classical
  let F := (modulesSpecToSheaf.obj (tilde (R := .of R) M)).presheaf
  have hs : ∀ (U : (Spec (.of R)).Opens), Function.Surjective (tilde.toOpen M U) := by
    intro U s
    obtain ⟨J, φ, hJ, hφ⟩ := affine_section_ideal_presentation R M U s
    let ι : ModuleCat.of R J ⟶ ModuleCat.of R R := ModuleCat.ofHom J.subtype
    have : Mono ι := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    obtain ⟨ψ, hψ⟩ := Injective.factors (ModuleCat.ofHom φ) ι
    refine ⟨ψ 1, ?_⟩
    have ha : ∀ a : J, (a : R) • tilde.toOpen M U (ψ 1) = (a : R) • s := by
      intro a
      have he : ψ (a : R) = φ a := congrArg (fun f ↦ f a) hψ
      rw [← (tilde.toOpen M U).hom.map_smul]
      have he' : (a : R) • ψ 1 = φ a := by
        rw [← ψ.hom.map_smul]
        simpa only [smul_eq_mul, mul_one] using he
      rw [he', hφ]
    apply TopCat.Presheaf.IsSheaf.section_ext
      (modulesSpecToSheaf.obj (tilde (R := .of R) M)).2
    intro x hx
    obtain ⟨a, haJ, hax⟩ := IsConcreteLE.not_le_iff_exists.mp (hJ x hx)
    let V : (Spec (.of R)).Opens := U ⊓ PrimeSpectrum.basicOpen a
    refine ⟨V, inf_le_left, ⟨hx, hax⟩, ?_⟩
    apply (tilde (R := .of R) M).isSMulRegular_of_le_basicOpen
      (show V ≤ PrimeSpectrum.basicOpen a from inf_le_right)
    have he := congrArg (fun t ↦ F.map (homOfLE (show V ≤ U from inf_le_left)).op t)
      (ha ⟨a, haJ⟩)
    simpa only [map_smul] using he
  refine ⟨?_⟩
  intro U V i
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨m, hm⟩ := hs V.unop s
  refine ⟨tilde.toOpen M U.unop m, ?_⟩
  have he := congrArg (fun f ↦ f m) (tilde.toOpen_res M U.unop V.unop i.unop)
  exact he.trans hm

end

end AlgebraicGeometry.Scheme
