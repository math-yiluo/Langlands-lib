/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-!
# Relative Serre vanishing and coherence for closed subschemes of a projective bundle

Let `Y` be a locally noetherian scheme, `e : Y' ⟶ ℙ(n; Y)` a closed immersion and
`π = e ≫ (ℙ(n; Y) ↘ Y)`. For a coherent `𝒪_{Y'}`-module `𝒢`:

- the direct image `π_* 𝒢` is coherent
  (`isFinitePresentation_higherDirectImage_zero_of_projectiveSpace` in the namespace
  `AlgebraicGeometry.Scheme.Modules`);
- if `Y` is quasi-compact, `R^q π_* (𝒢(m)) = 0` for all `q > 0` and `m ≫ 0`, where
  `𝒢(m) = 𝒢 ⊗ e^* 𝒪(m)`
  (`AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_tensorObj_twistRestrict`).

Both are local on `Y`: over an affine open `V` of `Y`, with `g : Spec Γ(Y, V) ⟶ Y` the open
immersion, the base change of `π` along `g` is a closed subscheme of `ℙ(n; Spec Γ(Y, V))`, the
higher direct images along it are computed by its cohomology, and the projective case over the
noetherian ring `Γ(Y, V)` applies (`AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion`
and `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist_of_isNoetherianRing`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- A module vanishing along an open immersion `f` vanishes on the open range of `f`. -/
lemma isZero_restrict_opensRange_of_isZero_restrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (h : IsZero (M.restrict f)) :
    IsZero (M.restrict f.opensRange.ι) := by
  rw [isZero_restrict_iff]
  intro V hV
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, f ''ᵁ V' = V :=
    ⟨f ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hV]⟩
  exact (isZero_iff_forall_subsingleton _).1 h V'

/-- A quasi-coherent module on an affine scheme `Spec R` with no global sections is zero, being
the module associated with its global sections. -/
lemma isZero_of_subsingleton_sections_top {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (h : Subsingleton Γ(M, ⊤)) : IsZero M := by
  have : Subsingleton ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) := h
  have h' : IsZero ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) :=
    ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso ((tilde.functor R).map_isZero h') (asIso M.fromTildeΓ).symm

/-- Over an affine base `Spec R`, a higher direct image of a quasi-coherent module along a
quasi-compact separated morphism vanishes as soon as the corresponding cohomology group does. -/
lemma isZero_higherDirectImage_of_subsingleton_H {R : CommRingCat.{u}} {P : Scheme.{u}}
    (f : P ⟶ Spec R) [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions P.Modules]
    (N : P.Modules) [SheafOfModules.IsQuasicoherent (R := P.ringCatSheaf) N] (q : ℕ)
    (h : Subsingleton (N.H q)) : IsZero ((higherDirectImage f q).obj N) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f N q
  have := isQuasicoherent_higherDirectImage f N q
  exact isZero_of_subsingleton_sections_top _ he.1.subsingleton

/-- **Finiteness along a bijective semilinear map.** Let `σ : R →+* S`, `e : M →ₛₗ[σ] N`
bijective and `τ : A →+* R` a ring homomorphism. If `N` is finite over `A`, acting through
`σ ∘ τ`, then `M` is finite over `R`. -/
lemma Module.Finite.of_bijective_semilinearMap {R S A M N : Type*} [CommRing R] [CommRing S]
    [CommRing A] {σ : R →+* S} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e : M →ₛₗ[σ] N) (he : Function.Bijective e) (τ : A →+* R)
    (h : letI := Module.compHom N (σ.comp τ); Module.Finite A N) : Module.Finite R M := by
  let := Module.compHom N (σ.comp τ)
  let : Algebra A R := τ.toAlgebra
  let : Module A M := Module.compHom M τ
  have : IsScalarTower A R M := ⟨fun a r m ↦ by
    change (τ a * r) • m = τ a • r • m
    rw [mul_smul]⟩
  let e' : M ≃ₗ[A] N :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a m ↦ e.map_smulₛₗ (τ a) m
      invFun := Function.surjInv he.2
      left_inv := Function.leftInverse_surjInv he
      right_inv := Function.rightInverse_surjInv he.2 }
  have : Module.Finite A M := Module.Finite.equiv e'.symm
  exact Module.Finite.of_restrictScalars_finite A R M

variable {Y Y' : Scheme.{u}} {n : Type u} [Finite n] {π : Y' ⟶ Y} {e : Y' ⟶ ℙ(n; Y)}
  [IsClosedImmersion e] (he : e ≫ ℙ(n; Y) ↘ Y = π)

include he in
lemma isProper_of_comp_over : IsProper π := by
  rw [← he]
  infer_instance

include he in
/-- The base change of `π = e ≫ (ℙ(n; Y) ↘ Y)` along `g : Spec R ⟶ Y`, as a morphism into
`ℙ(n; Spec R)`. -/
abbrev chartLift {R : CommRingCat.{u}} (g : Spec R ⟶ Y) :
    Limits.pullback π g ⟶ ℙ(n; Spec R) :=
  ProjectiveSpace.liftBaseChange (g := g) (pullback.snd π g) (pullback.fst π g ≫ e)
    (by rw [Category.assoc, he, pullback.condition])

omit [Finite n] in
include he in
lemma isClosedImmersion_chartLift {R : CommRingCat.{u}} (g : Spec R ⟶ Y) :
    IsClosedImmersion (chartLift he g) := by
  have h : IsPullback (pullback.fst π g) (pullback.snd π g) (e ≫ ℙ(n; Y) ↘ Y) g := by
    rw [he]
    exact IsPullback.of_hasPullback π g
  exact MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_liftBaseChange _ h _)
    inferInstance

omit [Finite n] [IsClosedImmersion e] in
include he in
lemma chartLift_over {R : CommRingCat.{u}} (g : Spec R ⟶ Y) :
    chartLift he g ≫ ℙ(n; Spec R) ↘ Spec R = pullback.snd π g :=
  ProjectiveSpace.liftBaseChange_over _ _ _

/-- The pullback of `𝒢(m) = 𝒢 ⊗ e^* 𝒪(m)` to the base change of `π` along `g : Spec R ⟶ Y` is
the twist of the pullback of `𝒢` by the twisting sheaf of `ℙ(n; Spec R)`. -/
noncomputable def pullbackTensorTwistIso {R : CommRingCat.{u}} (g : Spec R ⟶ Y)
    (G : Y'.Modules) (m : ℤ) :
    (Modules.pullback (pullback.fst π g)).obj (G ⊗ ProjectiveSpace.twistRestrict e m) ≅
      (Modules.pullback (pullback.fst π g)).obj G ⊗
        ProjectiveSpace.twistRestrict (chartLift he g) m :=
  (Functor.Monoidal.μIso (Modules.pullback (pullback.fst π g)) G _).symm ≪≫
    (Iso.refl _ ⊗ᵢ (pullbackCompOfEq (pullback.fst π g) e _
        (ProjectiveSpace.liftBaseChange_map _ _ _).symm _ ≪≫
      (pullbackCompOfEq (chartLift he g) (ProjectiveSpace.map n g) _ rfl _).symm ≪≫
      (Modules.pullback (chartLift he g)).mapIso
        (ProjectiveSpace.pullbackMapTwistIso n g m)))

variable [IsLocallyNoetherian Y] [HasInjectiveResolutions Y'.Modules]

include he in
/-- **Relative Serre vanishing, locally.** For an affine open `V` of `Y` with open immersion
`g : Spec Γ(Y, V) ⟶ Y`, there is `m₀` with `(R^q π_* 𝒢(m))|_V = 0` for all `q > 0` and
`m ≥ m₀`. -/
lemma exists_isZero_higherDirectImage_tensorObj_twistRestrict_restrict (G : Y'.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y'.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := Y'.ringCatSheaf) G] {V : Y.Opens}
    (hV : IsAffineOpen V) :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ, IsZero
      (((higherDirectImage π (q + 1)).obj (G ⊗ ProjectiveSpace.twistRestrict e m)).restrict
        hV.fromSpec) := by
  have := isProper_of_comp_over he
  let g := hV.fromSpec
  have := isGrothendieckAbelian (Limits.pullback π g)
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := isClosedImmersion_chartLift he g
  obtain ⟨m₀, hm₀⟩ := exists_subsingleton_H_tensor_twist_of_isNoetherianRing Γ(Y, V)
    (chartLift he g) ((Modules.pullback (pullback.fst π g)).obj G)
  refine ⟨m₀, fun m hm q ↦ ?_⟩
  obtain ⟨E⟩ := nonempty_higherDirectImage_iso_restrict π (G ⊗ ProjectiveSpace.twistRestrict e m)
    g (pullback.fst π g) (pullback.snd π g) (IsPullback.of_hasPullback π g) (q + 1)
  refine IsZero.of_iso ?_ E.symm
  have h₁ := hm₀ m hm (q + 1) (Nat.succ_pos q)
  have : (G ⊗ ProjectiveSpace.twistRestrict e m).IsQuasicoherent :=
    isQuasicoherent_tensorObj _ _
  exact isZero_higherDirectImage_of_subsingleton_H (pullback.snd π g) _ (q + 1)
    (subsingleton_H_of_iso (pullbackTensorTwistIso he g G m).symm (q + 1))

include he in
/-- **Relative Serre vanishing.** Let `Y` be locally noetherian and quasi-compact,
`e : Y' ⟶ ℙ(n; Y)` a closed immersion and `π = e ≫ (ℙ(n; Y) ↘ Y)`. For a coherent
`𝒪_{Y'}`-module `𝒢` there is `m₀` with `R^q π_* (𝒢 ⊗ e^* 𝒪(m)) = 0` for all `q > 0` and
`m ≥ m₀`. -/
theorem exists_isZero_higherDirectImage_tensorObj_twistRestrict [CompactSpace Y]
    (G : Y'.Modules) [SheafOfModules.IsQuasicoherent (R := Y'.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := Y'.ringCatSheaf) G] :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, ∀ q : ℕ,
      IsZero ((higherDirectImage π (q + 1)).obj (G ⊗ ProjectiveSpace.twistRestrict e m)) := by
  classical
  have hcov : ∀ y : Y, ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V := fun y ↦ by
    obtain ⟨V, hV, hyV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
      (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hyV⟩
  choose V hV hyV using hcov
  choose m₀ hm₀ using fun y ↦
    exists_isZero_higherDirectImage_tensorObj_twistRestrict_restrict he G (hV y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (V y : Set Y))
    (fun y ↦ (V y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyV y⟩)
  obtain ⟨M, hM⟩ := (s.finite_toSet.image m₀).bddAbove
  refine ⟨M, fun m hm q ↦ isZero_of_forall_exists_isZero_restrict _ fun y ↦ ?_⟩
  obtain ⟨y', hy', hyy'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
  refine ⟨V y', hyy', ?_⟩
  have h := isZero_restrict_opensRange_of_isZero_restrict (hV y').fromSpec
    (hm₀ y' m ((hM ⟨y', hy', rfl⟩).trans hm) q)
  rwa [(hV y').opensRange_fromSpec] at h

include he in
/-- **Coherence of the direct image.** Let `Y` be locally noetherian, `e : Y' ⟶ ℙ(n; Y)` a
closed immersion and `π = e ≫ (ℙ(n; Y) ↘ Y)`. The direct image `π_* 𝒢` of a coherent
`𝒪_{Y'}`-module `𝒢` is of finite presentation (it is quasi-coherent by
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`): over an affine open `V`
of `Y` its sections are `H⁰` of a coherent module on a closed subscheme of `ℙ(n; Spec Γ(Y, V))`,
a finite `Γ(Y, V)`-module. -/
theorem isFinitePresentation_higherDirectImage_zero_of_projectiveSpace (G : Y'.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y'.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := Y'.ringCatSheaf) G] :
    ((higherDirectImage π 0).obj G).IsFinitePresentation := by
  have := isProper_of_comp_over he
  have hP (V : Y.Opens) (hV : IsAffineOpen V) :
      ∃ P : (((higherDirectImage π 0).obj G).restrict hV.fromSpec).Presentation, P.IsFinite := by
    let g := hV.fromSpec
    have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(Spec Γ(Y, V), ⊤) :=
      isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso Γ(Y, V)).commRingCatIsoToRingEquiv.symm
    have := isGrothendieckAbelian (Limits.pullback π g)
    have := isClosedImmersion_chartLift he g
    obtain ⟨E⟩ := nonempty_higherDirectImage_iso_restrict π G g (pullback.fst π g)
      (pullback.snd π g) (IsPullback.of_hasPullback π g) 0
    obtain ⟨σ, hσ⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
      (pullback.snd π g) ((Modules.pullback (pullback.fst π g)).obj G) 0
    have hfin := finite_H_of_isClosedImmersion Γ(Y, V) (chartLift he g)
      ((Modules.pullback (pullback.fst π g)).obj G) 0
    rw [chartLift_over he g] at hfin
    have : Module.Finite Γ(Spec Γ(Y, V), ⊤) Γ((higherDirectImage (pullback.snd π g) 0).obj
        ((Modules.pullback (pullback.fst π g)).obj G), ⊤) :=
      Module.Finite.of_bijective_semilinearMap σ hσ (Scheme.ΓSpecIso Γ(Y, V)).inv.hom hfin
    let φ : Γ((higherDirectImage (pullback.snd π g) 0).obj
        ((Modules.pullback (pullback.fst π g)).obj G), ⊤) →ₗ[Γ(Spec Γ(Y, V), ⊤)]
        Γ(((higherDirectImage π 0).obj G).restrict g, ⊤) :=
      { toFun := E.hom.app ⊤, map_add' := map_add _, map_smul' := Hom.app_smul E.hom }
    have : Module.Finite Γ(Spec Γ(Y, V), ⊤)
        Γ(((higherDirectImage π 0).obj G).restrict g, ⊤) :=
      Module.Finite.of_surjective φ (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).2
    have := finite_sections_top_of_finite (((higherDirectImage π 0).obj G).restrict g)
    have := isQuasicoherent_higherDirectImage π G 0
    exact exists_presentation_isFinite _
  have (V : Y.affineOpens) : IsOpenImmersion (IsAffineOpen.fromSpec (U := V.1) V.2) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  choose P _ using fun V : Y.affineOpens ↦ hP V.1 V.2
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top Y)

end AlgebraicGeometry.Scheme.Modules
