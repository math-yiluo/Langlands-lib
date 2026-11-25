/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.OfForget
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

/-!
# Constructible sheaves and restriction of scalars to a quotient ring

Let `Λ` be a commutative ring and `J` an ideal of `Λ`. Restriction of scalars along
`Λ ⟶ Λ ⧸ J` sends étale sheaves of `Λ ⧸ J`-modules to étale sheaves of `Λ`-modules
(`CategoryTheory.Sheaf.restrictScalars`). It commutes with the pullback
(`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso`) and with stalks, and, for `Λ ⧸ J` finite,
it preserves and reflects constructibility
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff`). A sheaf of `Λ`-modules
killed by `J` is the restriction of scalars of its coextension of scalars
(`CategoryTheory.Sheaf.restrictScalarsCoextendScalarsIso`).

Consequently, for `Λ ⧸ J` finite, an extension of constructible sheaves of `Λ`-modules which is
killed by `J` is constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_smul_eq_zero`), reducing to the
extension property of constructible sheaves over the finite ring `Λ ⧸ J`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact`). This is how the extension
property is obtained for the reductions `K ⊗ᴸ Λ ⧸ Iⁿ⁺¹` at the integral stage `Λ = 𝒪_E` of the
`ℓ`-adic formalism, `Λ` itself being infinite.
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace ModuleCat

variable {R : Type w} [CommRing R] (J : Ideal R)

/-- Restriction of scalars along a quotient map `R ⟶ R ⧸ J` is a left adjoint. -/
instance : (restrictScalars.{w} (Ideal.Quotient.mk J)).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj.{w, w, w} (Ideal.Quotient.mk J)).isLeftAdjoint

/-- Restriction of scalars along a quotient map `R ⟶ R ⧸ J` is a right adjoint. -/
instance : (restrictScalars.{w} (Ideal.Quotient.mk J)).IsRightAdjoint :=
  (extendRestrictScalarsAdj.{w, w, w} (Ideal.Quotient.mk J)).isRightAdjoint

/-- The counit `Hom_R(R ⧸ J, M) ⟶ M`, `g ↦ g 1`, of the adjunction between restriction and
coextension of scalars along `R ⟶ R ⧸ J` is an isomorphism when `J` kills `M`. -/
lemma isIso_restrictCoextendScalarsAdj_counit_app (M : ModuleCat.{w} R)
    (hM : ∀ r ∈ J, ∀ m : M, r • m = 0) :
    IsIso ((restrictCoextendScalarsAdj.{w, w, w} (Ideal.Quotient.mk J)).counit.app M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun g₁ g₂ h ↦ ?_, fun m ↦ ?_⟩
  · refine CoextendScalars.ext (LinearMap.ext fun s ↦ ?_)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have e : ∀ g : (coextendScalars (Ideal.Quotient.mk J)).obj M,
        CoextendScalars.equiv _ M g (Ideal.Quotient.mk J r) =
          r • (restrictCoextendScalarsAdj.{w, w, w} (Ideal.Quotient.mk J)).counit.app M g := by
      intro g
      change _ = r • CoextendScalars.equiv _ M g (1 : R ⧸ J)
      rw [← map_smul]
      congr 1
      change _ = Ideal.Quotient.mk J r * 1
      rw [mul_one]
    rw [e, e, h]
  · let g₀ : R ⧸ J →ₗ[R] M := J.liftQ (LinearMap.toSpanSingleton R M m) fun r hr ↦ hM r hr m
    let g : (restrictScalars (Ideal.Quotient.mk J)).obj (of _ (R ⧸ J)) →ₗ[R] M :=
      { toFun s := g₀ s
        map_add' a b := g₀.map_add a b
        map_smul' r s := by
          change g₀ (Ideal.Quotient.mk J r * (show R ⧸ J from s)) = r • g₀ s
          rw [← g₀.map_smul]
          rfl }
    refine ⟨(CoextendScalars.equiv _ M).symm g, ?_⟩
    change J.liftQ (LinearMap.toSpanSingleton R M m) (fun r hr ↦ hM r hr m)
      (Submodule.Quotient.mk (1 : R)) = m
    rw [Submodule.liftQ_apply]
    simp

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type u'} [Category.{v} C] (K : GrothendieckTopology C)
  {R : Type w} [CommRing R] (J : Ideal R)

/-- Coextension of scalars on sheaves along `R ⟶ R ⧸ J`. -/
abbrev coextendScalars : Sheaf K (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} (R ⧸ J)) :=
  sheafCompose K (ModuleCat.coextendScalars.{w, w, w} (Ideal.Quotient.mk J))

/-- Coextension of scalars on sheaves is right adjoint to restriction of scalars. -/
instance : (coextendScalars K J).IsRightAdjoint :=
  (restrictCoextendScalarsAdj K (Ideal.Quotient.mk J)).isRightAdjoint

variable {K J}

-- Avoid searching for an irrelevant torsion-free instance in the counit proof.
attribute [-simp] smul_eq_zero smul_right_inj
  IsRegular.smul_right_inj IsRegular.smul_eq_zero_iff_right in
/-- A sheaf of `R`-modules killed by `J` is the restriction of scalars of its coextension of
scalars along `R ⟶ R ⧸ J`: the counit `Hom_R(R ⧸ J, F) ⟶ F` is an isomorphism. -/
def restrictScalarsCoextendScalarsIso (F : Sheaf K (ModuleCat.{w} R))
    (hF : ∀ r ∈ J, r • 𝟙 F = 0) :
    (restrictScalars K (Ideal.Quotient.mk J)).obj ((coextendScalars K J).obj F) ≅ F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U ↦
      have : IsIso ((ModuleCat.restrictCoextendScalarsAdj.{w, w, w}
          (Ideal.Quotient.mk J)).counit.app (F.obj.obj U)) :=
        ModuleCat.isIso_restrictCoextendScalarsAdj_counit_app J _ fun r hr m ↦ by
          have := congr_arg (fun φ : F ⟶ F ↦ φ.hom.app U m) (hF r hr)
          have h2 : (r • 𝟙 F).hom.app U = r • 𝟙 (F.obj.obj U) := rfl
          simpa [h2] using this
      asIso ((ModuleCat.restrictCoextendScalarsAdj.{w, w, w}
          (Ideal.Quotient.mk J)).counit.app (F.obj.obj U)))
      fun φ ↦ ((ModuleCat.restrictCoextendScalarsAdj.{w, w, w}
          (Ideal.Quotient.mk J)).counit.naturality (F.obj.map φ)))

/-- The isomorphism `restrictScalarsCoextendScalarsIso` is natural. -/
@[reassoc]
lemma restrictScalarsCoextendScalarsIso_hom_naturality {F G : Sheaf K (ModuleCat.{w} R)}
    (φ : F ⟶ G) (hF : ∀ r ∈ J, r • 𝟙 F = 0) (hG : ∀ r ∈ J, r • 𝟙 G = 0) :
    (restrictScalars K (Ideal.Quotient.mk J)).map ((coextendScalars K J).map φ) ≫
      (restrictScalarsCoextendScalarsIso G hG).hom =
        (restrictScalarsCoextendScalarsIso F hF).hom ≫ φ := by
  ext U : 3
  exact (ModuleCat.restrictCoextendScalarsAdj.{w, w, w}
    (Ideal.Quotient.mk J)).counit.naturality (φ.hom.app U)

end CategoryTheory.Sheaf

namespace ModuleCat

variable {R : Type w} [CommRing R] (J : Ideal R)

/-- A module over `R ⧸ J` is finitely generated over `R ⧸ J` if and only if it is finitely
generated over `R`. -/
lemma finite_restrictScalars_quotient_iff (M : ModuleCat.{w} (R ⧸ J)) :
    Module.Finite R ((restrictScalars (Ideal.Quotient.mk J)).obj M) ↔ Module.Finite (R ⧸ J) M := by
  let N := (restrictScalars (Ideal.Quotient.mk J)).obj M
  have key : ∀ s : Set M, ((Submodule.span R (s : Set N) : Submodule R N) : Set N) =
      ((Submodule.span (R ⧸ J) s : Submodule (R ⧸ J) M) : Set M) := by
    intro s
    ext m
    constructor
    · intro hm
      induction hm using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul r x _ hx => exact Submodule.smul_mem _ (Ideal.Quotient.mk J r) hx
    · intro hm
      induction hm using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem (Submodule.span R _)
      | add x y _ _ hx hy => exact add_mem (S := Submodule R _) hx hy
      | smul a x _ hx =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact Submodule.smul_mem (Submodule.span R _) r hx
  simp only [Module.finite_def, Submodule.fg_def]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← SetLike.coe_set_eq, ← key, h]
    rfl
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← SetLike.coe_set_eq, Submodule.top_coe]
    erw [key, h]
    rfl

end ModuleCat

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ)

namespace Scheme

variable {X : Scheme.{u}}

/-- The stalks of the restriction of scalars of a sheaf `G` of `Λ ⧸ J`-modules are finitely
generated over `Λ` if and only if those of `G` are finitely generated over `Λ ⧸ J`: taking
stalks commutes with restriction of scalars, which preserves colimits. -/
lemma isFinitelyGenerated_sheafFiber_restrictScalars_iff
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    ConcreteCategory.IsFinitelyGenerated ((pointSmallEtale s).sheafFiber.obj
        ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G)) ↔
      ConcreteCategory.IsFinitelyGenerated ((pointSmallEtale s).sheafFiber.obj G) := by
  refine (ConcreteCategory.isFinitelyGenerated_iff_of_iso (C := ModuleCat.{u + 1} Λ)
    (((pointSmallEtale s).sheafFiberCompIso (ModuleCat.restrictScalars.{u + 1}
      (Ideal.Quotient.mk J))).app G)).trans ?_
  rw [ModuleCat.isFinitelyGenerated_iff, ModuleCat.isFinitelyGenerated_iff]
  exact ModuleCat.finite_restrictScalars_quotient_iff J _

/-- A sheaf of `Λ ⧸ J`-modules is finite if and only if its restriction of scalars to `Λ` is. -/
lemma isFiniteSheaf_restrictScalars_iff
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))) :
    IsFiniteSheaf ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G) ↔
      IsFiniteSheaf G :=
  ⟨fun h ↦ ⟨fun Ω _ _ s ↦ (isFinitelyGenerated_sheafFiber_restrictScalars_iff J G Ω s).1
      (h.isFinitelyGenerated_sheafFiber Ω s)⟩,
    fun h ↦ ⟨fun Ω _ _ s ↦ (isFinitelyGenerated_sheafFiber_restrictScalars_iff J G Ω s).2
      (h.isFinitelyGenerated_sheafFiber Ω s)⟩⟩

/-- The restriction of scalars of a locally constant sheaf of `Λ ⧸ J`-modules is locally
constant, trivialized by the same cover: restriction of scalars preserves sheafification, hence
constant sheaves. -/
instance IsLocallyConstantSheaf.restrictScalars
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))) [h : IsLocallyConstantSheaf G] :
    IsLocallyConstantSheaf
      ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G) := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.nonempty_locallyConstantDatum
  refine ⟨⟨⟨𝒰, fun i ↦ ?_⟩⟩⟩
  have := h𝒰 i
  exact inferInstanceAs (((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
    (Ideal.Quotient.mk J))).obj (G.over _)).IsConstant _)

/-- The restriction of scalars of a finite locally constant sheaf of `Λ ⧸ J`-modules is finite
locally constant. -/
instance IsFiniteLocallyConstantSheaf.restrictScalars
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J)))
    [h : IsFiniteLocallyConstantSheaf G] :
    IsFiniteLocallyConstantSheaf
      ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G) where
  toIsFiniteSheaf := (isFiniteSheaf_restrictScalars_iff J G).2 h.toIsFiniteSheaf

/-- For `Λ ⧸ J` finite, a sheaf of `Λ ⧸ J`-modules whose restriction of scalars to `Λ` is finite
locally constant is finite locally constant: its underlying sheaf of sets is finite locally
constant (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget`). -/
lemma IsFiniteLocallyConstantSheaf.of_restrictScalars [Finite (Λ ⧸ J)]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J)))
    [h : IsFiniteLocallyConstantSheaf
      ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G)] :
    IsFiniteLocallyConstantSheaf G := by
  have hfin : IsFiniteSheaf G := (isFiniteSheaf_restrictScalars_iff J G).1 h.toIsFiniteSheaf
  refine IsFiniteLocallyConstantSheaf.of_forget G ⟨?_, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨𝒰, fun i ↦ ?_⟩
    have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
      (((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G).over
        _)).IsConstant _)
  · have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} (Λ ⧸ J))) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hfg := hfin.isFinitelyGenerated_sheafFiber Ω s
    rw [ModuleCat.isFinitelyGenerated_iff] at hfg
    have : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} (Λ ⧸ J))).obj G) :=
      Module.finite_of_finite (Λ ⧸ J)
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} (Λ ⧸ J)))).app G).symm.toEquiv

/-- For `Λ ⧸ J` finite, a sheaf of `Λ ⧸ J`-modules is constructible if and only if its
restriction of scalars to `Λ` is: pullback to the strata commutes with restriction of scalars
(`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso`). -/
lemma isConstructibleSheaf_restrictScalars_iff [Finite (Λ ⧸ J)]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))) :
    IsConstructibleSheaf
        ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G) ↔
      IsConstructibleSheaf G := by
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars X.smallEtaleTopology
        (Ideal.Quotient.mk J) ⋙ Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj G) :=
      hS i
    have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars _ (Ideal.Quotient.mk J)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} (Λ ⧸ J)) (S.immersion i)).obj G)) :=
      IsFiniteLocallyConstantSheaf.of_iso
        ((Etale.upperStarRestrictScalarsIso (Ideal.Quotient.mk J) (S.immersion i)).app G)
    exact IsFiniteLocallyConstantSheaf.of_restrictScalars J _
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} (Λ ⧸ J))
        (S.immersion i) ⋙ Sheaf.restrictScalars _ (Ideal.Quotient.mk J)).obj G) :=
      inferInstanceAs (IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars _
        (Ideal.Quotient.mk J)).obj ((Etale.upperStar _ (S.immersion i)).obj G)))
    exact IsFiniteLocallyConstantSheaf.of_iso
      ((Etale.upperStarRestrictScalarsIso (Ideal.Quotient.mk J) (S.immersion i)).app G).symm

/-- **Extensions of constructible sheaves killed by an ideal of finite index.** Let `J` be an
ideal of `Λ` with `Λ ⧸ J` finite, and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of
sheaves of `Λ`-modules with `F₁` and `F₃` constructible and `F₂` killed by `J`. Then `F₂` is
constructible: the sequence is the restriction of scalars of a short exact sequence of sheaves of
`Λ ⧸ J`-modules, whose outer terms are constructible
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_restrictScalars_iff`), and the extension
property holds over the finite ring `Λ ⧸ J`
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact`). -/
theorem IsConstructibleSheaf.of_shortExact_of_smul_eq_zero [Finite (Λ ⧸ J)]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (hJ : ∀ r ∈ J, r • 𝟙 S.X₂ = 0) [IsConstructibleSheaf S.X₁] [IsConstructibleSheaf S.X₃] :
    IsConstructibleSheaf S.X₂ := by
  have h₁ : ∀ r ∈ J, r • 𝟙 S.X₁ = 0 := fun r hr ↦ by
    have := hS.mono_f
    rw [← cancel_mono S.f, zero_comp]
    calc (r • 𝟙 S.X₁) ≫ S.f = S.f ≫ (r • 𝟙 S.X₂) := by simp
      _ = 0 := by rw [hJ r hr, comp_zero]
  have h₃ : ∀ r ∈ J, r • 𝟙 S.X₃ = 0 := fun r hr ↦ by
    have := hS.epi_g
    rw [← cancel_epi S.g, comp_zero]
    calc S.g ≫ (r • 𝟙 S.X₃) = (r • 𝟙 S.X₂) ≫ S.g := by simp
      _ = 0 := by rw [hJ r hr, zero_comp]
  let res := Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)
  let S' := S.map (Sheaf.coextendScalars X.smallEtaleTopology J)
  let e : S'.map res ≅ S := ShortComplex.isoMk
    (Sheaf.restrictScalarsCoextendScalarsIso _ h₁) (Sheaf.restrictScalarsCoextendScalarsIso _ hJ)
    (Sheaf.restrictScalarsCoextendScalarsIso _ h₃)
    (Sheaf.restrictScalarsCoextendScalarsIso_hom_naturality S.f h₁ hJ)
    (Sheaf.restrictScalarsCoextendScalarsIso_hom_naturality S.g hJ h₃)
  have hS' : S'.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff res).1 (ShortComplex.shortExact_of_iso e.symm hS)
  have : IsConstructibleSheaf S'.X₁ := (isConstructibleSheaf_restrictScalars_iff J _).1
    (IsConstructibleSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ h₁).symm)
  have : IsConstructibleSheaf S'.X₃ := (isConstructibleSheaf_restrictScalars_iff J _).1
    (IsConstructibleSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ h₃).symm)
  have : IsConstructibleSheaf S'.X₂ := IsConstructibleSheaf.of_shortExact hS'
  have : IsConstructibleSheaf (res.obj ((Sheaf.coextendScalars _ J).obj S.X₂)) :=
    (isConstructibleSheaf_restrictScalars_iff J _).2 this
  exact IsConstructibleSheaf.of_iso (Sheaf.restrictScalarsCoextendScalarsIso _ hJ)

end Scheme

end AlgebraicGeometry
