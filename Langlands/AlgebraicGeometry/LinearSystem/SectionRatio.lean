import Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.ModuleLinear

/-! # Ratios of pulled-back line-bundle sections

For a morphism `g : T ⟶ X` landing in the trivialization open of a global section `s₀` of a
line bundle `L`, the pullback of `s₀` is a frame of the pulled-back line bundle, so the
pullback of every global section `σ` is a unique multiple `r • g^* s₀` with `r ∈ Γ(T, ⊤)`.
This `r` is `sectionRatio L g σ s₀`. It is additive and linear over global functions in `σ`,
natural in `g`, multiplicative in the denominator, and it vanishes exactly when `σ`
vanishes along `g`.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

variable {X T T' : Scheme.{u}}

section pullbackSection

variable (M : X.Modules)

/-- The section morphism of a sum of sections is the sum of the section morphisms. -/
lemma sectionHom_add (s t : GlobalSections M) :
    sectionHom M (s + t) = sectionHom M s + sectionHom M t :=
  FiniteSectionAvoidance.sectionHom_add M s t

/-- The section morphism of zero is zero. -/
lemma sectionHom_zero : sectionHom M 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rw [Scheme.Modules.Hom.zero_app]
  change (sectionHom M 0).app U a = 0
  rw [LineBundleDescent.sectionHom_app, map_zero, smul_zero]

/-- The section morphism of a multiple is the section morphism precomposed with
multiplication by the scalar. -/
lemma sectionHom_smul (r : Γ(X, ⊤)) (s : GlobalSections M) :
    sectionHom M (r • s) = structureMulHom r ≫ sectionHom M s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rw [Scheme.Modules.Hom.comp_app]
  change (sectionHom M (r • s)).app U a = (sectionHom M s).app U ((structureMulHom r).app U a)
  rw [LineBundleDescent.sectionHom_app, LineBundleDescent.sectionHom_app, structureMulHom_app,
    Scheme.Modules.map_smul, mul_smul]

variable (f : T ⟶ X)

/-- Pullback of sections is additive. -/
lemma pullbackSection_add (s t : GlobalSections M) :
    pullbackSection f M (s + t) = pullbackSection f M s + pullbackSection f M t := by
  change (pullbackSectionHom f M (s + t)).app ⊤ (1 : Γ(T, ⊤)) = _
  rw [pullbackSectionHom, sectionHom_add, Functor.map_add, Preadditive.comp_add,
    Scheme.Modules.Hom.add_app]
  rfl

/-- Pullback of the zero section is zero. -/
lemma pullbackSection_zero : pullbackSection f M 0 = 0 :=
  Langlands.SchemeModule.pullbackSection_zero f M

/-- Pullback of sections as an additive map. -/
def pullbackSectionAddHom : GlobalSections M →+ GlobalSections ((Scheme.Modules.pullback f).obj M)
    where
  toFun := pullbackSection f M
  map_zero' := pullbackSection_zero M f
  map_add' := pullbackSection_add M f

/-- Pullback of a finite sum of sections. -/
lemma pullbackSection_sum {ι : Type*} (S : Finset ι) (s : ι → GlobalSections M) :
    pullbackSection f M (∑ i ∈ S, s i) = ∑ i ∈ S, pullbackSection f M (s i) :=
  map_sum (pullbackSectionAddHom M f) s S

/-- Pullback of sections is linear over global functions. -/
lemma pullbackSection_smul (r : Γ(X, ⊤)) (s : GlobalSections M) :
    pullbackSection f M (r • s) = f.appTop r • pullbackSection f M s := by
  have key : pullbackSectionHom f M (r • s) =
      structureMulHom (f.appTop r) ≫ pullbackSectionHom f M s := by
    have h := pullback_structureEnd_eq_mulHom f (structureMulHom r)
    rw [structureEndValue_mulHom] at h
    rw [← h, pullbackSectionHom, pullbackSectionHom, sectionHom_smul, Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (pullbackSectionHom f M (r • s)).app ⊤ (1 : Γ(T, ⊤)) = _
  rw [key, Scheme.Modules.Hom.comp_app]
  change (pullbackSectionHom f M s).app ⊤ ((structureMulHom (f.appTop r)).app ⊤ (1 : Γ(T, ⊤))) = _
  rw [structureMulHom_app, one_mul]
  have e : T.presheaf.map (homOfLE (le_top : (⊤ : T.Opens) ≤ ⊤)).op (f.appTop r) =
      ((f.appTop r : Γ(T, ⊤)) • (1 : Γ(T, ⊤)) : Γ(T, ⊤)) := by
    rw [smul_eq_mul, mul_one]
    exact LineBundleDescent.map_id_apply (structureModule T) _ (f.appTop r)
  rw [e]
  exact Scheme.Modules.Hom.app_smul _ _ _

/-- Pullback of sections along a composite is the iterated pullback, transported along
the canonical composition isomorphism of pullback functors. -/
lemma pullbackSection_comp (h : T' ⟶ T) (s : GlobalSections M) :
    ((Scheme.Modules.pullbackComp h f).hom.app M).app ⊤
        (pullbackSection h ((Scheme.Modules.pullback f).obj M) (pullbackSection f M s)) =
      pullbackSection (h ≫ f) M s := by
  apply sectionHom_injective
  rw [sectionHom_naturality]
  erw [sectionHom_pullbackSection]
  rw [sectionHom_pullbackSection, pullbackSectionHom, pullbackSectionHom,
    sectionHom_pullbackSection, pullbackSectionHom, Functor.map_comp]
  have hn := (Scheme.Modules.pullbackComp h f).hom.naturality (sectionHom M s)
  have hu : (Scheme.Modules.pullbackComp h f).hom.app (structureModule X) ≫
      (Langlands.Scheme.Modules.pullbackUnitIso (h ≫ f)).hom =
      (Scheme.Modules.pullback h).map (Langlands.Scheme.Modules.pullbackUnitIso f).hom ≫
        (Langlands.Scheme.Modules.pullbackUnitIso h).hom :=
    Langlands.Scheme.Modules.pullbackUnitComposition T' T X h f
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hn]
  have hu' : (Langlands.Scheme.Modules.pullbackUnitIso h).inv ≫
      (Scheme.Modules.pullback h).map (Langlands.Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullbackComp h f).hom.app (structureModule X) =
      (Langlands.Scheme.Modules.pullbackUnitIso (h ≫ f)).inv := by
    rw [Iso.inv_comp_eq, ← cancel_mono (Langlands.Scheme.Modules.pullbackUnitIso (h ≫ f)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hu, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      (Scheme.Modules.pullback h).map_id, Category.id_comp]
  rw [reassoc_of% hu']

/-- Vanishing along a morphism implies vanishing along every composite. -/
lemma vanishesAlong_comp {L : LineBundle X} {g : T ⟶ X} {σ : GlobalSections L.obj}
    (h : T' ⟶ T) (hg : VanishesAlong L g σ) : VanishesAlong L (h ≫ g) σ := by
  unfold VanishesAlong at hg ⊢
  rw [← pullbackSection_comp, hg, pullbackSection_zero, map_zero]

end pullbackSection

section ratio

variable (L : LineBundle X)

/-- The pullback of a section along a morphism into its trivialization open is a frame. -/
lemma bijective_sectionHom_pullbackSection (g : T ⟶ X) (s₀ : GlobalSections L.obj)
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) :
    Function.Bijective ((sectionHom _ (pullbackSection g L.obj s₀)).app ⊤) := by
  have htop : trivializationOpen ((Scheme.Modules.pullback g).obj L.obj)
      (pullbackSection g L.obj s₀) = ⊤ := by
    rw [lineBundlePullbackSectionOpen]
    exact top_le_iff.mp fun t _ ↦ hg t
  have htriv := (maximalTrivialization T _ (pullbackSection g L.obj s₀) ⊤).mpr htop.ge
  exact (LineBundleDescent.trivializesOn_iff_bijective _ _ _).mp htriv ⊤ le_rfl

lemma sectionHom_app_top {Y : Scheme.{u}} (N : Y.Modules) (τ : GlobalSections N)
    (a : Γ(Y, ⊤)) : (sectionHom N τ).app ⊤ a = a • τ := by
  rw [LineBundleDescent.sectionHom_app, LineBundleDescent.map_id_apply]

/-- The ratio of the pullbacks of `σ` and `s₀` along `g`. It is meaningful when `g` lands
in the trivialization open of `s₀`. -/
def sectionRatio (g : T ⟶ X) (σ s₀ : GlobalSections L.obj) : Γ(T, ⊤) :=
  Classical.epsilon fun a : Γ(T, ⊤) ↦
    a • pullbackSection g L.obj s₀ = pullbackSection g L.obj σ

variable {L}

lemma sectionRatio_smul {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (σ : GlobalSections L.obj) :
    sectionRatio L g σ s₀ • pullbackSection g L.obj s₀ = pullbackSection g L.obj σ := by
  apply Classical.epsilon_spec (p := fun a : Γ(T, ⊤) ↦
    a • pullbackSection g L.obj s₀ = pullbackSection g L.obj σ)
  obtain ⟨a, ha⟩ := (bijective_sectionHom_pullbackSection L g s₀ hg).2
    (pullbackSection g L.obj σ)
  exact ⟨a, by rw [← sectionHom_app_top]; exact ha⟩

lemma sectionRatio_eq_iff {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (σ : GlobalSections L.obj) (a : Γ(T, ⊤)) :
    sectionRatio L g σ s₀ = a ↔ a • pullbackSection g L.obj s₀ = pullbackSection g L.obj σ := by
  refine ⟨fun h ↦ h ▸ sectionRatio_smul hg σ, fun h ↦ ?_⟩
  apply (bijective_sectionHom_pullbackSection L g s₀ hg).1
  rw [sectionHom_app_top, sectionHom_app_top, sectionRatio_smul hg, h]

/-- A section vanishes along `g` exactly when its ratio to a frame does. -/
lemma vanishesAlong_iff_sectionRatio_eq_zero {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (σ : GlobalSections L.obj) :
    VanishesAlong L g σ ↔ sectionRatio L g σ s₀ = 0 := by
  rw [sectionRatio_eq_iff hg, zero_smul, VanishesAlong, eq_comm]

lemma sectionRatio_self {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) : sectionRatio L g s₀ s₀ = 1 := by
  rw [sectionRatio_eq_iff hg, one_smul]

lemma sectionRatio_add {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (σ τ : GlobalSections L.obj) :
    sectionRatio L g (σ + τ) s₀ = sectionRatio L g σ s₀ + sectionRatio L g τ s₀ := by
  rw [sectionRatio_eq_iff hg, add_smul, sectionRatio_smul hg, sectionRatio_smul hg,
    pullbackSection_add]

lemma sectionRatio_zero {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) : sectionRatio L g 0 s₀ = 0 := by
  rw [sectionRatio_eq_iff hg, zero_smul, pullbackSection_zero]

lemma sectionRatio_smul_left {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (r : Γ(X, ⊤)) (σ : GlobalSections L.obj) :
    sectionRatio L g (r • σ) s₀ = g.appTop r * sectionRatio L g σ s₀ := by
  rw [sectionRatio_eq_iff hg, mul_smul, sectionRatio_smul hg, pullbackSection_smul]

lemma sectionRatio_sum {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) {ι : Type*} (S : Finset ι)
    (σ : ι → GlobalSections L.obj) :
    sectionRatio L g (∑ i ∈ S, σ i) s₀ = ∑ i ∈ S, sectionRatio L g (σ i) s₀ := by
  rw [sectionRatio_eq_iff hg, Finset.sum_smul, pullbackSection_sum]
  exact Finset.sum_congr rfl fun i _ ↦ sectionRatio_smul hg (σ i)

/-- Ratios are natural in the morphism. -/
lemma sectionRatio_comp {g : T ⟶ X} {s₀ : GlobalSections L.obj}
    (hg : ∀ t, g t ∈ trivializationOpen L.obj s₀) (h : T' ⟶ T) (σ : GlobalSections L.obj) :
    sectionRatio L (h ≫ g) σ s₀ = h.appTop (sectionRatio L g σ s₀) := by
  have hhg : ∀ t, (h ≫ g) t ∈ trivializationOpen L.obj s₀ := fun t ↦ hg (h t)
  rw [sectionRatio_eq_iff hhg, ← pullbackSection_comp, ← pullbackSection_comp,
    ← sectionRatio_smul hg σ, pullbackSection_smul, Scheme.Modules.Hom.app_smul]

/-- Ratios are multiplicative in the denominator. -/
lemma sectionRatio_mul {g : T ⟶ X} {s₀ s₁ : GlobalSections L.obj}
    (hg₀ : ∀ t, g t ∈ trivializationOpen L.obj s₀) (hg₁ : ∀ t, g t ∈ trivializationOpen L.obj s₁)
    (σ : GlobalSections L.obj) :
    sectionRatio L g σ s₁ * sectionRatio L g s₁ s₀ = sectionRatio L g σ s₀ := by
  symm
  rw [sectionRatio_eq_iff hg₀, mul_smul, sectionRatio_smul hg₀, sectionRatio_smul hg₁]

/-- The ratio of two frames is a unit. -/
lemma isUnit_sectionRatio {g : T ⟶ X} {s₀ s₁ : GlobalSections L.obj}
    (hg₀ : ∀ t, g t ∈ trivializationOpen L.obj s₀) (hg₁ : ∀ t, g t ∈ trivializationOpen L.obj s₁) :
    IsUnit (sectionRatio L g s₁ s₀) := by
  refine IsUnit.of_mul_eq_one (sectionRatio L g s₀ s₁) ?_
  rw [mul_comm, sectionRatio_mul hg₀ hg₁, sectionRatio_self hg₀]

/-- At a field-valued point, a section vanishes exactly when the image point lies outside
its trivialization open. -/
lemma vanishesAlong_iff_not_mem {K : Type u} [Field K] (y : Spec (CommRingCat.of K) ⟶ X)
    (σ : GlobalSections L.obj) :
    VanishesAlong L y σ ↔ y (IsLocalRing.closedPoint K) ∉ trivializationOpen L.obj σ := by
  constructor
  · intro hv hy
    have hg : ∀ t, y t ∈ trivializationOpen L.obj σ := fun t ↦ by
      rwa [Subsingleton.elim t (IsLocalRing.closedPoint K)]
    have hb := (bijective_sectionHom_pullbackSection L y σ hg).1
    have h1 : (sectionHom _ (pullbackSection y L.obj σ)).app ⊤ (1 : Γ(Spec (CommRingCat.of K), ⊤)) =
        (sectionHom _ (pullbackSection y L.obj σ)).app ⊤ 0 := by
      rw [sectionHom_app_top, sectionHom_app_top, one_smul, zero_smul]
      exact hv
    have h10 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom (hb h1)
    rw [map_one, map_zero] at h10
    exact one_ne_zero h10
  · intro hy
    have hres : residueSection L.obj σ (y (IsLocalRing.closedPoint K)) = 0 := by
      by_contra h
      apply hy
      have := lineBundleResidueOpenComparison X L σ
      rw [← SetLike.mem_coe, ← this]
      exact h
    unfold VanishesAlong
    rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y,
      ← pullbackSection_comp]
    change ((Scheme.Modules.pullbackComp _ _).hom.app L.obj).app ⊤
      (pullbackSection _ _ (residueSection L.obj σ (y (IsLocalRing.closedPoint K)))) = 0
    rw [hres, pullbackSection_zero, map_zero]

end ratio

end Langlands.AlgebraicGeometry.LinearSystem
