import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Torsors of cocycles on affine fpqc covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent

namespace CocycleTorsor

set_option backward.isDefEq.respectTransparency false in
/-- Faithfully flat descent of an affine scheme along an affine flat surjective map, presented
by a groupoid-like relation on the scheme to be descended. -/
theorem exists_affineQuotient {Y R U M₀ P : Scheme.{u}} [IsAffine Y] [IsAffine U] [IsAffine M₀]
    (t s : R ⟶ Y) (f : Y ⟶ U) (q₀ : U ⟶ M₀) [Flat q₀] [Surjective q₀]
    (hout : IsPullback (t ≫ f) s q₀ (f ≫ q₀))
    (diag : Y ⟶ R) (hdt : diag ≫ t = 𝟙 Y) (hds : diag ≫ s = 𝟙 Y)
    (p₁ p₂ : P ⟶ R) (hP : IsPullback p₁ p₂ s t)
    (comp : P ⟶ R) (hct : comp ≫ t = p₁ ≫ t) (hcs : comp ≫ s = p₂ ≫ s) :
    ∃ (M : Scheme.{u}) (q : Y ⟶ M) (h : M ⟶ M₀),
      IsAffine M ∧ IsPullback f q q₀ h ∧ IsPullback t s q q := by
  have hR : IsAffine R := IsAffine.of_isPullback hout
  have hPo := isPushout_appTop_of_isPullback hout
  have hP₂ := isPushout_appTop_of_isPullback hP
  have hφ : q₀.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q₀).mp ⟨inferInstance, inferInstance⟩
  have hw : t ≫ f ≫ q₀ = s ≫ f ≫ q₀ := by
    simpa only [Category.assoc] using hout.w
  have hmem : ∀ a, f.appTop.hom (q₀.appTop.hom a) ∈
      t.appTop.hom.eqLocus s.appTop.hom := fun a =>
    congrArg (fun k : R ⟶ M₀ => k.appTop.hom a) hw
  have key := isPushout_eqLocus_of_groupoid q₀.appTop.hom hφ f.appTop.hom t.appTop.hom
    s.appTop.hom diag.appTop.hom p₁.appTop.hom p₂.appTop.hom comp.appTop.hom hPo hP₂
    (congrArg (fun k => k.appTop.hom) hdt) (congrArg (fun k => k.appTop.hom) hds)
    (congrArg (fun k => k.appTop.hom) hct) (congrArg (fun k => k.appTop.hom) hcs) hmem
  set A : Subring Γ(Y, ⊤) := t.appTop.hom.eqLocus s.appTop.hom with hA
  let iA : Γ(M₀, ⊤) →+* A := (f.appTop.hom.comp q₀.appTop.hom).codRestrict _ hmem
  let M : Scheme.{u} := Spec (CommRingCat.of A)
  let h : M ⟶ M₀ := Spec.map (CommRingCat.ofHom iA) ≫ M₀.isoSpec.inv
  let q : Y ⟶ M := Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom A.subtype)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ key
  have hpbU : IsPullback f q q₀ h := by
    refine hsq.of_iso Y.isoSpec.symm U.isoSpec.symm (Iso.refl _) M₀.isoSpec.symm ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, q, Iso.inv_hom_id_assoc]
      rfl
    · simp only [Iso.symm_hom, CommRingCat.ofHom_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp, h]
      rfl
  have hq : t ≫ q = s ≫ q := by
    simp only [q, ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact x.2
  have hfin : IsPullback t s q q := by
    have H : IsPullback (t ≫ f) s q₀ (q ≫ h) := by rwa [← hpbU.w]
    exact IsPullback.of_right H hq hpbU
  exact ⟨M, q, h, inferInstance, hpbU, hfin⟩


section Construction

variable {S : Scheme.{u}} (G : GroupScheme S) (U : Over S)

/-- The trivial torsor over the cover: points are pairs `(h, a)` of a group point and a
cover point. -/
abbrev trivialCover : Over S := G.X ⊗ U

/-- The relation scheme: points `(b, (h, a))`, relating `(h, a)` to `(h ξ(a, b), b)`. -/
abbrev relation : Over S := U ⊗ trivialCover G U

/-- The source `(b, (h, a)) ↦ (h, a)` of a relation point. -/
abbrev src : relation G U ⟶ trivialCover G U := snd _ _

variable {G U} (ξ : Cocycle G U)

/-- The target `(b, (h, a)) ↦ (h ξ(a, b), b)` of a relation point. -/
def tgt : relation G U ⟶ trivialCover G U :=
  lift ((snd U _ ≫ fst G.X U) * ξ.toFun (snd U _ ≫ snd G.X U) (fst U _)) (fst U _)

@[reassoc]
theorem comp_tgt {Z : Over S} (r : Z ⟶ relation G U) :
    r ≫ tgt ξ = lift ((r ≫ snd U _ ≫ fst G.X U) *
      ξ.toFun (r ≫ snd U _ ≫ snd G.X U) (r ≫ fst U _)) (r ≫ fst U _) := by
  rw [tgt, comp_lift, MonObj.comp_mul, ← ξ.naturality]

@[reassoc (attr := simp)]
theorem tgt_snd : tgt ξ ≫ snd G.X U = fst U (trivialCover G U) := by
  simp [tgt]

end Construction

section Quotient

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- The diagonal relation point `(a, (h, a))`. -/
def diag : trivialCover G U ⟶ relation G U := lift (snd G.X U) (𝟙 _)

@[reassoc (attr := simp)]
theorem diag_src : diag ≫ src G U = 𝟙 _ := lift_snd _ _

variable (ξ : Cocycle G U)

@[reassoc (attr := simp)]
theorem diag_tgt : diag ≫ tgt ξ = 𝟙 _ := by
  rw [comp_tgt]
  simp only [diag, lift_snd_assoc, lift_fst, Category.id_comp, Cocycle.toFun_self, mul_one]
  exact lift_fst_snd

theorem isPullback_out :
    IsPullback ((tgt ξ).left ≫ (snd G.X U).left) (src G U).left U.hom
      ((snd G.X U).left ≫ U.hom) := by
  have h1 : (tgt ξ).left ≫ (snd G.X U).left = pullback.fst U.hom (trivialCover G U).hom := by
    rw [← Over.comp_left, tgt_snd]
    rfl
  rw [h1]
  refine (IsPullback.of_hasPullback U.hom (trivialCover G U).hom).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact pullback.condition

/-- Composable pairs of relation points, as an object over the base. -/
def pairs : Over S := Over.mk (pullback.fst (src G U).left (tgt ξ).left ≫ (relation G U).hom)

/-- The first relation point of a composable pair. -/
def pair₁ : pairs ξ ⟶ relation G U := Over.homMk (pullback.fst _ _) rfl

/-- The second relation point of a composable pair. -/
def pair₂ : pairs ξ ⟶ relation G U := Over.homMk (pullback.snd _ _) (by
  change pullback.snd _ _ ≫ (relation G U).hom = pullback.fst _ _ ≫ (relation G U).hom
  conv_lhs => rw [← Over.w (tgt ξ)]
  conv_rhs => rw [← Over.w (src G U)]
  rw [← Category.assoc, ← Category.assoc, pullback.condition])

theorem pair_condition : pair₁ ξ ≫ src G U = pair₂ ξ ≫ tgt ξ :=
  Over.OverMorphism.ext pullback.condition

/-- The composite relation point. -/
def compose : pairs ξ ⟶ relation G U := lift (pair₁ ξ ≫ fst U _) (pair₂ ξ ≫ snd U _)

theorem compose_src : compose ξ ≫ src G U = pair₂ ξ ≫ src G U := lift_snd _ _

theorem compose_tgt : compose ξ ≫ tgt ξ = pair₁ ξ ≫ tgt ξ := by
  have hc := pair_condition ξ
  have hh : pair₁ ξ ≫ snd U _ ≫ fst G.X U = (pair₂ ξ ≫ snd U _ ≫ fst G.X U) *
      ξ.toFun (pair₂ ξ ≫ snd U _ ≫ snd G.X U) (pair₂ ξ ≫ fst U _) := by
    have h := congrArg (· ≫ fst G.X U) hc
    simp only [Category.assoc, comp_tgt_assoc, lift_fst] at h
    exact h
  have ha : pair₁ ξ ≫ snd U _ ≫ snd G.X U = pair₂ ξ ≫ fst U _ := by
    have h := congrArg (· ≫ snd G.X U) hc
    simp only [Category.assoc, comp_tgt_assoc, lift_snd] at h
    exact h
  rw [comp_tgt, comp_tgt]
  simp only [compose, lift_fst, lift_snd_assoc]
  rw [hh, ha, mul_assoc, ← ξ.cocycle]
  simp only [Category.assoc]

variable [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Flat U.hom] [Surjective U.hom]

instance : IsAffine (trivialCover G U).left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact inferInstanceAs (IsAffine (pullback G.X.hom U.hom))

/-- An affine quotient of the trivial torsor over the cover by the relation of the cocycle,
together with its identification of the trivial torsor with the pullback to the cover. -/
structure Quotient where
  /-- The quotient scheme. -/
  scheme : Scheme.{u}
  /-- The quotient map. -/
  proj : (trivialCover G U).left ⟶ scheme
  /-- The structure map of the quotient. -/
  base : scheme ⟶ S
  isAffine : IsAffine scheme
  isPullback : IsPullback (snd G.X U).left proj U.hom base
  kernelPair : IsPullback (tgt ξ).left (src G U).left proj proj

theorem nonempty_quotient : Nonempty (Quotient ξ) := by
  obtain ⟨M, q, h, hM, hpb, hker⟩ := exists_affineQuotient (tgt ξ).left (src G U).left
    (snd G.X U).left U.hom (isPullback_out ξ) diag.left
    (by rw [← Over.comp_left, diag_tgt]; rfl) (by rw [← Over.comp_left, diag_src]; rfl)
    (pullback.fst (src G U).left (tgt ξ).left) (pullback.snd (src G U).left (tgt ξ).left)
    (IsPullback.of_hasPullback _ _) (compose ξ).left
    (congrArg (fun f => f.left) (compose_tgt ξ)) (congrArg (fun f => f.left) (compose_src ξ))
  exact ⟨⟨M, q, h, hM, hpb, hker⟩⟩

end Quotient

section Descent

variable {S : Scheme.{u}}

/-- A morphism out of the source of an effective epimorphism of underlying schemes, which takes
equal values on any two test points with equal images, descends to the target. -/
theorem exists_desc {A B C : Over S} (π : A ⟶ B) [EffectiveEpi π.left] (e : A ⟶ C)
    (he : ∀ {Z : Over S} (a₁ a₂ : Z ⟶ A), a₁ ≫ π = a₂ ≫ π → a₁ ≫ e = a₂ ≫ e) :
    ∃ e' : B ⟶ C, π ≫ e' = e := by
  let d : B.left ⟶ C.left :=
    EffectiveEpi.desc π.left e.left (fun {Z} a b hab => by
      have hb : b ≫ A.hom = a ≫ A.hom := by
        rw [← Over.w π, ← Category.assoc, ← Category.assoc, hab]
      let a₀ : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
      let b₀ : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
      exact congrArg (fun e => e.left) (he a₀ b₀ (Over.OverMorphism.ext hab)))
  have hd : π.left ≫ d = e.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk d ?_, Over.OverMorphism.ext hd⟩
  apply (cancel_epi π.left).mp
  rw [← Category.assoc, hd, Over.w e, Over.w π]

/-- Morphisms of the target of an effective epimorphism of underlying schemes agree when they
agree after composition with it. -/
theorem hom_ext_of_effectiveEpi {A B C : Over S} (π : A ⟶ B) [EffectiveEpi π.left]
    {e₁ e₂ : B ⟶ C} (h : π ≫ e₁ = π ≫ e₂) : e₁ = e₂ := by
  apply Over.OverMorphism.ext
  apply (cancel_epi π.left).mp
  exact congrArg (fun e => e.left) h

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
/-- Products of fpqc morphisms of objects over the base are effective epimorphisms. -/
theorem effectiveEpi_tensorHom {A B C D : Over S} (f : A ⟶ B) (g : C ⟶ D)
    [QuasiCompact f.left] [Flat f.left] [Surjective f.left]
    [QuasiCompact g.left] [Flat g.left] [Surjective g.left] :
    EffectiveEpi (f ⊗ₘ g).left := by
  have hp : fpqcProperty (f ⊗ₘ g).left :=
    MorphismProperty.pullbackMap (P := fpqcProperty)
      ⟨inferInstance, inferInstance, inferInstance⟩
      ⟨inferInstance, inferInstance, inferInstance⟩
      (Over.w f).symm (Over.w g).symm
  let : QuasiCompact (f ⊗ₘ g).left := hp.1
  let : Flat (f ⊗ₘ g).left := hp.2.1
  let : Surjective (f ⊗ₘ g).left := hp.2.2
  infer_instance

end Descent

/-- The structure map of a group scheme has the unit section, so it is surjective. -/
theorem surjective_groupScheme_hom {S : Scheme.{u}} (G : GroupScheme S) : Surjective G.X.hom := by
  have h : η[G.X].left ≫ G.X.hom = 𝟙 S := Over.w η[G.X]
  refine ⟨fun x => ⟨η[G.X].left x, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, h]
  rfl

section Torsor

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S} (ξ : Cocycle G U)
variable [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Flat U.hom] [Surjective U.hom]

/-- The chosen affine quotient. -/
def quotient : Quotient ξ := Classical.choice (nonempty_quotient ξ)

/-- The torsor of the cocycle. -/
def torsor : Over S := Over.mk (quotient ξ).base

/-- The quotient map from the trivial torsor over the cover to the torsor of the cocycle. -/
def proj : trivialCover G U ⟶ torsor ξ := Over.homMk (quotient ξ).proj (by
  change (quotient ξ).proj ≫ (quotient ξ).base = pullback.fst G.X.hom U.hom ≫ G.X.hom
  rw [← (quotient ξ).isPullback.w]
  exact pullback.condition.symm)

instance : IsAffine (torsor ξ).left := (quotient ξ).isAffine

instance : Flat (proj ξ).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) (quotient ξ).isPullback
    inferInstance

instance : Surjective (proj ξ).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    (quotient ξ).isPullback inferInstance

instance : QuasiCompact (proj ξ).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
    (quotient ξ).isPullback inferInstance

theorem tgt_proj : tgt ξ ≫ proj ξ = src G U ≫ proj ξ :=
  Over.OverMorphism.ext (quotient ξ).kernelPair.w

/-- The class in the torsor of the point `(h, a)` of the trivial torsor over the cover. -/
def mk {Z : Over S} (h : Z ⟶ G.X) (a : Z ⟶ U) : Z ⟶ torsor ξ := lift h a ≫ proj ξ

@[reassoc]
theorem comp_mk {Z Z' : Over S} (t : Z' ⟶ Z) (h : Z ⟶ G.X) (a : Z ⟶ U) :
    t ≫ mk ξ h a = mk ξ (t ≫ h) (t ≫ a) := by
  rw [mk, mk, ← Category.assoc, comp_lift]

theorem proj_eq_mk : proj ξ = mk ξ (fst G.X U) (snd G.X U) := by
  rw [mk, lift_fst_snd, Category.id_comp]

/-- Two points of the trivial torsor have the same class exactly when they are related by the
cocycle. -/
theorem mk_eq_mk_iff {Z : Over S} (h₁ h₂ : Z ⟶ G.X) (a₁ a₂ : Z ⟶ U) :
    mk ξ h₁ a₁ = mk ξ h₂ a₂ ↔ h₁ = h₂ * ξ.toFun a₂ a₁ := by
  constructor
  · intro he
    have hk := (quotient ξ).kernelPair
    let r₀ : Z.left ⟶ (relation G U).left :=
      hk.lift (lift h₁ a₁).left (lift h₂ a₂).left (congrArg (fun f => f.left) he)
    have hr₁ : r₀ ≫ (tgt ξ).left = (lift h₁ a₁).left := hk.lift_fst _ _ _
    have hr₂ : r₀ ≫ (src G U).left = (lift h₂ a₂).left := hk.lift_snd _ _ _
    let r : Z ⟶ relation G U := Over.homMk r₀ (by
      rw [← Over.w (src G U), ← Category.assoc, hr₂, Over.w (lift h₂ a₂)])
    have ht : r ≫ tgt ξ = lift h₁ a₁ := Over.OverMorphism.ext hr₁
    have hs : r ≫ src G U = lift h₂ a₂ := Over.OverMorphism.ext hr₂
    have hsf : r ≫ snd U _ ≫ fst G.X U = h₂ := by
      rw [← Category.assoc]; change (r ≫ src G U) ≫ _ = _; rw [hs, lift_fst]
    have hss : r ≫ snd U _ ≫ snd G.X U = a₂ := by
      rw [← Category.assoc]; change (r ≫ src G U) ≫ _ = _; rw [hs, lift_snd]
    rw [comp_tgt, hsf, hss] at ht
    have hb : r ≫ fst U _ = a₁ := by
      simpa only [lift_snd] using congrArg (· ≫ snd G.X U) ht
    have hh := congrArg (· ≫ fst G.X U) ht
    simp only [lift_fst, hb] at hh
    exact hh.symm
  · intro he
    let r : Z ⟶ relation G U := lift a₁ (lift h₂ a₂)
    have ht : r ≫ tgt ξ = lift h₁ a₁ := by
      rw [comp_tgt]
      simp only [r, lift_fst, lift_snd_assoc, lift_snd, he]
    have hs : r ≫ src G U = lift h₂ a₂ := lift_snd _ _
    rw [mk, mk, ← ht, ← hs, Category.assoc, Category.assoc, tgt_proj]

/-- Morphisms out of the torsor agree when they agree on all classes. -/
theorem hom_ext_mk {C : Over S} {φ ψ : torsor ξ ⟶ C}
    (h : ∀ {Z : Over S} (g : Z ⟶ G.X) (a : Z ⟶ U), mk ξ g a ≫ φ = mk ξ g a ≫ ψ) : φ = ψ := by
  apply hom_ext_of_effectiveEpi (proj ξ)
  rw [proj_eq_mk]
  exact h _ _

theorem tensorHom_proj {W : Over S} {Z : Over S} (t : Z ⟶ W ⊗ trivialCover G U) :
    t ≫ (𝟙 W ⊗ₘ proj ξ) =
      lift (t ≫ fst _ _) (mk ξ (t ≫ snd _ _ ≫ fst G.X U) (t ≫ snd _ _ ≫ snd G.X U)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · rw [Category.assoc, tensorHom_snd, lift_snd, ← Category.assoc, proj_eq_mk, comp_mk]
    simp only [Category.assoc]

theorem tensorHom_proj_proj {Z : Over S} (t : Z ⟶ trivialCover G U ⊗ trivialCover G U) :
    t ≫ (proj ξ ⊗ₘ proj ξ) =
      lift (mk ξ (t ≫ fst _ _ ≫ fst G.X U) (t ≫ fst _ _ ≫ snd G.X U))
        (mk ξ (t ≫ snd _ _ ≫ fst G.X U) (t ≫ snd _ _ ≫ snd G.X U)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tensorHom_fst, lift_fst, ← Category.assoc, proj_eq_mk, comp_mk]
    simp only [Category.assoc]
  · rw [Category.assoc, tensorHom_snd, lift_snd, ← Category.assoc, proj_eq_mk, comp_mk]
    simp only [Category.assoc]

instance {W : Over S} : EffectiveEpi (𝟙 W ⊗ₘ proj ξ).left := by
  have : QuasiCompact (Over.Hom.left (𝟙 W)) := by rw [Over.id_left]; infer_instance
  have : Flat (Over.Hom.left (𝟙 W)) := by rw [Over.id_left]; infer_instance
  have : Surjective (Over.Hom.left (𝟙 W)) := by rw [Over.id_left]; infer_instance
  exact effectiveEpi_tensorHom _ _

instance : EffectiveEpi (proj ξ ⊗ₘ proj ξ).left := effectiveEpi_tensorHom _ _

/-- Morphisms out of `W ⊗ torsor` agree when they agree on all pairs of a point of `W` and a
class. -/
theorem hom_ext_tensor_mk {W C : Over S} {φ ψ : W ⊗ torsor ξ ⟶ C}
    (h : ∀ {Z : Over S} (w : Z ⟶ W) (g : Z ⟶ G.X) (a : Z ⟶ U),
      lift w (mk ξ g a) ≫ φ = lift w (mk ξ g a) ≫ ψ) : φ = ψ := by
  apply hom_ext_of_effectiveEpi (𝟙 W ⊗ₘ proj ξ)
  have e := tensorHom_proj ξ (𝟙 (W ⊗ trivialCover G U))
  rw [Category.id_comp] at e
  rw [e]
  exact h _ _ _

/-- Morphisms out of `torsor ⊗ torsor` agree when they agree on all pairs of classes. -/
theorem hom_ext_mk_mk {C : Over S} {φ ψ : torsor ξ ⊗ torsor ξ ⟶ C}
    (h : ∀ {Z : Over S} (g₁ : Z ⟶ G.X) (a₁ : Z ⟶ U) (g₂ : Z ⟶ G.X) (a₂ : Z ⟶ U),
      lift (mk ξ g₁ a₁) (mk ξ g₂ a₂) ≫ φ = lift (mk ξ g₁ a₁) (mk ξ g₂ a₂) ≫ ψ) : φ = ψ := by
  apply hom_ext_of_effectiveEpi (proj ξ ⊗ₘ proj ξ)
  have e := tensorHom_proj_proj ξ (𝟙 (trivialCover G U ⊗ trivialCover G U))
  rw [Category.id_comp] at e
  rw [e]
  exact h _ _ _ _

/-- Left multiplication on the trivial torsor over the cover. -/
def actCover : G.X ⊗ trivialCover G U ⟶ trivialCover G U :=
  lift (fst _ _ * (snd _ _ ≫ fst G.X U)) (snd _ _ ≫ snd G.X U)

omit [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Flat U.hom] [Surjective U.hom] in
theorem comp_actCover {Z : Over S} (t : Z ⟶ G.X ⊗ trivialCover G U) :
    t ≫ actCover = lift ((t ≫ fst _ _) * (t ≫ snd _ _ ≫ fst G.X U)) (t ≫ snd _ _ ≫ snd G.X U) := by
  rw [actCover, comp_lift, MonObj.comp_mul]

theorem comp_actCover_proj {Z : Over S} (t : Z ⟶ G.X ⊗ trivialCover G U) :
    t ≫ actCover ≫ proj ξ =
      mk ξ ((t ≫ fst _ _) * (t ≫ snd _ _ ≫ fst G.X U)) (t ≫ snd _ _ ≫ snd G.X U) := by
  rw [← Category.assoc, comp_actCover, mk]

theorem exists_smul : ∃ act : G.X ⊗ torsor ξ ⟶ torsor ξ,
    (𝟙 G.X ⊗ₘ proj ξ) ≫ act = actCover ≫ proj ξ := by
  refine exists_desc (𝟙 G.X ⊗ₘ proj ξ) (actCover ≫ proj ξ) (fun {Z} t₁ t₂ he => ?_)
  rw [tensorHom_proj, tensorHom_proj] at he
  have hg : t₁ ≫ fst _ _ = t₂ ≫ fst _ _ := by
    simpa only [lift_fst] using congrArg (· ≫ fst _ _) he
  have hm := congrArg (· ≫ snd _ _) he
  simp only [lift_snd] at hm
  rw [mk_eq_mk_iff] at hm
  rw [comp_actCover_proj, comp_actCover_proj, mk_eq_mk_iff, hm, hg, mul_assoc]

/-- The action of the group on the torsor. -/
def smul : G.X ⊗ torsor ξ ⟶ torsor ξ := (exists_smul ξ).choose

theorem lift_mk_smul {Z : Over S} (g h : Z ⟶ G.X) (a : Z ⟶ U) :
    lift g (mk ξ h a) ≫ smul ξ = mk ξ (g * h) a := by
  have e := tensorHom_proj ξ (lift g (lift h a))
  simp only [lift_fst, lift_snd_assoc, lift_fst, lift_snd] at e
  rw [← e, Category.assoc, smul, (exists_smul ξ).choose_spec, ← Category.assoc, comp_actCover]
  simp only [lift_fst, lift_snd_assoc, lift_snd]
  rfl

theorem smul_one_universal : lift (1 : torsor ξ ⟶ G.X) (𝟙 _) ≫ smul ξ = 𝟙 _ := by
  apply hom_ext_mk ξ
  intro Z g a
  rw [← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id, lift_mk_smul, one_mul]

theorem smul_mul_universal :
    lift ((fst (G.X ⊗ G.X) (torsor ξ) ≫ fst G.X G.X) * (fst _ _ ≫ snd G.X G.X)) (snd _ _) ≫
        smul ξ =
      lift (fst _ _ ≫ fst G.X G.X) (lift (fst _ _ ≫ snd G.X G.X) (snd _ _) ≫ smul ξ) ≫
        smul ξ := by
  apply hom_ext_tensor_mk ξ
  intro Z w g a
  rw [← Category.assoc, comp_lift, MonObj.comp_mul, lift_snd, lift_fst_assoc, lift_fst_assoc,
    lift_mk_smul, ← Category.assoc, comp_lift, lift_fst_assoc, ← Category.assoc, comp_lift,
    lift_fst_assoc, lift_snd, lift_mk_smul, lift_mk_smul, mul_assoc]

/-- The action of the group on the torsor of the cocycle. -/
@[instance_reducible]
def modObj : ModObj G.X (torsor ξ) :=
  schemeActionOfPointLaws (smul ξ)
    (fun x => by
      have h := congrArg (fun f => x ≫ f) (smul_one_universal ξ)
      simpa only [← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] using h)
    (fun h h' x => by
      have e := congrArg (fun f => lift (lift h h') x ≫ f) (smul_mul_universal ξ)
      simp only [← Category.assoc, comp_lift, MonObj.comp_mul, lift_snd, lift_fst] at e
      simpa only [Category.assoc, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e)

attribute [local instance] modObj

theorem smul_eq {Z : Over S} (m : Z ⟶ G.X) (x : Z ⟶ torsor ξ) : m • x = lift m x ≫ smul ξ :=
  rfl

theorem smul_mk {Z : Over S} (m g : Z ⟶ G.X) (a : Z ⟶ U) : m • mk ξ g a = mk ξ (m * g) a :=
  lift_mk_smul ξ m g a

omit [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Flat U.hom] [Surjective U.hom] in
private theorem group_aux {Γ : Type*} [Group Γ] (H₁ H₂ x y z w : Γ) (hxy : x * y = w * z) :
    H₂ * x * y * (H₁ * z)⁻¹ = H₂ * w * H₁⁻¹ := by
  calc H₂ * x * y * (H₁ * z)⁻¹ = H₂ * (x * y) * z⁻¹ * H₁⁻¹ := by group
    _ = H₂ * (w * z) * z⁻¹ * H₁⁻¹ := by rw [hxy]
    _ = H₂ * w * H₁⁻¹ := by group

/-- The difference `((h₁, a₁), (h₂, a₂)) ↦ h₂ ξ(a₂, a₁) h₁⁻¹` on pairs of points of the trivial
torsor over the cover. -/
def diffCover : trivialCover G U ⊗ trivialCover G U ⟶ G.X :=
  (snd _ _ ≫ fst G.X U) * ξ.toFun (snd _ _ ≫ snd G.X U) (fst _ _ ≫ snd G.X U) *
    (fst _ _ ≫ fst G.X U)⁻¹

omit [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Flat U.hom] [Surjective U.hom] in
theorem comp_diffCover {Z : Over S} (t : Z ⟶ trivialCover G U ⊗ trivialCover G U) :
    t ≫ diffCover ξ = (t ≫ snd _ _ ≫ fst G.X U) *
      ξ.toFun (t ≫ snd _ _ ≫ snd G.X U) (t ≫ fst _ _ ≫ snd G.X U) * (t ≫ fst _ _ ≫ fst G.X U)⁻¹ := by
  rw [diffCover, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← ξ.naturality]

theorem exists_diff : ∃ d : torsor ξ ⊗ torsor ξ ⟶ G.X, (proj ξ ⊗ₘ proj ξ) ≫ d = diffCover ξ := by
  refine exists_desc (proj ξ ⊗ₘ proj ξ) (diffCover ξ) (fun {Z} t₁ t₂ he => ?_)
  rw [tensorHom_proj_proj, tensorHom_proj_proj] at he
  have h1 := congrArg (· ≫ fst (torsor ξ) (torsor ξ)) he
  have h2 := congrArg (· ≫ snd (torsor ξ) (torsor ξ)) he
  simp only [lift_fst, lift_snd] at h1 h2
  rw [mk_eq_mk_iff] at h1 h2
  rw [comp_diffCover ξ t₁, comp_diffCover ξ t₂]
  rw [h1, h2]
  exact group_aux _ _ _ _ _ _ (by rw [← ξ.cocycle, ← ξ.cocycle])

/-- The difference of two points of the torsor: the group point carrying the first to the
second. -/
def diff : torsor ξ ⊗ torsor ξ ⟶ G.X := (exists_diff ξ).choose

theorem lift_mk_mk_diff {Z : Over S} (g₁ : Z ⟶ G.X) (a₁ : Z ⟶ U) (g₂ : Z ⟶ G.X) (a₂ : Z ⟶ U) :
    lift (mk ξ g₁ a₁) (mk ξ g₂ a₂) ≫ diff ξ = g₂ * ξ.toFun a₂ a₁ * g₁⁻¹ := by
  have e := tensorHom_proj_proj ξ (lift (lift g₁ a₁) (lift g₂ a₂))
  simp only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at e
  rw [← e, Category.assoc, diff, (exists_diff ξ).choose_spec, comp_diffCover]
  simp only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]

theorem diff_smul_universal : lift (diff ξ) (fst _ _) ≫ smul ξ = snd (torsor ξ) (torsor ξ) := by
  apply hom_ext_mk_mk ξ
  intro Z g₁ a₁ g₂ a₂
  rw [← Category.assoc, comp_lift, lift_mk_mk_diff, lift_fst, lift_snd, lift_mk_smul,
    mk_eq_mk_iff, inv_mul_cancel_right]

theorem smul_diff_universal :
    lift (snd G.X (torsor ξ)) (smul ξ) ≫ diff ξ = fst G.X (torsor ξ) := by
  apply hom_ext_tensor_mk ξ
  intro Z w g a
  rw [← Category.assoc, comp_lift, lift_snd, lift_mk_smul, lift_mk_mk_diff, lift_fst,
    Cocycle.toFun_self, mul_one, mul_inv_cancel_right]

/-- The action on the torsor of the cocycle is simply transitive on every test scheme. -/
theorem isIso_leftSMul : IsIso (ModObj.leftSMul G.X (torsor ξ)) := by
  rw [ModObj.isIso_leftSMul_iff]
  intro Z x y
  refine ⟨lift x y ≫ diff ξ, ?_, fun m hm => ?_⟩
  · have h := congrArg (fun f => lift x y ≫ f) (diff_smul_universal ξ)
    simp only [← Category.assoc, comp_lift, lift_fst, lift_snd] at h
    exact h
  · have h := congrArg (fun f => lift m x ≫ f) (smul_diff_universal ξ)
    simp only [← Category.assoc, comp_lift, lift_fst, lift_snd] at h
    rw [← h, ← smul_eq, hm]

/-- The point of the torsor over the cover: the class of the identity. -/
def point : U ⟶ torsor ξ := mk ξ 1 (𝟙 U)

theorem toFun_smul_point {Z : Over S} (a b : Z ⟶ U) :
    ξ.toFun a b • (b ≫ point ξ) = a ≫ point ξ := by
  rw [point, comp_mk, comp_mk, MonObj.comp_one, MonObj.comp_one, Category.comp_id,
    Category.comp_id, smul_mk, mul_one, mk_eq_mk_iff, one_mul]

theorem fst_smul_point : fst G.X U • (snd G.X U ≫ point ξ) = proj ξ := by
  rw [point, comp_mk, MonObj.comp_one, Category.comp_id, smul_mk, mul_one, proj_eq_mk]

theorem isPullback_point :
    IsPullback (snd G.X U).left (fst G.X U • (snd G.X U ≫ point ξ)).left U.hom
      (torsor ξ).hom := by
  rw [fst_smul_point]
  exact (quotient ξ).isPullback

theorem surjective_hom : Surjective (torsor ξ).hom := by
  have : Surjective G.X.hom := surjective_groupScheme_hom G
  have : Surjective (snd G.X U).left := inferInstanceAs (Surjective (pullback.snd G.X.hom U.hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (quotient ξ).isPullback
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

theorem smooth_hom [Smooth G.X.hom] : Smooth (torsor ξ).hom := by
  have : Smooth (snd G.X U).left := inferInstanceAs (Smooth (pullback.snd G.X.hom U.hom))
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (quotient ξ).isPullback
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end Torsor

end CocycleTorsor

/-- A torsor with a point over the cover whose cocycle is `ξ` and with a section over the base
trivializes `ξ`. -/
theorem Cocycle.isTrivial_of_torsor_section {S : Scheme.{u}}
    {G : GroupScheme S} {U X : Over S} [ModObj G.X X] (hX : IsIso (ModObj.leftSMul G.X X))
    (ξ : Cocycle G U) (u : U ⟶ X)
    (hu : ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b • (b ≫ u) = a ≫ u)
    (s : S ⟶ X.left) (hs : s ≫ X.hom = 𝟙 S) : ξ.IsTrivial := by
  let σ : 𝟙_ (Over S) ⟶ X := Over.homMk s hs
  let f : U ⟶ G.X := torsorDiff hX (toUnit U ≫ σ) u
  have hf : f • (toUnit U ≫ σ) = u := torsorDiff_smul hX _ _
  refine ⟨f, fun {Z} a b => ?_⟩
  have hpt (c : Z ⟶ U) : c ≫ u = (c ≫ f) • (toUnit Z ≫ σ) := by
    rw [← hf, ModObj.comp_smul, comp_toUnit_assoc]
  have h := hu a b
  rw [hpt a, hpt b, smul_smul] at h
  have e : ξ.toFun a b * (b ≫ f) = a ≫ f :=
    (eq_torsorDiff hX h).trans (eq_torsorDiff hX rfl).symm
  rw [← e, mul_inv_cancel_right]

/-- **Torsors of cocycles.** Over an affine base, every actual natural cocycle of an affine group
scheme on an affine flat surjective cover is the cocycle of an actual torsor with a point over
the cover. The torsor is affine and surjective over the base, and its pullback to the cover is
identified with the trivial torsor over the cover, compatibly with the point. -/
def CocycleTorsorExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (G : GroupScheme S) [IsAffineHom G.X.hom]
    (U : Over S) [IsAffine U.left] [Flat U.hom] [Surjective U.hom] (ξ : Cocycle G U),
    ∃ (X : Over S) (_ : ModObj G.X X) (_ : IsIso (ModObj.leftSMul G.X X)) (u : U ⟶ X),
      IsAffine X.left ∧ Surjective X.hom ∧
      IsPullback (snd G.X U).left (fst G.X U • (snd G.X U ≫ u)).left U.hom X.hom ∧
      ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b • (b ≫ u) = a ≫ u

theorem cocycleTorsorExistence : CocycleTorsorExistenceStatement.{u} := by
  intro S _ G _ U _ _ _ ξ
  let := CocycleTorsor.modObj ξ
  exact ⟨CocycleTorsor.torsor ξ, CocycleTorsor.modObj ξ, CocycleTorsor.isIso_leftSMul ξ,
    CocycleTorsor.point ξ, inferInstance, CocycleTorsor.surjective_hom ξ,
    CocycleTorsor.isPullback_point ξ, fun a b => CocycleTorsor.toFun_smul_point ξ a b⟩

end Langlands.GroupScheme
