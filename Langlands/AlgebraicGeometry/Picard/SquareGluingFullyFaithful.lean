import Langlands.AlgebraicGeometry.Modules.TwoLegIsoGluing
import Langlands.AlgebraicGeometry.Modules.SquareLocalIsoLift
import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing

/-! # Full faithfulness of the actual Picard gluing comparison -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful

open Langlands.Scheme.Modules

variable {Y₀ Y₁ Y₂ Y : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)

/-- Over every affine open `U` of `Y`, the two inverse images receive maps from a
common corner over `Y₀` whose square of global sections is a ring pullback. -/
def AffineRestrictedCubes : Prop :=
  ∀ U : Y.Opens, IsAffineOpen U →
    ∃ (T₀ : Scheme.{u}) (ι₁ : T₀ ⟶ j₁ ⁻¹ᵁ U) (ι₂ : T₀ ⟶ j₂ ⁻¹ᵁ U) (g₀ : T₀ ⟶ Y₀),
      ι₁ ≫ (j₁ ⁻¹ᵁ U).ι = g₀ ≫ i₁ ∧ ι₂ ≫ (j₂ ⁻¹ᵁ U).ι = g₀ ≫ i₂ ∧
        IsPullback (j₁ ∣_ U).appTop (j₂ ∣_ U).appTop ι₁.appTop ι₂.appTop

variable (Y) in
/-- Any two actual line bundles are trivial on a common cover by affine opens. -/
def CommonAffineTrivializingCovers : Prop :=
  ∀ L L' : LineBundle Y, ∃ (ι : Type u) (U : ι → Y.Opens),
    (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
      ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.obj ≅
          structureModule (U i).toScheme) ∧
        Nonempty ((Scheme.Modules.pullback (U i).ι).obj L'.obj ≅
          structureModule (U i).toScheme)

/-- The two maps out of the apex of a pullback of rings jointly detect equality. -/
lemma eq_of_isPullback {R A B C : CommRingCat.{u}} {p : R ⟶ A} {q : R ⟶ B}
    {a : A ⟶ C} {b : B ⟶ C} (h : IsPullback p q a b) {r s : R}
    (hp : p r = p s) (hq : q r = q s) : r = s :=
  Types.ext_of_isPullback (h.map (forget CommRingCat)) hp hq

lemma appTop_comp_apply {X X' X'' : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ X'')
    (x : Γ(X'', ⊤)) : (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

include i₁ i₂ in
/-- Ring-pullback squares on affine opens make the unit maps to the two inverse
images jointly injective on every open subscheme. -/
lemma unitsJointlyInjectiveOnOpens (hR : AffineRestrictedCubes i₁ i₂ j₁ j₂) :
    TwoLegIsoGluing.UnitsJointlyInjectiveOnOpens j₁ j₂ := by
  apply TwoLegIsoGluing.unitsJointlyInjectiveOnOpens_of_affine
  intro T t hT ht s s' hss'
  have := hT
  have := ht
  simp only [Prod.mk.injEq] at hss'
  obtain ⟨h₁, h₂⟩ := hss'
  let U := t.opensRange
  obtain ⟨T₀, ι₁, ι₂, g₀, -, -, hP⟩ := hR U (isAffineOpen_opensRange t)
  let φ := t.isoOpensRange
  have key (V : Scheme.{u}) (j : V ⟶ Y)
      (hj : Units.map (pullback.snd j t).appTop.hom.toMonoidHom s =
        Units.map (pullback.snd j t).appTop.hom.toMonoidHom s') :
      (j ∣_ U).appTop (φ.inv.appTop s.val) = (j ∣_ U).appTop (φ.inv.appTop s'.val) := by
    let q : (j ⁻¹ᵁ U).toScheme ⟶ pullback j t :=
      pullback.lift (j ⁻¹ᵁ U).ι ((j ∣_ U) ≫ φ.inv) (by
        simp [φ, U, morphismRestrict_ι])
    have hq : q ≫ pullback.snd j t = (j ∣_ U) ≫ φ.inv := pullback.lift_snd _ _ _
    have hv := congrArg (fun v : Γ(pullback j t, ⊤)ˣ ↦ q.appTop v.val) hj
    simp only [Units.coe_map] at hv
    rw [← appTop_comp_apply, ← appTop_comp_apply, ← hq, appTop_comp_apply,
      appTop_comp_apply]
    exact hv
  have hinv (x : Γ(T, ⊤)) : φ.hom.appTop (φ.inv.appTop x) = x := by
    rw [← appTop_comp_apply, Iso.hom_inv_id]
    rfl
  apply Units.ext
  have he := eq_of_isPullback hP (key Y₁ j₁ h₁) (key Y₂ j₂ h₂)
  rw [← hinv s.val, ← hinv s'.val, he]

variable (w : i₁ ≫ j₁ = i₂ ≫ j₂)

include w in
/-- On a common affine trivializing cover, isomorphisms compatible on the base
square glue uniquely to an actual isomorphism with both prescribed pullbacks. -/
lemma existsUnique_iso (hR : AffineRestrictedCubes i₁ i₂ j₁ j₂)
    (hcov : CommonAffineTrivializingCovers Y) {L L' : LineBundle Y}
    (e₁ : (Scheme.Modules.pullback j₁).obj L.obj ≅ (Scheme.Modules.pullback j₁).obj L'.obj)
    (e₂ : (Scheme.Modules.pullback j₂).obj L.obj ≅ (Scheme.Modules.pullback j₂).obj L'.obj)
    (he : (Scheme.Modules.pullback i₁).map e₁.hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w L'.obj).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w L.obj).hom ≫
        (Scheme.Modules.pullback i₂).map e₂.hom) :
    ∃! E₀ : L.obj ≅ L'.obj, (Scheme.Modules.pullback j₁).mapIso E₀ = e₁ ∧
      (Scheme.Modules.pullback j₂).mapIso E₀ = e₂ := by
  obtain ⟨ι, U, hU, hsup, htriv⟩ := hcov L L'
  let 𝒰 := Y.openCoverOfIsOpenCover U hsup
  refine TwoLegIsoGluing.existsUnique_iso_of_local j₁ j₂ e₁ e₂
    (unitsJointlyInjectiveOnOpens i₁ i₂ j₁ j₂ hR) 𝒰
    (fun i ↦ (htriv i).1) (fun i ↦ (htriv i).2) (fun i ↦ ?_)
  obtain ⟨T₀, ι₁, ι₂, g₀, k₁, k₂, hP⟩ := hR (U i) (hU i)
  have wT : ι₁ ≫ (j₁ ∣_ U i) = ι₂ ≫ (j₂ ∣_ U i) := by
    rw [← cancel_mono (U i).ι]
    simp only [Category.assoc, morphismRestrict_ι]
    rw [reassoc_of% k₁, reassoc_of% k₂, w]
  exact SquareLocalIsoLift.exists_compatible_lift i₁ i₂ j₁ j₂ w (U i).ι
    (j₁ ∣_ U i) (j₂ ∣_ U i) ι₁ ι₂ wT (j₁ ⁻¹ᵁ U i).ι (j₂ ⁻¹ᵁ U i).ι g₀ k₁ k₂ e₁ e₂
    (isPullback_morphismRestrict j₁ (U i)).flip (isPullback_morphismRestrict j₂ (U i)).flip
    hP (htriv i).1.some (htriv i).2.some he

/-- The equality-induced arrow of actual Picard groupoids has the equality-induced
underlying module map. -/
lemma eqToHom_iso_hom_hom {X : Scheme.{u}} {A B : PicardGroupoid X} (e : A = B) :
    (eqToHom e).iso.hom.hom = eqToHom (congrArg (fun A : PicardGroupoid X ↦ A.of.obj) e) := by
  subst e
  rfl

/-- The Picard square comparison has the ordinary module square comparison as its
underlying map. -/
lemma squarePullbackIso_app (L : PicardGroupoid Y) :
    ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L).iso.hom.hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w L.of.obj).hom := by
  simp only [PicardGroupoid.squarePullbackIso, squarePullbackIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, coreCategory_comp_iso, eqToIso.hom, eqToHom_app,
    ObjectProperty.FullSubcategory.comp_hom, Iso.app_hom, Iso.app_inv,
    Scheme.Modules.pullbackCongr]
  rw [eqToHom_iso_hom_hom]
  rfl

variable {i₁ i₂ j₁ j₂ w}

/-- The first leg of an arrow of gluing data, as an isomorphism of modules. -/
def leftIso {L L' : PicardGroupoid Y}
    (φ : (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L ⟶
      (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L') :
    (Scheme.Modules.pullback j₁).obj L.of.obj ≅ (Scheme.Modules.pullback j₁).obj L'.of.obj :=
  (LineBundle.forget Y₁).mapIso φ.left.iso

/-- The second leg of an arrow of gluing data, as an isomorphism of modules. -/
def rightIso {L L' : PicardGroupoid Y}
    (φ : (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L ⟶
      (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L') :
    (Scheme.Modules.pullback j₂).obj L.of.obj ≅ (Scheme.Modules.pullback j₂).obj L'.of.obj :=
  (LineBundle.forget Y₂).mapIso φ.right.iso

/-- The two legs of an arrow of gluing data agree over the base square. -/
lemma leftIso_compatible {L L' : PicardGroupoid Y}
    (φ : (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L ⟶
      (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).obj L') :
    (Scheme.Modules.pullback i₁).map (leftIso φ).hom ≫
        (squarePullbackIso j₂ i₁ i₂ j₁ w L'.of.obj).hom =
      (squarePullbackIso j₂ i₁ i₂ j₁ w L.of.obj).hom ≫
        (Scheme.Modules.pullback i₂).map (rightIso φ).hom := by
  have h := congrArg (fun f ↦ f.iso.hom.hom) φ.w
  change (Scheme.Modules.pullback i₁).map φ.left.iso.hom.hom ≫
      ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L').iso.hom.hom =
    ((PicardGroupoid.squarePullbackIso i₁ i₂ j₁ j₂ w).hom.app L).iso.hom.hom ≫
      (Scheme.Modules.pullback i₂).map φ.right.iso.hom.hom at h
  rw [squarePullbackIso_app, squarePullbackIso_app] at h
  exact h

variable (i₁ i₂ j₁ j₂ w)

/-- Under the affine restricted-cube and common-cover hypotheses, the actual
Picard comparison into gluing data is fully faithful. -/
def fullyFaithful (hR : AffineRestrictedCubes i₁ i₂ j₁ j₂)
    (hcov : CommonAffineTrivializingCovers Y) :
    (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).FullyFaithful where
  preimage {L L'} φ := (Core.isoMk (ObjectProperty.isoMk _
    (existsUnique_iso i₁ i₂ j₁ j₂ w hR hcov (leftIso φ) (rightIso φ)
      (leftIso_compatible φ)).exists.choose)).hom
  map_preimage {L L'} φ := by
    have hE := (existsUnique_iso i₁ i₂ j₁ j₂ w hR hcov (leftIso φ) (rightIso φ)
      (leftIso_compatible φ)).exists.choose_spec
    apply Comma.hom_ext
    · apply Core.hom_ext
      apply ObjectProperty.hom_ext
      exact congrArg Iso.hom hE.1
    · apply Core.hom_ext
      apply ObjectProperty.hom_ext
      exact congrArg Iso.hom hE.2
  preimage_map {L L'} a := by
    have hu := (existsUnique_iso i₁ i₂ j₁ j₂ w hR hcov
      (leftIso ((PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).map a))
      (rightIso ((PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).map a))
      (leftIso_compatible _))
    have h := hu.unique hu.exists.choose_spec
      (y₂ := (LineBundle.forget Y).mapIso a.iso) ⟨Iso.ext rfl, Iso.ext rfl⟩
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    exact congrArg Iso.hom h

/-- The actual Picard comparison into gluing data is full. -/
lemma full (hR : AffineRestrictedCubes i₁ i₂ j₁ j₂)
    (hcov : CommonAffineTrivializingCovers Y) :
    (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).Full :=
  (fullyFaithful i₁ i₂ j₁ j₂ w hR hcov).full

/-- The actual Picard comparison into gluing data is faithful. -/
lemma faithful (hR : AffineRestrictedCubes i₁ i₂ j₁ j₂)
    (hcov : CommonAffineTrivializingCovers Y) :
    (PicardGroupoid.squareGluingComparison i₁ i₂ j₁ j₂ w).Faithful :=
  (fullyFaithful i₁ i₂ j₁ j₂ w hR hcov).faithful

end Langlands.AlgebraicGeometry.Picard.SquareGluingFullyFaithful
