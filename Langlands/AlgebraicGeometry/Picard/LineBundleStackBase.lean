import Langlands.AlgebraicGeometry.Picard.LineBundleStackDictionary
import Langlands.AlgebraicGeometry.Modules.LineBundleDescentEffectiveProof
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing

/-! # Base cases of descent for module realizations -/

universe u

open CategoryTheory Opposite Limits Bicategory AlgebraicGeometry
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open Langlands.Scheme.Modules Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- Compatibility of a family of module morphisms over a family `f` with all the composition
comparisons. -/
def ModCompat {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (M N : S.Modules)
    (φ : ∀ i, (Scheme.Modules.pullback (f i)).obj M ⟶ (Scheme.Modules.pullback (f i)).obj N) :
    Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (Scheme.Modules.pullback f₁).map (φ i₁) ≫ (compIso f₁ (f i₁) q hf₁ N).hom ≫
        (compIso f₂ (f i₂) q hf₂ N).inv =
      (compIso f₁ (f i₁) q hf₁ M).hom ≫ (compIso f₂ (f i₂) q hf₂ M).inv ≫
        (Scheme.Modules.pullback f₂).map (φ i₂)

/-- The square comparison through a common composite, with the module `compIso`. -/
lemma squarePullbackIso_hom_eq {Y X' Y' W : Scheme.{u}} (r : Y' ⟶ Y) (p' : W ⟶ X')
    (s : W ⟶ Y') (t : X' ⟶ Y) (hs : p' ≫ t = s ≫ r) (w : W ⟶ Y) (e₁ : p' ≫ t = w)
    (e₂ : s ≫ r = w) (N : Y.Modules) :
    (squarePullbackIso r p' s t hs N).hom = (compIso p' t w e₁ N).hom ≫ (compIso s r w e₂ N).inv :=
  UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso r p' s t hs w e₁ e₂ N

/-- The unit coherence of module pullbacks, as a composition comparison. -/
lemma map_pullbackId_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (C : Y.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app C) =
      (compIso f (𝟙 Y) f (Category.comp_id f) C).hom := by
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) C
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h
  have h' : (Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app C ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app C) =
        eqToHom (by simp) := by
    simpa using h
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app C), h']
  simp [compIso, UnitCocycleDescentUniqueness.compIso, Scheme.Modules.pullbackCongr]

namespace ModuleRealization

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} (R : ModuleRealization F)

/-- The isomorphism given by a module isomorphism. -/
def isoOfIso {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (E : R.mod M ≅ R.mod N) : M ≅ N where
  hom := R.ofIso E
  inv := R.ofIso E.symm
  hom_inv_id := R.hom_ext (by simp)
  inv_hom_id := R.hom_ext (by simp)

@[simp]
lemma modHom_isoOfIso_hom {X : Scheme.{u}} {M N : F.obj (.mk (op X))} (E : R.mod M ≅ R.mod N) :
    R.modHom (R.isoOfIso E).hom = E.hom :=
  R.modHom_ofIso E

section FullyFaithful

variable {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

/-- The module isomorphisms underlying a morphism of descent data between pulled-back
objects. -/
def descIso {M N : F.obj (.mk (op S))}
    (φ : (F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) (i : ι) :
    (Scheme.Modules.pullback (f i)).obj (R.mod M) ≅ (Scheme.Modules.pullback (f i)).obj (R.mod N) :=
  (R.mapIso (f i) M).symm ≪≫ R.modIso (φ.hom i) ≪≫ R.mapIso (f i) N

lemma descIso_hom {M N : F.obj (.mk (op S))}
    (φ : (F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) (i : ι) :
    (R.descIso f φ i).hom = (R.mapIso (f i) M).inv ≫ R.modHom (φ.hom i) ≫ (R.mapIso (f i) N).hom :=
  rfl

lemma modCompat_descIso {M N : F.obj (.mk (op S))}
    (φ : (F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) :
    ModCompat f (R.mod M) (R.mod N) (fun i ↦ (R.descIso f φ i).hom) := by
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  have h := congrArg R.μ (φ.comm q f₁ f₂ hf₁ hf₂)
  rw [R.μ_comp, R.μ_comp, R.μ_map, R.μ_map] at h
  erw [R.μ_ofObj_hom, R.μ_ofObj_hom] at h
  simp only [descIso_hom, Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((Scheme.Modules.pullback f₂).map (R.mapIso (f i₂) N).inv)]
  simp only [Category.assoc]
  rw [h]
  simp [Iso.map_inv_hom_id_assoc, Iso.map_hom_inv_id]

/-- Full faithfulness of the descent functor from unique gluing of module isomorphisms. -/
def fullyFaithfulToDescentData
    (H : ∀ (M N : S.Modules), IsLocallyFreeRankOne M → IsLocallyFreeRankOne N →
      ∀ (e : ∀ i, (Scheme.Modules.pullback (f i)).obj M ≅ (Scheme.Modules.pullback (f i)).obj N),
        ModCompat f M N (fun i ↦ (e i).hom) →
          ∃! E : M ≅ N, ∀ i, (Scheme.Modules.pullback (f i)).map E.hom = (e i).hom) :
    (F.toDescentData f).FullyFaithful where
  preimage {M N} φ := R.ofIso (H _ _ (R.rankOne M) (R.rankOne N) (R.descIso f φ)
    (R.modCompat_descIso f φ)).exists.choose
  map_preimage {M N} φ := by
    ext i
    apply R.hom_ext
    have hE := (H _ _ (R.rankOne M) (R.rankOne N) (R.descIso f φ)
      (R.modCompat_descIso f φ)).exists.choose_spec i
    change R.modHom ((F.map (f i).op.toLoc).toFunctor.map _) = _
    rw [R.modHom_map, R.modHom_ofIso, hE, descIso_hom]
    simp
  preimage_map {M N} ψ := by
    apply R.hom_ext
    have hu := (H _ _ (R.rankOne M) (R.rankOne N) (R.descIso f ((F.toDescentData f).map ψ))
      (R.modCompat_descIso f _)).unique
      (H _ _ (R.rankOne M) (R.rankOne N) (R.descIso f ((F.toDescentData f).map ψ))
        (R.modCompat_descIso f _)).exists.choose_spec
      (y₂ := R.modIso ψ) (fun i ↦ by
        rw [descIso_hom]
        change _ = _ ≫ R.modHom ((F.map (f i).op.toLoc).toFunctor.map ψ) ≫ _
        rw [R.modHom_map]
        simp)
    rw [R.modHom_ofIso, hu]
    rfl

end FullyFaithful

include R in
/-- Morphism descent along open covers. -/
lemma isPrestackFor_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) :
    F.IsPrestackFor (Presieve.ofArrows 𝒰.X 𝒰.f) := by
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff]
  refine ⟨R.fullyFaithfulToDescentData 𝒰.f fun M N _ _ e he ↦ ?_⟩
  refine openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing X 𝒰 M N e fun i j ↦ ?_
  have sq (L : X.Modules) : (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
      (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition L).hom =
      (compIso (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i) (pullback.fst _ _ ≫ 𝒰.f i) rfl L).hom ≫
        (compIso (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j) (pullback.fst _ _ ≫ 𝒰.f i)
          pullback.condition.symm L).inv :=
    UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso _ _ _ _ _ _ rfl
      pullback.condition.symm L
  rw [sq, sq]
  exact he (pullback.fst _ _ ≫ 𝒰.f i) (pullback.fst _ _) (pullback.snd _ _) rfl
    pullback.condition.symm

include R in
/-- Morphism descent along quasi-compact faithfully flat morphisms. -/
lemma isPrestackFor_singleton {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [Flat p]
    [Surjective p] : F.IsPrestackFor (Presieve.singleton p) := by
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isPrestackFor_ofArrows_iff]
  refine ⟨R.fullyFaithfulToDescentData (fun _ : PUnit.{1} ↦ p) fun M N hM hN e he ↦ ?_⟩
  obtain ⟨e₀, he₀, hu⟩ := LineBundleIsoDescent.lineBundleIsoDescent X Y p inferInstance
    inferInstance inferInstance M N hM hN (e PUnit.unit) (fun U a b h ↦ by
      rw [equalCompositeIso_hom_eq_compIso p a b h (a ≫ p) rfl h.symm,
        equalCompositeIso_hom_eq_compIso p a b h (a ≫ p) rfl h.symm]
      exact he (a ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) a b rfl h.symm)
  refine ⟨e₀, fun i ↦ by cases i; exact congrArg Iso.hom he₀, fun E hE ↦ hu E ?_⟩
  ext1
  exact hE PUnit.unit

section Pull

variable {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

lemma hom_congr' (D : F.DescentData f) {Z : Scheme.{u}} {q q' : Z ⟶ S} (hq : q = q')
    {i₁ i₂ : ι} (x₁ : Z ⟶ X i₁) (x₂ : Z ⟶ X i₂) (h₁ : x₁ ≫ f i₁ = q) (h₂ : x₂ ≫ f i₂ = q) :
    D.hom q x₁ x₂ h₁ h₂ = D.hom q' x₁ x₂ (h₁.trans hq) (h₂.trans hq) := by
  subst hq
  rfl

/-- Pullback of the module form of a descent morphism. -/
lemma map_μ_hom (D : F.DescentData f) {Z W : Scheme.{u}} (q : Z ⟶ S) {i₁ i₂ : ι}
    (x₁ : Z ⟶ X i₁) (x₂ : Z ⟶ X i₂) (hx₁ : x₁ ≫ f i₁ = q) (hx₂ : x₂ ≫ f i₂ = q) (g : W ⟶ Z)
    (y₁ : W ⟶ X i₁) (y₂ : W ⟶ X i₂) (h₁ : g ≫ x₁ = y₁) (h₂ : g ≫ x₂ = y₂) :
    (Scheme.Modules.pullback g).map (R.μ (D.hom q x₁ x₂ hx₁ hx₂)) =
      (compIso g x₁ y₁ h₁ (R.mod (D.obj i₁))).hom ≫
        R.μ (D.hom (g ≫ q) y₁ y₂ (by rw [← h₁, Category.assoc, hx₁])
          (by rw [← h₂, Category.assoc, hx₂])) ≫
        (compIso g x₂ y₂ h₂ (R.mod (D.obj i₂))).inv := by
  have h := congrArg R.μ (D.pullHom_hom g q (g ≫ q) rfl x₁ x₂ hx₁ hx₂ y₁ y₂ h₁ h₂)
  rw [R.μ_pullHom, tr] at h
  rw [← h]
  simp

end Pull

section OpenCover

variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u})

/-- The module transitions of a descent datum over an open cover. -/
def transition (D : F.DescentData 𝒰.f) (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (R.mod (D.obj i)) ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (R.mod (D.obj j)) :=
  R.μIso (D.hom (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) (pullback.fst _ _) (pullback.snd _ _)
    rfl pullback.condition.symm)

lemma transition_cocycle (D : F.DescentData 𝒰.f) :
    Langlands.Scheme.Modules.OpenCoverModuleGluing.CocycleCondition 𝒰
      (fun i ↦ R.mod (D.obj i)) (R.transition 𝒰 D) := by
  intro i j k
  apply Langlands.Scheme.Modules.OpenCoverModuleGluing.CompEq4.of_eq
  let fij := pullback.fst (𝒰.f i) (𝒰.f j)
  let sij := pullback.snd (𝒰.f i) (𝒰.f j)
  let fik := pullback.fst (𝒰.f i) (𝒰.f k)
  let sik := pullback.snd (𝒰.f i) (𝒰.f k)
  let fjk := pullback.fst (𝒰.f j) (𝒰.f k)
  let sjk := pullback.snd (𝒰.f j) (𝒰.f k)
  let a := pullback.fst fij fik
  let b := pullback.snd fij fik
  have hab : a ≫ fij = b ≫ fik := pullback.condition
  let l : pullback fij fik ⟶ pullback (𝒰.f j) (𝒰.f k) := pullback.lift (a ≫ sij) (b ≫ sik)
    (by simp only [a, b, fij, sij, fik, sik, Category.assoc, ← pullback.condition,
      pullback.condition_assoc])
  have hl₁ : l ≫ fjk = a ≫ sij := pullback.lift_fst _ _ _
  have hl₂ : l ≫ sjk = b ≫ sik := pullback.lift_snd _ _ _
  have hq₁ : l ≫ (fjk ≫ 𝒰.f j) = a ≫ (fij ≫ 𝒰.f i) := by
    rw [← Category.assoc, hl₁, Category.assoc, ← pullback.condition]
  have hq₂ : b ≫ (fik ≫ 𝒰.f i) = a ≫ (fij ≫ 𝒰.f i) := by
    rw [← Category.assoc, ← hab, Category.assoc]
  simp only [transition, μIso_hom]
  rw [R.map_μ_hom D _ fij sij rfl pullback.condition.symm a (a ≫ fij) (a ≫ sij) rfl rfl,
    R.map_μ_hom D _ fjk sjk rfl pullback.condition.symm l (a ≫ sij) (b ≫ sik) hl₁ hl₂,
    R.map_μ_hom D _ fik sik rfl pullback.condition.symm b (a ≫ fij) (b ≫ sik) hab.symm rfl,
    squarePullbackIso_hom_eq fjk a l sij _ (a ≫ sij) rfl hl₁,
    squarePullbackIso_hom_eq sik l b sjk _ (b ≫ sik) hl₂ rfl,
    squarePullbackIso_hom_eq fik a b fij _ (a ≫ fij) rfl hab.symm]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hom_congr' D hq₁ (a ≫ sij) (b ≫ sik), hom_congr' D hq₂ (a ≫ fij) (b ≫ sik),
    ← R.μ_comp_assoc, D.hom_comp]

/-- The line-bundle gluing data of a descent datum over an open cover. -/
abbrev gluingData (D : F.DescentData 𝒰.f) : LineBundleGluingData 𝒰 where
  bundle i := ⟨R.mod (D.obj i), R.rankOne _⟩
  transition := R.transition 𝒰 D
  cocycle := R.transition_cocycle 𝒰 D

/-- Transport of the transitions of the glued data along a map into an overlap. -/
lemma tr_transition (D : F.DescentData 𝒰.f) {Y : Scheme.{u}} (q : Y ⟶ X) {i₁ i₂ : 𝒰.I₀}
    (f₁ : Y ⟶ 𝒰.X i₁) (f₂ : Y ⟶ 𝒰.X i₂) (hf₁ : f₁ ≫ 𝒰.f i₁ = q) (hf₂ : f₂ ≫ 𝒰.f i₂ = q)
    (ℓ : Y ⟶ pullback (𝒰.f i₁) (𝒰.f i₂)) (hℓ₁ : ℓ ≫ pullback.fst _ _ = f₁)
    (hℓ₂ : ℓ ≫ pullback.snd _ _ = f₂) :
    tr ℓ hℓ₁ hℓ₂ (R.transition 𝒰 D i₁ i₂).hom =
      (Scheme.Modules.pullback f₁).map ((R.gluingData 𝒰 D).moduleIso i₁).inv ≫
        (compIso f₁ (𝒰.f i₁) q hf₁ (R.gluingData 𝒰 D).gluedModule).hom ≫
        (compIso f₂ (𝒰.f i₂) q hf₂ (R.gluingData 𝒰 D).gluedModule).inv ≫
        (Scheme.Modules.pullback f₂).map ((R.gluingData 𝒰 D).moduleIso i₂).hom := by
  let G := R.gluingData 𝒰 D
  have hℓq : ℓ ≫ (pullback.fst (𝒰.f i₁) (𝒰.f i₂) ≫ 𝒰.f i₁) = q := by
    rw [← Category.assoc, hℓ₁, hf₁]
  have hc := G.moduleIso_compatible i₁ i₂
  have hT : (R.transition 𝒰 D i₁ i₂).hom =
      (Scheme.Modules.pullback (pullback.fst (𝒰.f i₁) (𝒰.f i₂))).map (G.moduleIso i₁).inv ≫
        (squarePullbackIso (𝒰.f i₂) (pullback.fst (𝒰.f i₁) (𝒰.f i₂))
          (pullback.snd (𝒰.f i₁) (𝒰.f i₂)) (𝒰.f i₁) pullback.condition G.gluedModule).hom ≫
        (Scheme.Modules.pullback (pullback.snd (𝒰.f i₁) (𝒰.f i₂))).map
          (G.moduleIso i₂).hom := by
    rw [← cancel_epi ((Scheme.Modules.pullback (pullback.fst (𝒰.f i₁) (𝒰.f i₂))).map
      (G.moduleIso i₁).hom), Iso.map_hom_inv_id_assoc]
    exact hc
  rw [hT, squarePullbackIso_hom_eq _ _ _ _ _ _ rfl pullback.condition.symm,
    tr_comp ℓ hℓ₁ hℓ₁ hℓ₂, tr_comp ℓ hℓ₁ hℓ₂ hℓ₂, tr_comp ℓ hℓ₁ hℓq hℓ₂, tr_map, tr_map,
    tr_compIso ℓ _ _ _ rfl f₁ q hℓ₁ hℓq hf₁,
    tr_compIso_inv ℓ _ _ _ pullback.condition.symm f₂ q hℓ₂ hℓq hf₂]
  simp only [Category.assoc]
  rfl

include R in
/-- Effective descent along open covers. -/
lemma essSurj_openCover : (F.toDescentData 𝒰.f).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  let ι := R.ofModuleIso (R.gluingData 𝒰 D).gluedModule (R.gluingData 𝒰 D).gluedModule_rankOne
  let M := R.ofModule (R.gluingData 𝒰 D).gluedModule (R.gluingData 𝒰 D).gluedModule_rankOne
  let E : ∀ i, R.mod (((F.toDescentData 𝒰.f).obj M).obj i) ≅ R.mod (D.obj i) := fun i ↦
    R.mapIso (𝒰.f i) M ≪≫ (Scheme.Modules.pullback (𝒰.f i)).mapIso ι ≪≫
      (R.gluingData 𝒰 D).moduleIso i
  refine ⟨M, ⟨Pseudofunctor.DescentData.isoMk (fun i ↦ R.isoOfIso (E i)) ?_⟩⟩
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  refine R.μ_injective ?_
  let ℓ : Y ⟶ pullback (𝒰.f i₁) (𝒰.f i₂) := pullback.lift f₁ f₂ (hf₁.trans hf₂.symm)
  have hℓ₁ : ℓ ≫ pullback.fst _ _ = f₁ := pullback.lift_fst _ _ _
  have hℓ₂ : ℓ ≫ pullback.snd _ _ = f₂ := pullback.lift_snd _ _ _
  have hℓq : ℓ ≫ (pullback.fst (𝒰.f i₁) (𝒰.f i₂) ≫ 𝒰.f i₁) = q := by
    rw [← Category.assoc, hℓ₁, hf₁]
  rw [R.μ_comp, R.μ_comp, R.μ_map, R.μ_map,
    R.μ_toDescentData_obj_hom 𝒰.f M q f₁ f₂ hf₁ hf₂, modHom_isoOfIso_hom, modHom_isoOfIso_hom,
    ← D.pullHom_hom ℓ _ q hℓq (pullback.fst _ _) (pullback.snd _ _) rfl
      pullback.condition.symm f₁ f₂ hℓ₁ hℓ₂, R.μ_pullHom]
  erw [R.tr_transition 𝒰 D q f₁ f₂ hf₁ hf₂ ℓ hℓ₁ hℓ₂]
  simp only [E, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  congr 1
  erw [Iso.map_inv_hom_id_assoc]
  rw [Iso.map_hom_inv_id_assoc, compIso_naturality_assoc]
  congr 1
  rw [← cancel_epi (compIso f₂ (𝒰.f i₂) q hf₂ (R.mod M)).hom, Iso.hom_inv_id_assoc]
  erw [← compIso_naturality_assoc f₂ (𝒰.f i₂) q hf₂ ι.hom, Iso.hom_inv_id_assoc]

end OpenCover

section Singleton

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

lemma hom_congr_unit (D : F.DescentData (fun _ : Unit ↦ p)) {Z : Scheme.{u}} {q q' : Z ⟶ Y}
    (hq : q = q') (a b : Z ⟶ X) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    D.hom q (i₁ := ()) (i₂ := ()) a b ha hb =
      D.hom q' (i₁ := ()) (i₂ := ()) a b (ha.trans hq) (hb.trans hq) := by
  subst hq
  rfl

/-- The equal-composite descent datum of modules underlying a descent datum along `p`. -/
def datum (D : F.DescentData (fun _ : Unit ↦ p)) : Datum p (R.mod (D.obj ())) where
  θ U a b h := R.μIso (D.hom (a ≫ p) (i₁ := ()) (i₂ := ()) a b rfl h.symm)
  nat U V k a b h h' := by
    have h₂ := congrArg R.μ (D.pullHom_hom k (a ≫ p) ((k ≫ a) ≫ p) (by simp)
      (i₁ := ()) (i₂ := ()) a b rfl h.symm (k ≫ a) (k ≫ b) rfl rfl)
    rw [R.μ_pullHom] at h₂
    simp only [μIso_hom]
    rw [← h₂, tr, compIso_rfl, compIso_rfl]
    rfl
  coc U a b c h h' h'' := by
    simp only [μIso_hom]
    rw [← R.μ_comp, hom_congr_unit p D h.symm b c rfl h'.symm, D.hom_comp]

lemma datum_θ_hom (D : F.DescentData (fun _ : Unit ↦ p)) {U : Scheme.{u}} (a b : U ⟶ X)
    (h : a ≫ p = b ≫ p) :
    ((R.datum p D).θ U a b h).hom = R.μ (D.hom (a ≫ p) (i₁ := ()) (i₂ := ()) a b rfl h.symm) :=
  rfl

include R in
/-- Effective descent along affine faithfully flat morphisms with affine target. -/
lemma essSurj_singleton [IsAffineHom p] [Flat p] [Surjective p] [IsAffine Y] :
    (F.toDescentData (fun _ : Unit ↦ p)).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  obtain ⟨N, hN, ⟨S⟩⟩ := exists_str (R.datum p D) (R.rankOne _) (𝟙 Y)
  let F₀ := R.mod (D.obj ())
  have hs₀ : p ≫ 𝟙 Y = 𝟙 X ≫ p := by simp
  let γ₀ := S.γ X (𝟙 X) p hs₀
  let ι := R.ofModuleIso N hN
  let M := R.ofModule N hN
  let E : R.mod (((F.toDescentData (fun _ : Unit ↦ p)).obj M).obj ()) ≅ R.mod (D.obj ()) :=
    R.mapIso p M ≪≫ (Scheme.Modules.pullback p).mapIso ι ≪≫ γ₀ ≪≫
      (Scheme.Modules.pullbackId X).app F₀
  have n (Y' : Scheme.{u}) (f' : Y' ⟶ X) (q : Y' ⟶ Y) (hf' : f' ≫ p = q) :
      (Scheme.Modules.pullback f').map γ₀.hom =
        (compIso f' p q hf' N).hom ≫ (S.γ Y' f' q (by rw [Category.comp_id, hf'])).hom ≫
          (compIso f' (𝟙 X) f' (Category.comp_id f') F₀).inv := by
    rw [S.nat X Y' f' (𝟙 X) p hs₀ f' q (by rw [Category.comp_id, hf']) (Category.comp_id f') hf',
      tr]
    simp
    rfl
  refine ⟨M, ⟨Pseudofunctor.DescentData.isoMk (fun _ ↦ R.isoOfIso E) ?_⟩⟩
  rintro Y' q ⟨⟩ ⟨⟩ f₁ f₂ hf₁ hf₂
  refine R.μ_injective ?_
  rw [R.μ_comp, R.μ_comp, R.μ_map, R.μ_map,
    R.μ_toDescentData_obj_hom (fun _ : Unit ↦ p) M q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂,
    modHom_isoOfIso_hom, hom_congr_unit p D hf₁.symm f₁ f₂ hf₁ hf₂,
    ← datum_θ_hom R p D f₁ f₂ (hf₁.trans hf₂.symm)]
  simp only [E, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [n Y' f₁ q hf₁, n Y' f₂ q hf₂, map_pullbackId_hom_app, map_pullbackId_hom_app]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [S.coc Y' f₁ f₂ q (by rw [Category.comp_id, hf₁]) (by rw [Category.comp_id, hf₂])
      (hf₁.trans hf₂.symm), compIso_naturality_assoc, compIso_naturality_assoc,
    Iso.inv_hom_id_assoc]

end Singleton

end ModuleRealization

end Langlands.AlgebraicGeometry.Picard
