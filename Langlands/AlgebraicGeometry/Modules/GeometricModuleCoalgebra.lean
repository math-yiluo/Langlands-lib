import Langlands.AlgebraicGeometry.Modules.AffinePushforwardBaseChange
import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatPullbackDescent
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr
import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeComposition

/-! # Geometric cocycles and ordinary module coactions -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules
open Langlands.Scheme.Modules.LineBundleFlatDescent
open Langlands.AlgebraicGeometry.Modules.DerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules.GeometricModuleCoalgebra

section BaseChange

variable {X Y X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f : X ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The specified base-change map is also the mate of the inverse pullback square. -/
lemma pushforwardBaseChange_eq_unit_comp_counit (M : X.Modules) :
    pushforwardBaseChange g f f' g' w M =
      (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M)) ≫
        (Scheme.Modules.pushforward f').map
          ((pullbackSquareIso g f f' g' w).inv.app
              ((Scheme.Modules.pushforward f).obj M) ≫
            (Scheme.Modules.pullback g').map
              ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) := by
  have hu := pullback_map_unit_comp_pushforwardBaseChange g f f' g' w
    ((Scheme.Modules.pushforward f).obj M)
  have hn := pushforwardBaseChange_naturality g f f' g' w
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)
  symm
  rw [← hu, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← hn, ← Functor.map_comp_assoc]
  simp

end BaseChange

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The actual canonical cocycle on an ordinary pullback. -/
def pullbackDatum (M : Y.Modules) : Datum p ((Scheme.Modules.pullback p).obj M) where
  θ U a b h := equalCompositeIso p a b h M
  nat U V k a b h h' := by
    simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv] using
      congrArg Iso.hom (equalCompositeIso_precomp p a b M k h h')
  coc U a b c h h' h'' := by
    simpa only [Iso.trans_hom] using
      congrArg Iso.hom (equalCompositeIso_trans p a b c M h h' h'')

variable {p} {F : X.Modules}

/-- Evaluation of a pulled-back pushforward at another lift of the same base map. -/
def evaluation {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).obj
        ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward p).obj F)) ⟶
      (Scheme.Modules.pullback b).obj F :=
  (equalCompositeIso p a b h ((Scheme.Modules.pushforward p).obj F)).hom ≫
    (Scheme.Modules.pullback b).map
      ((Scheme.Modules.pullbackPushforwardAdjunction p).counit.app F)

/-- Evaluation commutes with further ordinary pullback. -/
lemma evaluation_tr {U V : Scheme.{u}} (k : V ⟶ U)
    {a b : U ⟶ X} {a' b' : V ⟶ X} (ha : k ≫ a = a') (hb : k ≫ b = b')
    (h : a ≫ p = b ≫ p) (h' : a' ≫ p = b' ≫ p) :
    tr k ha hb (evaluation (F := F) a b h) = evaluation a' b' h' := by
  unfold evaluation
  rw [tr_comp k ha hb hb, tr_map]
  congr 1
  exact ((pullbackDatum p ((Scheme.Modules.pushforward p).obj F)).θ_tr
    k ha hb h h').symm

/-- Changing the first lift and then evaluating is direct evaluation. -/
@[reassoc]
lemma evaluation_comp {U : Scheme.{u}} (a b c : U ⟶ X)
    (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p) (h'' : a ≫ p = c ≫ p) :
    (equalCompositeIso p a b h ((Scheme.Modules.pushforward p).obj F)).hom ≫
        evaluation b c h' = evaluation a c h'' := by
  unfold evaluation
  rw [← Category.assoc, ← Iso.trans_hom, equalCompositeIso_trans]

/-- The candidate coaction obtained by transporting the cocycle through actual affine
base change on the kernel pair. -/
def coaction [IsAffineHom p] [F.IsQuasicoherent] (D : Datum p F) :
    F ⟶ (Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward p).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd p p)).unit.app F ≫
    (Scheme.Modules.pushforward (pullback.snd p p)).map
      (D.θ _ (pullback.snd p p) (pullback.fst p p) pullback.condition.symm).hom ≫
    (affinePushforwardBaseChangeIso p p (pullback.snd p p) (pullback.fst p p)
      (IsPullback.of_hasPullback p p) F).inv

variable [IsAffineHom p] [F.IsQuasicoherent] (D : Datum p F)

lemma coaction_comp_baseChange :
    coaction D ≫ pushforwardBaseChange p p (pullback.snd p p) (pullback.fst p p)
        pullback.condition F =
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd p p)).unit.app F ≫
        (Scheme.Modules.pushforward (pullback.snd p p)).map
          (D.θ _ (pullback.snd p p) (pullback.fst p p) pullback.condition.symm).hom := by
  let e := affinePushforwardBaseChangeIso p p (pullback.snd p p) (pullback.fst p p)
    (IsPullback.of_hasPullback p p) F
  change (_ ≫ _ ≫ e.inv) ≫ e.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma coaction_evaluation_kernelPair :
    (Scheme.Modules.pullback (pullback.snd p p)).map (coaction D) ≫
        evaluation (pullback.snd p p) (pullback.fst p p) pullback.condition.symm =
      (D.θ _ (pullback.snd p p) (pullback.fst p p) pullback.condition.symm).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd p p)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit]
  have hB := pushforwardBaseChange_eq_unit_comp_counit p p
    (pullback.snd p p) (pullback.fst p p) pullback.condition F
  have he : (pullbackSquareIso p p (pullback.snd p p) (pullback.fst p p)
      pullback.condition).inv.app ((Scheme.Modules.pushforward p).obj F) =
      (equalCompositeIso p (pullback.snd p p) (pullback.fst p p)
        pullback.condition.symm ((Scheme.Modules.pushforward p).obj F)).hom := by
    change (equalCompositeIso p (pullback.fst p p) (pullback.snd p p)
      pullback.condition ((Scheme.Modules.pushforward p).obj F)).inv = _
    exact (congrArg Iso.hom (equalCompositeIso_symm p (pullback.fst p p)
      (pullback.snd p p) ((Scheme.Modules.pushforward p).obj F)
      pullback.condition pullback.condition.symm)).symm
  rw [he] at hB
  change coaction D ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd p p)).homEquiv _ _)
        (evaluation (pullback.snd p p) (pullback.fst p p) pullback.condition.symm) = _
  simp only [Adjunction.homEquiv_unit, evaluation]
  rw [← hB]
  exact coaction_comp_baseChange D

/-- The coaction recovers the given cocycle on every scheme test. -/
lemma coaction_evaluation {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map (coaction D) ≫ evaluation a b h =
      (D.θ U a b h).hom := by
  let l : U ⟶ pullback p p := pullback.lift b a h.symm
  have ha : l ≫ pullback.snd p p = a := pullback.lift_snd _ _ _
  have hb : l ≫ pullback.fst p p = b := pullback.lift_fst _ _ _
  have H := congrArg (tr l ha hb) (coaction_evaluation_kernelPair D)
  rw [tr_comp l ha ha hb, tr_map, evaluation_tr,
    ← D.θ_tr l ha hb pullback.condition.symm h] at H
  exact H

/-- The cocycle-derived coaction satisfies the actual adjunction counit law. -/
lemma coaction_counit :
    coaction D ≫ (Scheme.Modules.pullbackPushforwardAdjunction p).counit.app F = 𝟙 F := by
  have h := coaction_evaluation D (𝟙 X) (𝟙 X) rfl
  simp only [evaluation, equalCompositeIso_refl, Iso.refl_hom, Category.id_comp,
    D.θ_self] at h
  have hn := (Scheme.Modules.pullbackId X).hom.naturality
    (coaction D ≫ (Scheme.Modules.pullbackPushforwardAdjunction p).counit.app F)
  simp only [Functor.map_comp, Functor.id_map, h, Category.id_comp] at hn
  rw [← cancel_epi ((Scheme.Modules.pullbackId X).hom.app F)]
  erw [Category.comp_id]
  exact hn.symm

/-- Evaluation at all lifts detects morphisms into a pullback of `p^* p_* F`. -/
lemma evaluation_jointly_monic {U : Scheme.{u}} (a : U ⟶ X) {N : U.Modules}
    (m n : N ⟶ (Scheme.Modules.pullback a).obj
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pushforward p).obj F)))
    (h : ∀ (V : Scheme.{u}) (k : V ⟶ U) (b : V ⟶ X)
      (hb : (k ≫ a) ≫ p = b ≫ p),
      (Scheme.Modules.pullback k).map m ≫
          (compIso k a (k ≫ a) rfl _).hom ≫ evaluation (k ≫ a) b hb =
        (Scheme.Modules.pullback k).map n ≫
          (compIso k a (k ≫ a) rfl _).hom ≫ evaluation (k ≫ a) b hb) :
    m = n := by
  let q := a ≫ p
  let i := pullback.fst p q
  let j := pullback.snd p q
  let R := (Scheme.Modules.pushforward p).obj F
  let C := compIso a p q rfl R
  let B := affinePushforwardBaseChangeIso q p j i (IsPullback.of_hasPullback p q) F
  have hi : i ≫ p = j ≫ q := pullback.condition
  have hja : (j ≫ a) ≫ p = j ≫ q := Category.assoc _ _ _
  have hji : (j ≫ a) ≫ p = i ≫ p := hja.trans hi.symm
  have hs :
      (pullbackSquareIso q p j i hi).inv.app R =
        (compIso j q (j ≫ q) rfl R).hom ≫
          (compIso i p (j ≫ q) hi R).inv := by
    rw [← cancel_epi ((pullbackSquareIso q p j i hi).hom.app R),
      Iso.hom_inv_id_app]
    change 𝟙 _ = (squarePullbackIso q i j p hi R).hom ≫ _
    rw [UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso
      q i j p hi (j ≫ q) hi rfl]
    change 𝟙 _ = ((compIso i p (j ≫ q) hi R).hom ≫
      (compIso j q (j ≫ q) rfl R).inv) ≫
        (compIso j q (j ≫ q) rfl R).hom ≫ (compIso i p (j ≫ q) hi R).inv
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  have hc :
      (Scheme.Modules.pullback j).map C.hom ≫
        (pullbackSquareIso q p j i hi).inv.app R =
      (compIso j a (j ≫ a) rfl ((Scheme.Modules.pullback p).obj R)).hom ≫
        (equalCompositeIso p (j ≫ a) i hji R).hom := by
    rw [hs, equalCompositeIso_hom_eq_compIso p (j ≫ a) i hji (j ≫ q) hja hi]
    rw [← reassoc_of% (compIso_assoc j a p (j ≫ a) q (j ≫ q)
      rfl rfl rfl hja R)]
  have he (v : N ⟶ (Scheme.Modules.pullback a).obj
      ((Scheme.Modules.pullback p).obj R)) :
      ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
          (v ≫ C.hom ≫ B.hom) =
        (Scheme.Modules.pullback j).map v ≫
          (compIso j a (j ≫ a) rfl _).hom ≫ evaluation (j ≫ a) i hji := by
    change ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm
      ((v ≫ C.hom) ≫ pushforwardBaseChange q p j i hi F) = _
    rw [pushforwardBaseChange_eq_unit_comp_counit, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_symm_unit]
    simp only [Functor.map_comp, Category.id_comp, Category.assoc, evaluation]
    rw [reassoc_of% hc]
  rw [← cancel_mono (C.hom ≫ B.hom)]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).symm.injective
  simp only [he]
  exact h _ j i hji

/-- The cocycle-derived coaction is compatible with every geometric overlap. -/
lemma coaction_compatible {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) :
    (Scheme.Modules.pullback a).map (coaction D) ≫
        (equalCompositeIso p a b h ((Scheme.Modules.pushforward p).obj F)).hom =
      (D.θ U a b h).hom ≫ (Scheme.Modules.pullback b).map (coaction D) := by
  apply evaluation_jointly_monic b
  intro V k c hc
  have hab : (k ≫ a) ≫ p = (k ≫ b) ≫ p := by
    simpa only [Category.assoc] using congrArg (fun f => k ≫ f) h
  have hac : (k ≫ a) ≫ p = c ≫ p := hab.trans hc
  have hE := (pullbackDatum p ((Scheme.Modules.pushforward p).obj F)).θ_tr
    k rfl rfl h hab
  change (equalCompositeIso p (k ≫ a) (k ≫ b) hab
      ((Scheme.Modules.pushforward p).obj F)).hom =
    tr k rfl rfl (equalCompositeIso p a b h ((Scheme.Modules.pushforward p).obj F)).hom at hE
  have H :
      tr k rfl rfl ((Scheme.Modules.pullback a).map (coaction D) ≫
          (equalCompositeIso p a b h ((Scheme.Modules.pushforward p).obj F)).hom) ≫
        evaluation (k ≫ b) c hc =
      tr k rfl rfl ((D.θ U a b h).hom ≫
          (Scheme.Modules.pullback b).map (coaction D)) ≫
        evaluation (k ≫ b) c hc := by
    rw [tr_comp k rfl rfl rfl, tr_map, ← hE,
      tr_comp k rfl rfl rfl, ← D.θ_tr k rfl rfl h hab, tr_map]
    simp only [Category.assoc]
    rw [evaluation_comp (k ≫ a) (k ≫ b) c hab hc hac,
      coaction_evaluation D (k ≫ a) c hac, coaction_evaluation D (k ≫ b) c hc,
      D.coc V (k ≫ a) (k ≫ b) c hab hc hac]
  rw [← cancel_epi (compIso k a (k ≫ a) rfl F).inv]
  simpa only [tr, Category.assoc] using H

/-- The cocycle-derived coaction satisfies the actual comonad coassociativity law. -/
lemma coaction_coassoc :
    coaction D ≫ (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          ((Scheme.Modules.pushforward p).obj F)) =
      coaction D ≫ (Scheme.Modules.pullback p).map
        ((Scheme.Modules.pushforward p).map (coaction D)) := by
  let s := pullback.fst p p
  let t := pullback.snd p p
  let R := (Scheme.Modules.pushforward p).obj F
  let G := (Scheme.Modules.pullback p).obj R
  let E := equalCompositeIso p s t pullback.condition R
  let B (Q : X.Modules) := pushforwardBaseChange p p t s pullback.condition Q
  have : R.IsQuasicoherent := QuasicoherentLocal.isQuasicoherent_pushforward p F
  have hB : IsIso (B G) :=
    isIso_pushforwardBaseChange_of_isAffineHom p p t s (IsPullback.of_hasPullback p p) G
  have hunit :
      (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app R) ≫
        B G ≫ (Scheme.Modules.pushforward t).map E.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction t).unit.app G :=
    pullback_map_unit_comp_pushforwardBaseChange p p t s pullback.condition R
  have hco :
      coaction D ≫ B F ≫ (Scheme.Modules.pushforward t).map
          (D.θ _ s t pullback.condition).hom =
        (Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F := by
    rw [← Category.assoc]
    change (coaction D ≫ pushforwardBaseChange p p (pullback.snd p p)
        (pullback.fst p p) pullback.condition F) ≫ _ = _
    rw [coaction_comp_baseChange, Category.assoc, ← Functor.map_comp,
      D.coc _ t s t pullback.condition.symm pullback.condition rfl, D.θ_self]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have ha := coaction_compatible D s t pullback.condition
  change (Scheme.Modules.pullback s).map (coaction D) ≫ E.hom =
    (D.θ _ s t pullback.condition).hom ≫ (Scheme.Modules.pullback t).map (coaction D) at ha
  have hnat := pushforwardBaseChange_naturality p p t s pullback.condition (coaction D)
  change (Scheme.Modules.pullback p).map ((Scheme.Modules.pushforward p).map (coaction D)) ≫
      B G = B F ≫ (Scheme.Modules.pushforward t).map
        ((Scheme.Modules.pullback s).map (coaction D)) at hnat
  symm
  rw [← cancel_mono (B G ≫ (Scheme.Modules.pushforward t).map E.hom)]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, ← Functor.map_comp, ha, Functor.map_comp,
    reassoc_of% hco, hunit]
  exact ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.naturality (coaction D)).symm

/-- A genuine geometric cocycle gives a coalgebra for the specified module comonad. -/
def coalgebra : (modulePullbackDescentComonad p).Coalgebra where
  A := F
  a := coaction D
  counit := coaction_counit D
  coassoc := coaction_coassoc D

end Langlands.AlgebraicGeometry.Modules.GeometricModuleCoalgebra
