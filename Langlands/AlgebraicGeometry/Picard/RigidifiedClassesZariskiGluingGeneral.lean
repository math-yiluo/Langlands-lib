import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedGeneral

/-! # Zariski gluing of rigidified classes for general relative schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- Rigidified isomorphisms are unique over any base identified with a relative space. -/
lemma rigidifiedIso_subsingleton_of_iso
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (V : Over S)
    {Y : Scheme.{u}} (Q : (relativeSpace f).obj V ≅ Y) {σ : V.left ⟶ Y}
    (hσ : (relativeSection f ε section_eq).app V ≫ Q.hom = σ)
    (L M : RigidifiedLineBundle σ) : Subsingleton (L ≅ M) := by
  constructor
  intro α β
  let F := RigidifiedLineBundle.pullback Q.hom (𝟙 V.left)
    (by rw [hσ, Category.id_comp] :
      (relativeSection f ε section_eq).app V ≫ Q.hom =
        𝟙 V.left ≫ σ)
  have h := (unique V (F.obj L) (F.obj M)).elim (F.mapIso α) (F.mapIso β)
  have hv : (Scheme.Modules.pullback Q.hom).map α.hom.hom.val =
      (Scheme.Modules.pullback Q.hom).map β.hom.hom.val :=
    congrArg (fun e ↦ e.hom.hom.val) h
  apply Iso.ext
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact Langlands.Scheme.Modules.pullback_map_injective_of_iso Q hv

/-- The relative section, transported along identifications of relative spaces. -/
lemma relativeSection_comp_square {V V' : Over S}
    (h : V ⟶ V') {Y : Scheme.{u}} (Q : (relativeSpace f).obj V ≅ Y)
    (m : Y ⟶ (relativeSpace f).obj V')
    (hm : Q.hom ≫ m = (relativeSpace f).map h) :
    ((relativeSection f ε section_eq).app V ≫ Q.hom) ≫ m =
      h.left ≫ (relativeSection f ε section_eq).app V' := by
  rw [Category.assoc, hm]
  exact ((relativeSection f ε section_eq).naturality h).symm

/-- The relative section, carried through chosen maps out of two relative spaces. -/
lemma relativeSection_comp_square' {V V' : Over S}
    (h : V ⟶ V') {Y Y' : Scheme.{u}} (g : (relativeSpace f).obj V ⟶ Y)
    (n : (relativeSpace f).obj V' ⟶ Y') (m : Y ⟶ Y')
    (hm : g ≫ m = (relativeSpace f).map h ≫ n) :
    ((relativeSection f ε section_eq).app V ≫ g) ≫ m =
      h.left ≫ (relativeSection f ε section_eq).app V' ≫ n := by
  rw [Category.assoc, hm, ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((relativeSection f ε section_eq).naturality h).symm

/-- A rigidified isomorphism over a slice object, transported to an identified total space. -/
def isoTransport {V U U' : Over S}
    (a : V ⟶ U) (b : V ⟶ U') {P : Scheme.{u}}
    (Q : (relativeSpace f).obj V ≅ P) (fa : P ⟶ (relativeSpace f).obj U)
    (fb : P ⟶ (relativeSpace f).obj U')
    (ha : Q.hom ≫ fa = (relativeSpace f).map a)
    (hb : Q.hom ≫ fb = (relativeSpace f).map b)
    {L : relative f ε section_eq U} {M : relative f ε section_eq U'}
    (Φ : (RigidifiedLineBundle.relativePullback f ε section_eq
        a).obj L ≅
      (RigidifiedLineBundle.relativePullback f ε section_eq
        b).obj M) :
    (RigidifiedLineBundle.pullback fa a.left (relativeSection_comp_square f ε section_eq a Q fa ha)).obj L ≅
      (RigidifiedLineBundle.pullback fb b.left (relativeSection_comp_square f ε section_eq b Q fb hb)).obj M :=
  ((RigidifiedLineBundle.pullbackCompTo
      (ε'' := (relativeSection f ε section_eq).app V ≫ Q.hom)
      ((relativeSpace f).map a) a.left Q.inv (𝟙 V.left) fa a.left
      (by rw [← ha, Iso.inv_hom_id_assoc]) (Category.id_comp _)
      ((relativeSection f ε section_eq).naturality a).symm
      (by simp) _).app L).symm ≪≫
    (RigidifiedLineBundle.pullback
      (ε := (relativeSection f ε section_eq).app V)
      (ε' := (relativeSection f ε section_eq).app V ≫ Q.hom)
      Q.inv (𝟙 V.left) (by simp)).mapIso Φ ≪≫
    (RigidifiedLineBundle.pullbackCompTo
      (ε'' := (relativeSection f ε section_eq).app V ≫ Q.hom)
      ((relativeSpace f).map b) b.left Q.inv (𝟙 V.left) fb b.left
      (by rw [← hb, Iso.inv_hom_id_assoc]) (Category.id_comp _)
      ((relativeSection f ε section_eq).naturality b).symm
      (by simp) _).app M

section Gluing

variable (T : Over S) (𝒰 : T.left.OpenCover.{u})

/-- The relative space of a pairwise base overlap is the overlap of the induced cover. -/
def overlapIso (i j : 𝒰.I₀) :
    (relativeSpace f).obj (Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≅
      CategoryTheory.Limits.pullback ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j) :=
  ((relativeSpace f).map_isPullback (Langlands.AbelianScheme.over_isPullback T (𝒰.f i) (𝒰.f j))).isoPullback

@[reassoc]
lemma overlapIso_hom_fst (i j : 𝒰.I₀) :
    (overlapIso f T 𝒰 i j).hom ≫ pullback.fst _ _ =
      (relativeSpace f).map (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
        Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶ Over.mk (𝒰.f i ≫ T.hom)) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
lemma overlapIso_hom_snd (i j : 𝒰.I₀) :
    (overlapIso f T 𝒰 i j).hom ≫ pullback.snd _ _ =
      (relativeSpace f).map (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
          (by simp [pullback.condition_assoc]) :
        Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶ Over.mk (𝒰.f j ≫ T.hom)) :=
  IsPullback.isoPullback_hom_snd _

/-- The relative section on the pairwise overlap of the induced cover. -/
def overlapSection (i j : 𝒰.I₀) :
    CategoryTheory.Limits.pullback (𝒰.f i) (𝒰.f j) ⟶
      CategoryTheory.Limits.pullback ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j) :=
  (relativeSection f ε section_eq).app
    (Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≫ (overlapIso f T 𝒰 i j).hom

@[reassoc]
lemma overlapSection_fst (i j : 𝒰.I₀) :
    overlapSection f ε section_eq T 𝒰 i j ≫ pullback.fst _ _ =
      pullback.fst (𝒰.f i) (𝒰.f j) ≫
        (relativeSection f ε section_eq).app
          (Over.mk (𝒰.f i ≫ T.hom)) :=
  relativeSection_comp_square f ε section_eq _ _ _ (overlapIso_hom_fst f T 𝒰 i j)

@[reassoc]
lemma overlapSection_snd (i j : 𝒰.I₀) :
    overlapSection f ε section_eq T 𝒰 i j ≫ pullback.snd _ _ =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫
        (relativeSection f ε section_eq).app
          (Over.mk (𝒰.f j ≫ T.hom)) :=
  relativeSection_comp_square f ε section_eq _ _ _ (overlapIso_hom_snd f T 𝒰 i j)

/-- The base triple overlap map to the second pairwise overlap. -/
def tripleLift (i j k : 𝒰.I₀) :
    CategoryTheory.Limits.pullback (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ⟶
      CategoryTheory.Limits.pullback (𝒰.f j) (𝒰.f k) :=
  pullback.lift
    (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
      pullback.snd (𝒰.f i) (𝒰.f j))
    (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
      pullback.snd (𝒰.f i) (𝒰.f k))
    (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc])

/-- The relative space of a base triple overlap is the triple overlap of the induced cover. -/
def tripleIso (i j k : 𝒰.I₀) :
    (relativeSpace f).obj
        (Over.mk (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
          pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≅
      CategoryTheory.Limits.pullback (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
        (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f k)) :=
  IsPullback.isoPullback
    (((relativeSpace f).map_isPullback
      (Langlands.AbelianScheme.over_isPullback (Over.mk (𝒰.f i ≫ T.hom)) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f k)))).of_iso (Iso.refl _) (overlapIso f T 𝒰 i j)
      (overlapIso f T 𝒰 i k) (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
      (by rw [Iso.refl_hom, Category.comp_id, overlapIso_hom_fst])
      (by rw [Iso.refl_hom, Category.comp_id, overlapIso_hom_fst]))

/-- The relative section on the triple overlap of the induced cover. -/
def tripleSection (i j k : 𝒰.I₀) :
    CategoryTheory.Limits.pullback (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ⟶
      CategoryTheory.Limits.pullback (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
        (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f k)) :=
  (relativeSection f ε section_eq).app
      (Over.mk (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
          pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)) ≫
    (tripleIso f T 𝒰 i j k).hom

@[reassoc]
lemma tripleSection_fst (i j k : 𝒰.I₀) :
    tripleSection f ε section_eq T 𝒰 i j k ≫ pullback.fst _ _ =
      pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        overlapSection f ε section_eq T 𝒰 i j := by
  unfold tripleSection overlapSection
  exact relativeSection_comp_square' f ε section_eq _ _ _ _ (IsPullback.isoPullback_hom_fst _)

@[reassoc]
lemma tripleSection_snd (i j k : 𝒰.I₀) :
    tripleSection f ε section_eq T 𝒰 i j k ≫ pullback.snd _ _ =
      pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        overlapSection f ε section_eq T 𝒰 i k := by
  unfold tripleSection overlapSection
  exact relativeSection_comp_square' f ε section_eq _ _ _ _ (IsPullback.isoPullback_hom_snd _)

@[reassoc]
lemma tripleLift_fst (i j k : 𝒰.I₀) :
    tripleLift T 𝒰 i j k ≫ pullback.fst (𝒰.f j) (𝒰.f k) =
      pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f j) :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma tripleLift_snd (i j k : 𝒰.I₀) :
    tripleLift T 𝒰 i j k ≫ pullback.snd (𝒰.f j) (𝒰.f k) =
      pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f k) :=
  pullback.lift_snd _ _ _

/-- The relative sections on triple and pairwise overlaps are compatible with the lift. -/
lemma tripleSection_lift (i j k : 𝒰.I₀)
    (w : (pullback.fst
          (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
          (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f k)) ≫
        pullback.snd ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j)) ≫
          (relativeOpenCover f T 𝒰).f j =
      (pullback.snd
          (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
          (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f k)) ≫
        pullback.snd ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f k)) ≫
          (relativeOpenCover f T 𝒰).f k) :
    tripleSection f ε section_eq T 𝒰 i j k ≫ pullback.lift _ _ w =
      tripleLift T 𝒰 i j k ≫ overlapSection f ε section_eq T 𝒰 j k := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, tripleSection_fst_assoc, overlapSection_snd,
      Category.assoc, overlapSection_fst, tripleLift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, tripleSection_snd_assoc, overlapSection_snd,
      Category.assoc, overlapSection_snd, tripleLift_snd_assoc]

/-- A rigidified overlap isomorphism, transported to the overlap of the induced cover. -/
def overlapRigidIso (i j : 𝒰.I₀) {L : relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom))}
    {M : relative f ε section_eq (Over.mk (𝒰.f j ≫ T.hom))}
    (Φ : (RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj L ≅
      (RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj M) :
    (RigidifiedLineBundle.pullback (ε' := overlapSection f ε section_eq T 𝒰 i j) (pullback.fst _ _)
        (pullback.fst (𝒰.f i) (𝒰.f j)) (overlapSection_fst f ε section_eq T 𝒰 i j)).obj L ≅
      (RigidifiedLineBundle.pullback (ε' := overlapSection f ε section_eq T 𝒰 i j) (pullback.snd _ _)
        (pullback.snd (𝒰.f i) (𝒰.f j)) (overlapSection_snd f ε section_eq T 𝒰 i j)).obj M :=
  isoTransport f ε section_eq _ _ (overlapIso f T 𝒰 i j) _ _ (overlapIso_hom_fst f T 𝒰 i j)
    (overlapIso_hom_snd f T 𝒰 i j) Φ

/-- The transported overlap isomorphisms of rigidified families glue to a module sheaf. -/
lemma exists_glued
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (glue : Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u})
    (L : ∀ i, relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (Φ : ∀ i j,
      (RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj (L i) ≅
      (RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj (L j)) :
    ∃ (N : ((relativeSpace f).obj T).Modules)
      (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅
        (L i).obj.carrier),
      ∀ i j,
        (Scheme.Modules.pullback (pullback.fst ((relativeOpenCover f T 𝒰).f i)
            ((relativeOpenCover f T 𝒰).f j))).map (ψ i).hom ≫
          (overlapRigidIso f ε section_eq T 𝒰 i j (Φ i j)).hom.hom.val =
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeOpenCover f T 𝒰).f j)
            (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
            (pullback.snd ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
            ((relativeOpenCover f T 𝒰).f i) pullback.condition N).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeOpenCover f T 𝒰).f i)
            ((relativeOpenCover f T 𝒰).f j))).map (ψ j).hom := by
  refine glue _ (relativeOpenCover f T 𝒰) (fun i ↦ (L i).obj.carrier)
    (fun i j ↦ (RigidifiedLineBundle.forgetModule (overlapSection f ε section_eq T 𝒰 i j)).mapIso
      (overlapRigidIso f ε section_eq T 𝒰 i j (Φ i j))) ?_
  intro i j k
  have cs := tripleSection_lift f ε section_eq T 𝒰 i j k
    (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc])
  let α := (RigidifiedLineBundle.pullback _ _ (tripleSection_fst f ε section_eq T 𝒰 i j k)).mapIso
      (overlapRigidIso f ε section_eq T 𝒰 i j (Φ i j)) ≪≫
    RigidifiedLineBundle.squareIso _ _ (overlapSection_snd f ε section_eq T 𝒰 i j) _ _
      (overlapSection_fst f ε section_eq T 𝒰 j k) _ _ (tripleSection_fst f ε section_eq T 𝒰 i j k) _ _ cs
      (pullback.lift_fst _ _ _).symm (tripleLift_fst T 𝒰 i j k).symm (L j) ≪≫
    (RigidifiedLineBundle.pullback _ _ cs).mapIso (overlapRigidIso f ε section_eq T 𝒰 j k (Φ j k)) ≪≫
    RigidifiedLineBundle.squareIso _ _ (overlapSection_snd f ε section_eq T 𝒰 j k) _ _
      (overlapSection_snd f ε section_eq T 𝒰 i k) _ _ cs _ _ (tripleSection_snd f ε section_eq T 𝒰 i j k)
      (pullback.lift_snd _ _ _) (tripleLift_snd T 𝒰 i j k) (L k)
  let β := RigidifiedLineBundle.squareIso _ _ (overlapSection_fst f ε section_eq T 𝒰 i j) _ _
      (overlapSection_fst f ε section_eq T 𝒰 i k) _ _ (tripleSection_fst f ε section_eq T 𝒰 i j k) _ _
      (tripleSection_snd f ε section_eq T 𝒰 i j k) pullback.condition pullback.condition (L i) ≪≫
    (RigidifiedLineBundle.pullback _ _ (tripleSection_snd f ε section_eq T 𝒰 i j k)).mapIso
      (overlapRigidIso f ε section_eq T 𝒰 i k (Φ i k))
  have hαβ : α = β :=
    (rigidifiedIso_subsingleton_of_iso f ε section_eq unique _ (tripleIso f T 𝒰 i j k) rfl _ _).elim α β
  have h := congrArg
    (fun e ↦ (RigidifiedLineBundle.forgetModule (tripleSection f ε section_eq T 𝒰 i j k)).map e.hom) hαβ
  simp only [α, β, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    RigidifiedLineBundle.forgetModule_map_pullback_map,
    RigidifiedLineBundle.forgetModule_map_squareIso_hom] at h
  exact h

/-- The base-section square of a cover member. -/
lemma chartComm (i : 𝒰.I₀) :
    (relativeSection f ε section_eq).app
        (Over.mk (𝒰.f i ≫ T.hom)) ≫ (relativeOpenCover f T 𝒰).f i =
      𝒰.f i ≫ (relativeSection f ε section_eq).app T :=
  ((relativeSection f ε section_eq).naturality
    (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).symm

/-- A module whose pullbacks to the induced cover are line bundles is a line bundle. -/
lemma glued_isLocallyFreeRankOne (L : ∀ i, relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace f).obj T).Modules)
    (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅
      (L i).obj.carrier) :
    IsLocallyFreeRankOne N := by
  intro x
  obtain ⟨i, y, rfl⟩ := (relativeOpenCover f T 𝒰).exists_eq x
  exact IsLocallyFreeRankOne.exists_of_pullback _ ((L i).property.of_iso (ψ i).symm) y

/-- The rigidification of a local representative, moved to the chart of a module. -/
def chartRig (i : 𝒰.I₀) (L : relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace f).obj T).Modules)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅ L.obj.carrier) :
    structureModule (Over.mk (𝒰.f i ≫ T.hom)).left ≅
      (Scheme.Modules.pullback ((relativeSection f ε
        section_eq).app (Over.mk (𝒰.f i ≫ T.hom)))).obj
          ((Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N) :=
  L.obj.rigidification ≪≫ (Scheme.Modules.pullback _).mapIso ψ.symm

/-- The chart identification as a rigidified isomorphism. -/
def chartRigIso (i : 𝒰.I₀) (L : relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace f).obj T).Modules)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅ L.obj.carrier) :
    (⟨(Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N,
        chartRig f ε section_eq T 𝒰 i L N ψ⟩ :
      RigidifiedModule ((relativeSection f ε section_eq).app
        (Over.mk (𝒰.f i ≫ T.hom)))) ≅ L.obj :=
  RigidifiedModule.isoMk ψ (by simp [chartRig])

/-- Compatible chart identifications glue the chart rigidifications to the whole base. -/
lemma exists_rigidification (L : ∀ i, relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (Θ : ∀ i j,
      (RigidifiedLineBundle.pullback (ε' := overlapSection f ε section_eq T 𝒰 i j) (pullback.fst _ _)
          (pullback.fst (𝒰.f i) (𝒰.f j)) (overlapSection_fst f ε section_eq T 𝒰 i j)).obj (L i) ≅
        (RigidifiedLineBundle.pullback (ε' := overlapSection f ε section_eq T 𝒰 i j) (pullback.snd _ _)
          (pullback.snd (𝒰.f i) (𝒰.f j)) (overlapSection_snd f ε section_eq T 𝒰 i j)).obj (L j))
    (N : ((relativeSpace f).obj T).Modules)
    (ψ : ∀ i, (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅
      (L i).obj.carrier)
    (hψ : ∀ i j,
        (Scheme.Modules.pullback (pullback.fst ((relativeOpenCover f T 𝒰).f i)
            ((relativeOpenCover f T 𝒰).f j))).map (ψ i).hom ≫
          (Θ i j).hom.hom.val =
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeOpenCover f T 𝒰).f j)
            (pullback.fst ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
            (pullback.snd ((relativeOpenCover f T 𝒰).f i) ((relativeOpenCover f T 𝒰).f j))
            ((relativeOpenCover f T 𝒰).f i) pullback.condition N).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeOpenCover f T 𝒰).f i)
            ((relativeOpenCover f T 𝒰).f j))).map (ψ j).hom) :
    ∃ ρ : structureModule T.left ≅ (Scheme.Modules.pullback
        ((relativeSection f ε section_eq).app T)).obj N,
      ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom =
        (Langlands.Scheme.Modules.chartRigidification _ N (chartComm f ε section_eq T 𝒰 i)
          (chartRig f ε section_eq T 𝒰 i (L i) N (ψ i))).hom := by
  refine (Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing
    Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing T.left 𝒰
    (structureModule T.left) _
    (fun i ↦ Langlands.Scheme.Modules.chartRigidification _ N (chartComm f ε section_eq T 𝒰 i)
      (chartRig f ε section_eq T 𝒰 i (L i) N (ψ i))) ?_).exists
  intro i j
  have hz : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j = pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i :=
    pullback.condition.symm
  have cw : overlapSection f ε section_eq T 𝒰 i j ≫ pullback.fst ((relativeOpenCover f T 𝒰).f i)
        ((relativeOpenCover f T 𝒰).f j) ≫ (relativeOpenCover f T 𝒰).f i =
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫
        (relativeSection f ε section_eq).app T := by
    rw [overlapSection_fst_assoc, chartComm, Category.assoc]
  have hi := Langlands.Scheme.Modules.chartRigidification_restrict _ N (chartComm f ε section_eq T 𝒰 i)
    (chartRig f ε section_eq T 𝒰 i (L i) N (ψ i)) (pullback.fst _ _) (pullback.fst (𝒰.f i) (𝒰.f j))
    (overlapSection_fst f ε section_eq T 𝒰 i j) _ rfl _ rfl cw
  have hj := Langlands.Scheme.Modules.chartRigidification_restrict _ N (chartComm f ε section_eq T 𝒰 j)
    (chartRig f ε section_eq T 𝒰 j (L j) N (ψ j)) (pullback.snd _ _) (pullback.snd (𝒰.f i) (𝒰.f j))
    (overlapSection_snd f ε section_eq T 𝒰 i j) _ hz _ pullback.condition.symm cw
  let Θ' := (RigidifiedModule.pullback (pullback.fst _ _) (pullback.fst (𝒰.f i) (𝒰.f j))
      (overlapSection_fst f ε section_eq T 𝒰 i j)).map (chartRigIso f ε section_eq T 𝒰 i (L i) N (ψ i)).hom ≫
    (Θ i j).hom.hom ≫
      (RigidifiedModule.pullback (pullback.snd _ _) (pullback.snd (𝒰.f i) (𝒰.f j))
        (overlapSection_snd f ε section_eq T 𝒰 i j)).map (chartRigIso f ε section_eq T 𝒰 j (L j) N (ψ j)).inv
  have hΘ' : Θ'.val = (Langlands.Scheme.Modules.squarePullbackIso
      ((relativeOpenCover f T 𝒰).f j) (pullback.fst _ _) (pullback.snd _ _)
      ((relativeOpenCover f T 𝒰).f i) pullback.condition N).hom := by
    change (Scheme.Modules.pullback (pullback.fst _ _)).map (ψ i).hom ≫
        (Θ i j).hom.hom.val ≫ (Scheme.Modules.pullback (pullback.snd _ _)).map (ψ j).inv = _
    rw [reassoc_of% (hψ i j)]
    simp
  have hr := Langlands.Scheme.Modules.restricted_rigidification_eq
    (εP := overlapSection f ε section_eq T 𝒰 i j) _ _ (pullback.fst _ _) (pullback.snd _ _)
    (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
    (overlapSection_fst f ε section_eq T 𝒰 i j) (overlapSection_snd f ε section_eq T 𝒰 i j) pullback.condition N
    (chartRig f ε section_eq T 𝒰 i (L i) N (ψ i)) (chartRig f ε section_eq T 𝒰 j (L j) N (ψ j)) Θ' hΘ' _ rfl
    pullback.condition.symm
  rw [← hr] at hj
  exact Langlands.Scheme.Modules.square_compatible_of_common_map (𝒰.f j) (pullback.fst _ _)
    (pullback.snd _ _) (𝒰.f i) pullback.condition (Iso.refl _) _ _ _ (Category.id_comp _)
    (Category.id_comp _) hz rfl _ _ _ _ _ hi hj

/-- The glued rigidified family restricts to each local representative. -/
lemma glued_restrict_iso (i : 𝒰.I₀) (L : relative f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (N : ((relativeSpace f).obj T).Modules) (hN : IsLocallyFreeRankOne N)
    (ψ : (Scheme.Modules.pullback ((relativeOpenCover f T 𝒰).f i)).obj N ≅ L.obj.carrier)
    (ρ : structureModule T.left ≅ (Scheme.Modules.pullback
      ((relativeSection f ε section_eq).app T)).obj N)
    (hρ : (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom =
      (Langlands.Scheme.Modules.chartRigidification _ N (chartComm f ε section_eq T 𝒰 i)
        (chartRig f ε section_eq T 𝒰 i L N ψ)).hom) :
    Nonempty ((RigidifiedLineBundle.relativePullback f ε
      section_eq (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj
        (⟨⟨N, ρ⟩, hN⟩ : relative f ε section_eq T) ≅ L) := by
  refine ⟨RigidifiedLineBundle.isoMk ψ ?_⟩
  change ((Langlands.Scheme.Modules.pullbackUnitIso (𝒰.f i)).inv ≫
      (Scheme.Modules.pullback (𝒰.f i)).map ρ.hom ≫
        (RigidifiedModule.squarePullbackIso ((relativeOpenCover f T 𝒰).f i) (𝒰.f i)
          (chartComm f ε section_eq T 𝒰 i)).hom.app N) ≫
      (Scheme.Modules.pullback _).map ψ.hom = L.obj.rigidification.hom
  rw [hρ]
  simp [Langlands.Scheme.Modules.chartRigidification, chartRig]

end Gluing

/-- Compatible actual relative rigidified classes glue under uniqueness of isomorphisms. -/
theorem classes_zariskiGluing_of_unique_of_moduleGluing
    (glue : Langlands.Scheme.Modules.OpenCoverModuleGluingStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (q : ∀ i, Classes f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (hq : ∀ i j,
      classesPullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom)) (q i) =
      classesPullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
            (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom)) (q j)) :
    ∃ q₀ : Classes f ε section_eq T, ∀ i,
      classesPullback f ε section_eq
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q₀ = q i := by
  classical
  have hΦ : ∀ i j, Nonempty
      ((RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom))).obj (q i).out ≅
      (RigidifiedLineBundle.relativePullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j)) (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom))).obj (q j).out) := by
    intro i j
    have h := hq i j
    rw [← Quotient.out_eq (q i), ← Quotient.out_eq (q j)] at h
    exact Quotient.exact h
  let Φ := fun i j ↦ Classical.choice (hΦ i j)
  obtain ⟨N, ψ, hψ⟩ := exists_glued f ε section_eq T 𝒰 unique glue (fun i ↦ (q i).out) Φ
  have hN := glued_isLocallyFreeRankOne f ε section_eq T 𝒰 (fun i ↦ (q i).out) N ψ
  obtain ⟨ρ, hρ⟩ := exists_rigidification f ε section_eq T 𝒰 (fun i ↦ (q i).out)
    (fun i j ↦ overlapRigidIso f ε section_eq T 𝒰 i j (Φ i j)) N ψ hψ
  refine ⟨Quotient.mk _ (⟨⟨N, ρ⟩, hN⟩ : relative f ε section_eq T), fun i ↦ ?_⟩
  exact (Quotient.sound (glued_restrict_iso f ε section_eq T 𝒰 i (q i).out N hN (ψ i) ρ (hρ i))).trans
    (Quotient.out_eq (q i))

/-- Zariski gluing for general relative rigidified classes with unique isomorphisms. -/
theorem classes_zariskiGluing_of_unique
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (q : ∀ i, Classes f ε section_eq (Over.mk (𝒰.f i ≫ T.hom)))
    (hq : ∀ i j,
      classesPullback f ε section_eq
        (Over.homMk (pullback.fst (𝒰.f i) (𝒰.f j)) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f i ≫ T.hom)) (q i) =
      classesPullback f ε section_eq
        (Over.homMk (pullback.snd (𝒰.f i) (𝒰.f j))
            (by simp [pullback.condition_assoc]) :
          Over.mk (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom) ⟶
            Over.mk (𝒰.f j ≫ T.hom)) (q j)) :
    ∃ q₀ : Classes f ε section_eq T, ∀ i,
      classesPullback f ε section_eq
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q₀ = q i :=
  classes_zariskiGluing_of_unique_of_moduleGluing f ε section_eq
    Langlands.Scheme.Modules.openCoverModuleGluing unique T 𝒰 q hq

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
