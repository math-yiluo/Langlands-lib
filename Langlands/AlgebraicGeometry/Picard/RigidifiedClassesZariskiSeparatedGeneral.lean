import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiGluingProof

/-! # Zariski separation of rigidified classes for general relative schemes -/

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

/-- The relative-space map of a cover member is the member of the standard total-space cover. -/
lemma relativeSpace_openCover_map  (T : Over S)
    (𝒰 : T.left.OpenCover.{u}) (i : 𝒰.I₀) :
    (relativeSpace f).map
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) =
      (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).f i := by
  apply pullback.hom_ext
  · simp [relativeSpace, Scheme.Pullback.openCoverOfLeft, pullback.map]
  · simp [relativeSpace, Scheme.Pullback.openCoverOfLeft, pullback.map]


/-- Uniqueness identifies local isomorphisms after comparison with a common base pullback. -/
lemma rigidified_common_map (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
     {T U V W : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (a : W ⟶ U) (b : W ⟶ V) (z : W ⟶ T)
    (ha : a ≫ h = z) (hb : b ≫ k = z) (L M : relative f ε section_eq T)
    (ei : (RigidifiedLineBundle.relativePullback f ε
      section_eq h).obj L ≅
        (RigidifiedLineBundle.relativePullback f ε
          section_eq h).obj M)
    (ej : (RigidifiedLineBundle.relativePullback f ε
      section_eq k).obj L ≅
        (RigidifiedLineBundle.relativePullback f ε
          section_eq k).obj M) :
    ∃ r : (Scheme.Modules.pullback ((relativeSpace f).map z)).obj L.obj.carrier ⟶
        (Scheme.Modules.pullback ((relativeSpace f).map z)).obj M.obj.carrier,
      (Scheme.Modules.pullback ((relativeSpace f).map a)).map ei.hom.hom.val ≫
          compHom ((relativeSpace f).map a) ((relativeSpace f).map h)
            ((relativeSpace f).map z)
            (((relativeSpace f).map_comp a h).symm.trans
              (congrArg (relativeSpace f).map ha)) M.obj.carrier =
        compHom ((relativeSpace f).map a) ((relativeSpace f).map h)
          ((relativeSpace f).map z)
          (((relativeSpace f).map_comp a h).symm.trans
            (congrArg (relativeSpace f).map ha)) L.obj.carrier ≫ r ∧
      (Scheme.Modules.pullback ((relativeSpace f).map b)).map ej.hom.hom.val ≫
          compHom ((relativeSpace f).map b) ((relativeSpace f).map k)
            ((relativeSpace f).map z)
            (((relativeSpace f).map_comp b k).symm.trans
              (congrArg (relativeSpace f).map hb)) M.obj.carrier =
        compHom ((relativeSpace f).map b) ((relativeSpace f).map k)
          ((relativeSpace f).map z)
          (((relativeSpace f).map_comp b k).symm.trans
            (congrArg (relativeSpace f).map hb)) L.obj.carrier ≫ r := by
  let Ci := relativePullbackCompTo f ε section_eq h a z ha
  let Cj := relativePullbackCompTo f ε section_eq k b z hb
  let ri := (Ci.app L).symm ≪≫
    (RigidifiedLineBundle.relativePullback f ε
      section_eq a).mapIso ei ≪≫ Ci.app M
  let rj := (Cj.app L).symm ≪≫
    (RigidifiedLineBundle.relativePullback f ε
      section_eq b).mapIso ej ≪≫ Cj.app M
  have he : ri = rj := (unique W _ _).elim ri rj
  have hi : (RigidifiedLineBundle.relativePullback f ε
      section_eq a).map ei.hom ≫ Ci.hom.app M = Ci.hom.app L ≫ ri.hom := by
    simp [ri]
  have hj : (RigidifiedLineBundle.relativePullback f ε
      section_eq b).map ej.hom ≫ Cj.hom.app M = Cj.hom.app L ≫ ri.hom := by
    rw [he]
    simp [rj]
  refine ⟨ri.hom.hom.val, ?_, ?_⟩
  · have hh := congrArg (fun v ↦ v.hom.val) hi
    change (Scheme.Modules.pullback ((relativeSpace f).map a)).map ei.hom.hom.val ≫
      (Ci.hom.app M).hom.val = (Ci.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Ci, relativePullbackCompTo_hom_val] using hh
  · have hh := congrArg (fun v ↦ v.hom.val) hj
    change (Scheme.Modules.pullback ((relativeSpace f).map b)).map ej.hom.hom.val ≫
      (Cj.hom.app M).hom.val = (Cj.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Cj, relativePullbackCompTo_hom_val] using hh

/-- Actual local rigidified isomorphisms agree on the actual total-space overlap. -/
lemma rigidified_overlap_compatible (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
     {T U V : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (L M : relative f ε section_eq T)
    (ei : (RigidifiedLineBundle.relativePullback f ε
      section_eq h).obj L ≅
        (RigidifiedLineBundle.relativePullback f ε
          section_eq h).obj M)
    (ej : (RigidifiedLineBundle.relativePullback f ε
      section_eq k).obj L ≅
        (RigidifiedLineBundle.relativePullback f ε
          section_eq k).obj M) :
    (Scheme.Modules.pullback (pullback.fst ((relativeSpace f).map h)
      ((relativeSpace f).map k))).map ei.hom.hom.val ≫
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace f).map k)
          (pullback.fst ((relativeSpace f).map h) ((relativeSpace f).map k))
          (pullback.snd ((relativeSpace f).map h) ((relativeSpace f).map k))
          ((relativeSpace f).map h) pullback.condition M.obj.carrier).hom =
      (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace f).map k)
        (pullback.fst ((relativeSpace f).map h) ((relativeSpace f).map k))
        (pullback.snd ((relativeSpace f).map h) ((relativeSpace f).map k))
        ((relativeSpace f).map h) pullback.condition L.obj.carrier).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeSpace f).map h)
            ((relativeSpace f).map k))).map ej.hom.hom.val := by
  obtain ⟨r, hi, hj⟩ := rigidified_common_map f ε section_eq unique h k (pullback.fst h k)
    (pullback.snd h k) (pullback.fst h k ≫ h) rfl pullback.condition.symm L M ei ej
  exact Langlands.Scheme.Modules.square_compatible_of_common_map _ _ _ _ pullback.condition
    (PreservesPullback.iso (relativeSpace f) h k) _ _ _
    (PreservesPullback.iso_hom_fst _ _ _) (PreservesPullback.iso_hom_snd _ _ _)
    _ _ L.obj.carrier M.obj.carrier ei.hom.hom.val ej.hom.hom.val r hi hj


/-- The base-changed open cover, with its maps expressed by the actual relative functor. -/
def relativeOpenCover  (T : Over S)
    (𝒰 : T.left.OpenCover.{u}) : ((relativeSpace f).obj T).OpenCover.{u} :=
  (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).copy 𝒰.I₀
    (fun i ↦ (relativeSpace f).obj (Over.mk (𝒰.f i ≫ T.hom)))
    (fun i ↦ (relativeSpace f).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))
    (Equiv.refl _) (fun _ ↦ Iso.refl _)
    (fun i ↦ by
      change (relativeSpace f).map
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) =
        (𝟙 _) ≫ (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom f).f i
      simpa only [Category.id_comp] using relativeSpace_openCover_map f T 𝒰 i)

/-- Compatible local rigidified isomorphisms glue, with global rigidification checked on the base. -/
lemma rigidified_iso_of_local_isos (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (glue : Langlands.Scheme.Modules.OpenCoverHomGluingStatement.{u})
     (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (L M : relative f ε section_eq T)
    (ei : ∀ i, (RigidifiedLineBundle.relativePullback f ε
      section_eq
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
        (RigidifiedLineBundle.relativePullback f ε
          section_eq
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :
    Nonempty (L ≅ M) := by
  let 𝒱 := relativeOpenCover f T 𝒰
  let e' : ∀ i, (Scheme.Modules.pullback (𝒱.f i)).obj L.obj.carrier ≅
      (Scheme.Modules.pullback (𝒱.f i)).obj M.obj.carrier := fun i ↦
    (RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso (ei i)
  obtain ⟨e, he, _⟩ := Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing glue _ 𝒱
    L.obj.carrier M.obj.carrier e' (fun i j ↦
      rigidified_overlap_compatible f ε section_eq unique _ _ L M (ei i) (ei j))
  refine ⟨RigidifiedLineBundle.isoMk e ?_⟩
  apply Langlands.Scheme.Modules.hom_ext_of_openCover glue 𝒰
  intro i
  apply RigidifiedModule.rigidification_compatibility_of_pullback
    ((relativeSpace f).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)) (𝒰.f i)
    ((relativeSection f ε section_eq).naturality
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).symm L.obj M.obj e.hom
  have hei : (Scheme.Modules.pullback ((relativeSpace f).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))).map e.hom =
        (ei i).hom.hom.val := he i
  rw [hei]
  exact (ei i).hom.hom.property


/-- Rigidified classes are determined Zariski-locally whenever relative rigidified
isomorphisms are unique. -/
lemma classes_zariskiSeparated_of_unique
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    (T : Over S) (𝒰 : T.left.OpenCover.{u}) (q r : Classes f ε section_eq T)
    (h : ∀ i,
      classesPullback f ε section_eq
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) q =
      classesPullback f ε section_eq
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) r) :
    q = r := by
  classical
  induction q using Quotient.inductionOn with
  | h L =>
    induction r using Quotient.inductionOn with
    | h M =>
      apply Quotient.sound
      have hi : ∀ i, Nonempty (
          (relativePullback f ε section_eq
            (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
          (relativePullback f ε section_eq
            (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :=
        fun i ↦ Quotient.exact (h i)
      exact rigidified_iso_of_local_isos f ε section_eq unique
        Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing T 𝒰 L M
        (fun i ↦ Classical.choice (hi i))

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
