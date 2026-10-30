import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Zariski separatedness of actual rigidified abelian-scheme classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Scheme.Modules

/-- The actual square comparisons form a natural isomorphism. -/
lemma squarePullbackIso_naturality {X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) {M N : Y.Modules} (f : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pullback p').map
        ((AlgebraicGeometry.Scheme.Modules.pullback t).map f) ≫
      (squarePullbackIso p p' s t hs N).hom =
    (squarePullbackIso p p' s t hs M).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullback s).map
        ((AlgebraicGeometry.Scheme.Modules.pullback p).map f) := by
  exact ((AlgebraicGeometry.Scheme.Modules.pullbackComp p' t ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackCongr hs ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp s p).symm).hom.naturality f)

/-- The unique-gluing input detects equality of module maps on a cover. -/
lemma hom_ext_of_openCover (glue : OpenCoverHomGluingStatement.{u})
    {X : AlgebraicGeometry.Scheme.{u}} (𝒰 : X.OpenCover.{u})
    {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map f =
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map g) : f = g := by
  obtain ⟨k, _, hk⟩ := glue X 𝒰 M N
    (fun i ↦ (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map f)
    (fun i j ↦ squarePullbackIso_naturality _ _ _ _ pullback.condition f)
  exact (hk f (fun _ ↦ rfl)).trans (hk g (fun i ↦ (h i).symm)).symm

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- The relative-space map of a cover member is the member of the standard total-space cover. -/
lemma relativeSpace_openCover_map (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
    (𝒰 : T.left.OpenCover.{u}) (i : 𝒰.I₀) :
    (relativeSpace A.X.hom).map
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) =
      (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom A.X.hom).f i := by
  apply pullback.hom_ext
  · simp [relativeSpace, Scheme.Pullback.openCoverOfLeft, pullback.map]
  · simp [relativeSpace, Scheme.Pullback.openCoverOfLeft, pullback.map]

end Langlands.AbelianScheme

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule.RigidifiedModule

/-- Square comparisons commute with comparison to any chosen equal composite. -/
lemma squarePullbackIso_comp_to {V X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (M : Y.Modules) (a : V ⟶ X')
    (ap' : V ⟶ Y') (as' : V ⟶ X) (z : V ⟶ Y)
    (hap' : a ≫ p' = ap') (has' : a ≫ s = as')
    (hz : as' ≫ p = z) (hz' : ap' ≫ t = z) :
    (AlgebraicGeometry.Scheme.Modules.pullback a).map
        (squarePullbackIso p p' s t hs M).hom ≫
      compHom a s as' has' ((AlgebraicGeometry.Scheme.Modules.pullback p).obj M) ≫
        compHom as' p z hz M =
      compHom a p' ap' hap' ((AlgebraicGeometry.Scheme.Modules.pullback t).obj M) ≫
        compHom ap' t z hz' M := by
  subst ap' as'
  simpa only [compHom_rfl] using squarePullbackIso_comp p p' s t hs M a z hz hz'

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

variable {S X : Scheme.{u}}

/-- Comparison of iterated relative pullback with pullback along a chosen equal composite. -/
def relativePullbackCompTo (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)
    {T U V : Over S} (h : U ⟶ T) (g : V ⟶ U) (k : V ⟶ T) (hg : g ≫ h = k) :
    RigidifiedLineBundle.relativePullback f ε hε h ⋙
        RigidifiedLineBundle.relativePullback f ε hε g ≅
      RigidifiedLineBundle.relativePullback f ε hε k :=
  by
    subst k
    exact RigidifiedLineBundle.relativePullbackComp
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence f ε hε g h

/-- The comparison for equal rigidified pullback maps has the usual underlying map. -/
lemma pullbackCongr_hom_val {S X S' X' : Scheme.{u}}
    {ε : S ⟶ X} {ε' : S' ⟶ X'} {f₁ f₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (c₁ : ε' ≫ f₁ = g₁ ≫ ε) (c₂ : ε' ≫ f₂ = g₂ ≫ ε)
    (L : RigidifiedLineBundle ε) :
    ((RigidifiedLineBundle.pullbackCongr hf hg c₁ c₂).hom.app L).hom.val =
      (Scheme.Modules.pullbackCongr hf).hom.app L.obj.carrier := by
  subst f₂ g₂
  rfl

/-- The chosen relative comparison has the equal-composite module comparison underneath. -/
lemma relativePullbackCompTo_hom_val (f : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)
    {T U V : Over S} (h : U ⟶ T) (g : V ⟶ U) (k : V ⟶ T) (hg : g ≫ h = k)
    (L : RigidifiedLineBundle.relative f ε hε T) :
    ((relativePullbackCompTo f ε hε h g k hg).hom.app L).hom.val =
      Langlands.SchemeModule.RigidifiedModule.compHom
        ((relativeSpace f).map g) ((relativeSpace f).map h) ((relativeSpace f).map k)
        (((relativeSpace f).map_comp g h).symm.trans
          (congrArg (relativeSpace f).map hg)) L.obj.carrier := by
  subst k
  change _ ≫ ((RigidifiedLineBundle.pullbackCongr _ _ _ _).hom.app L).hom.val = _
  rw [pullbackCongr_hom_val]
  rfl

end Langlands.AlgebraicGeometry.Picard


namespace Langlands.AlgebraicGeometry.Picard

/-- The relative total-space functor preserves pullbacks. -/
instance relativeSpace_preservesPullbacks {S X : Scheme.{u}} (f : X ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (relativeSpace f) := by
  dsimp only [relativeSpace]
  infer_instance

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.Scheme.Modules

/-- Pullback along an isomorphism detects equality of actual module maps. -/
lemma pullback_map_injective_of_iso {X Y : AlgebraicGeometry.Scheme.{u}}
    (e : X ≅ Y) {M N : Y.Modules} {f g : M ⟶ N}
    (h : (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map f =
      (AlgebraicGeometry.Scheme.Modules.pullback e.hom).map g) : f = g := by
  let η := AlgebraicGeometry.Scheme.Modules.pullbackComp e.inv e.hom ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackId Y
  apply (cancel_epi (η.hom.app M)).mp
  calc η.hom.app M ≫ f =
        (AlgebraicGeometry.Scheme.Modules.pullback e.inv).map
          ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).map f) ≫ η.hom.app N :=
        (η.hom.naturality f).symm
    _ = (AlgebraicGeometry.Scheme.Modules.pullback e.inv).map
          ((AlgebraicGeometry.Scheme.Modules.pullback e.hom).map g) ≫ η.hom.app N := by rw [h]
    _ = η.hom.app M ≫ g := η.hom.naturality g

end Langlands.Scheme.Modules


namespace Langlands.Scheme.Modules

open Langlands.SchemeModule.RigidifiedModule

/-- A common map on the relative overlap gives actual Čech compatibility. -/
lemma square_compatible_of_common_map {V X Y X' Y' : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (hs : p' ≫ t = s ≫ p) (q : V ≅ X')
    (a : V ⟶ Y') (b : V ⟶ X) (z : V ⟶ Y)
    (ha : q.hom ≫ p' = a) (hb : q.hom ≫ s = b)
    (hz : b ≫ p = z) (hz' : a ≫ t = z)
    (M N : Y.Modules)
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback t).obj M ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback t).obj N)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback p).obj M ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback p).obj N)
    (r : (AlgebraicGeometry.Scheme.Modules.pullback z).obj M ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback z).obj N)
    (hi : (AlgebraicGeometry.Scheme.Modules.pullback a).map ei ≫ compHom a t z hz' N =
      compHom a t z hz' M ≫ r)
    (hj : (AlgebraicGeometry.Scheme.Modules.pullback b).map ej ≫ compHom b p z hz N =
      compHom b p z hz M ≫ r) :
    (AlgebraicGeometry.Scheme.Modules.pullback p').map ei ≫
        (squarePullbackIso p p' s t hs N).hom =
      (squarePullbackIso p p' s t hs M).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullback s).map ej := by
  apply pullback_map_injective_of_iso q
  simp only [Functor.map_comp]
  apply (cancel_mono (compHom q.hom s b hb
      ((AlgebraicGeometry.Scheme.Modules.pullback p).obj N) ≫ compHom b p z hz N)).mp
  have eM := squarePullbackIso_comp_to p p' s t hs N q.hom a b z ha hb hz hz'
  have eL := squarePullbackIso_comp_to p p' s t hs M q.hom a b z ha hb hz hz'
  have ni := (compHom_naturality q.hom p' a ha ei).symm
  have nj := (compHom_naturality q.hom s b hb ej).symm
  simp only [Category.assoc] at eM eL ⊢
  rw [eM, reassoc_of% ni, hi, ← reassoc_of% eL, ← hj, ← reassoc_of% nj]

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule

/-- Uniqueness identifies local isomorphisms after comparison with a common base pullback. -/
lemma rigidified_common_map (unique : RigidifiedIsoUniquenessStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) {T U V W : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (a : W ⟶ U) (b : W ⟶ V) (z : W ⟶ T)
    (ha : a ≫ h = z) (hb : b ≫ k = z) (L M : RigidifiedFamily A T)
    (ei : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) h).obj L ≅
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) h).obj M)
    (ej : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) k).obj L ≅
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) k).obj M) :
    ∃ r : (Scheme.Modules.pullback ((relativeSpace A.X.hom).map z)).obj L.obj.carrier ⟶
        (Scheme.Modules.pullback ((relativeSpace A.X.hom).map z)).obj M.obj.carrier,
      (Scheme.Modules.pullback ((relativeSpace A.X.hom).map a)).map ei.hom.hom.val ≫
          compHom ((relativeSpace A.X.hom).map a) ((relativeSpace A.X.hom).map h)
            ((relativeSpace A.X.hom).map z)
            (((relativeSpace A.X.hom).map_comp a h).symm.trans
              (congrArg (relativeSpace A.X.hom).map ha)) M.obj.carrier =
        compHom ((relativeSpace A.X.hom).map a) ((relativeSpace A.X.hom).map h)
          ((relativeSpace A.X.hom).map z)
          (((relativeSpace A.X.hom).map_comp a h).symm.trans
            (congrArg (relativeSpace A.X.hom).map ha)) L.obj.carrier ≫ r ∧
      (Scheme.Modules.pullback ((relativeSpace A.X.hom).map b)).map ej.hom.hom.val ≫
          compHom ((relativeSpace A.X.hom).map b) ((relativeSpace A.X.hom).map k)
            ((relativeSpace A.X.hom).map z)
            (((relativeSpace A.X.hom).map_comp b k).symm.trans
              (congrArg (relativeSpace A.X.hom).map hb)) M.obj.carrier =
        compHom ((relativeSpace A.X.hom).map b) ((relativeSpace A.X.hom).map k)
          ((relativeSpace A.X.hom).map z)
          (((relativeSpace A.X.hom).map_comp b k).symm.trans
            (congrArg (relativeSpace A.X.hom).map hb)) L.obj.carrier ≫ r := by
  let Ci := relativePullbackCompTo A.X.hom (unitSection A) (unitSection_comp A) h a z ha
  let Cj := relativePullbackCompTo A.X.hom (unitSection A) (unitSection_comp A) k b z hb
  let ri := (Ci.app L).symm ≪≫
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) a).mapIso ei ≪≫ Ci.app M
  let rj := (Cj.app L).symm ≪≫
    (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) b).mapIso ej ≪≫ Cj.app M
  have he : ri = rj := (unique S A W _ _).elim ri rj
  have hi : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) a).map ei.hom ≫ Ci.hom.app M = Ci.hom.app L ≫ ri.hom := by
    simp [ri]
  have hj : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) b).map ej.hom ≫ Cj.hom.app M = Cj.hom.app L ≫ ri.hom := by
    rw [he]
    simp [rj]
  refine ⟨ri.hom.hom.val, ?_, ?_⟩
  · have hh := congrArg (fun v ↦ v.hom.val) hi
    change (Scheme.Modules.pullback ((relativeSpace A.X.hom).map a)).map ei.hom.hom.val ≫
      (Ci.hom.app M).hom.val = (Ci.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Ci, relativePullbackCompTo_hom_val] using hh
  · have hh := congrArg (fun v ↦ v.hom.val) hj
    change (Scheme.Modules.pullback ((relativeSpace A.X.hom).map b)).map ej.hom.hom.val ≫
      (Cj.hom.app M).hom.val = (Cj.hom.app L).hom.val ≫ ri.hom.hom.val at hh
    simpa only [Cj, relativePullbackCompTo_hom_val] using hh

/-- Actual local rigidified isomorphisms agree on the actual total-space overlap. -/
lemma rigidified_overlap_compatible (unique : RigidifiedIsoUniquenessStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) {T U V : Over S}
    (h : U ⟶ T) (k : V ⟶ T) (L M : RigidifiedFamily A T)
    (ei : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) h).obj L ≅
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) h).obj M)
    (ej : (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A) k).obj L ≅
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A) k).obj M) :
    (Scheme.Modules.pullback (pullback.fst ((relativeSpace A.X.hom).map h)
      ((relativeSpace A.X.hom).map k))).map ei.hom.hom.val ≫
        (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace A.X.hom).map k)
          (pullback.fst ((relativeSpace A.X.hom).map h) ((relativeSpace A.X.hom).map k))
          (pullback.snd ((relativeSpace A.X.hom).map h) ((relativeSpace A.X.hom).map k))
          ((relativeSpace A.X.hom).map h) pullback.condition M.obj.carrier).hom =
      (Langlands.Scheme.Modules.squarePullbackIso ((relativeSpace A.X.hom).map k)
        (pullback.fst ((relativeSpace A.X.hom).map h) ((relativeSpace A.X.hom).map k))
        (pullback.snd ((relativeSpace A.X.hom).map h) ((relativeSpace A.X.hom).map k))
        ((relativeSpace A.X.hom).map h) pullback.condition L.obj.carrier).hom ≫
          (Scheme.Modules.pullback (pullback.snd ((relativeSpace A.X.hom).map h)
            ((relativeSpace A.X.hom).map k))).map ej.hom.hom.val := by
  obtain ⟨r, hi, hj⟩ := rigidified_common_map unique A h k (pullback.fst h k)
    (pullback.snd h k) (pullback.fst h k ≫ h) rfl pullback.condition.symm L M ei ej
  exact Langlands.Scheme.Modules.square_compatible_of_common_map _ _ _ _ pullback.condition
    (PreservesPullback.iso (relativeSpace A.X.hom) h k) _ _ _
    (PreservesPullback.iso_hom_fst _ _ _) (PreservesPullback.iso_hom_snd _ _ _)
    _ _ L.obj.carrier M.obj.carrier ei.hom.hom.val ej.hom.hom.val r hi hj

end Langlands.AbelianScheme

namespace Langlands.SchemeModule.RigidifiedModule

/-- Compatibility of a pulled-back map implies the pulled-back original compatibility equation. -/
lemma rigidification_compatibility_of_pullback {S X S' X' : Scheme.{u}}
    {ε : S ⟶ X} {ε' : S' ⟶ X'} (f : X' ⟶ X) (g : S' ⟶ S)
    (comm : ε' ≫ f = g ≫ ε) (M N : RigidifiedModule ε) (φ : M.carrier ⟶ N.carrier)
    (h : ((pullback f g comm).obj M).rigidification.hom ≫
        (Scheme.Modules.pullback ε').map ((Scheme.Modules.pullback f).map φ) =
      ((pullback f g comm).obj N).rigidification.hom) :
    (Scheme.Modules.pullback g).map (M.rigidification.hom ≫
        (Scheme.Modules.pullback ε).map φ) =
      (Scheme.Modules.pullback g).map N.rigidification.hom := by
  have hn := (squarePullbackIso f g comm).hom.naturality φ
  simp only [Functor.comp_map] at hn
  change ((Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map M.rigidification.hom ≫
        (squarePullbackIso f g comm).hom.app M.carrier) ≫
          (Scheme.Modules.pullback ε').map ((Scheme.Modules.pullback f).map φ) =
    (Langlands.Scheme.Modules.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map N.rigidification.hom ≫
        (squarePullbackIso f g comm).hom.app N.carrier at h
  simp only [Category.assoc] at h
  rw [← hn] at h
  rw [Functor.map_comp]
  apply (cancel_epi (Langlands.Scheme.Modules.pullbackUnitIso g).inv).mp
  apply (cancel_mono ((squarePullbackIso f g comm).hom.app N.carrier)).mp
  simpa only [Category.assoc] using h

end Langlands.SchemeModule.RigidifiedModule

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

/-- The base-changed open cover, with its maps expressed by the actual relative functor. -/
def relativeOpenCover (S : Scheme.{u}) (A : AbelianScheme S) (T : Over S)
    (𝒰 : T.left.OpenCover.{u}) : ((relativeSpace A.X.hom).obj T).OpenCover.{u} :=
  (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom A.X.hom).copy 𝒰.I₀
    (fun i ↦ (relativeSpace A.X.hom).obj (Over.mk (𝒰.f i ≫ T.hom)))
    (fun i ↦ (relativeSpace A.X.hom).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))
    (Equiv.refl _) (fun _ ↦ Iso.refl _)
    (fun i ↦ by
      change (relativeSpace A.X.hom).map
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) =
        (𝟙 _) ≫ (Scheme.Pullback.openCoverOfLeft 𝒰 T.hom A.X.hom).f i
      simpa only [Category.id_comp] using relativeSpace_openCover_map S A T 𝒰 i)

/-- Compatible local rigidified isomorphisms glue, with global rigidification checked on the base. -/
lemma rigidified_iso_of_local_isos (unique : RigidifiedIsoUniquenessStatement.{u})
    (glue : Langlands.Scheme.Modules.OpenCoverHomGluingStatement.{u})
    {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (𝒰 : T.left.OpenCover.{u})
    (L M : RigidifiedFamily A T)
    (ei : ∀ i, (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
      (unitSection_comp A)
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
        (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
          (unitSection_comp A)
          (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :
    Nonempty (L ≅ M) := by
  let 𝒱 := relativeOpenCover S A T 𝒰
  let e' : ∀ i, (Scheme.Modules.pullback (𝒱.f i)).obj L.obj.carrier ≅
      (Scheme.Modules.pullback (𝒱.f i)).obj M.obj.carrier := fun i ↦
    (RigidifiedLineBundle.forgetToRigidified _ ⋙ RigidifiedModule.forget _).mapIso (ei i)
  obtain ⟨e, he, _⟩ := Langlands.Scheme.Modules.openCoverIsoGluing_of_homGluing glue _ 𝒱
    L.obj.carrier M.obj.carrier e' (fun i j ↦
      rigidified_overlap_compatible unique A _ _ L M (ei i) (ei j))
  refine ⟨RigidifiedLineBundle.isoMk e ?_⟩
  apply Langlands.Scheme.Modules.hom_ext_of_openCover glue 𝒰
  intro i
  apply RigidifiedModule.rigidification_compatibility_of_pullback
    ((relativeSpace A.X.hom).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)) (𝒰.f i)
    ((relativeSection A.X.hom (unitSection A) (unitSection_comp A)).naturality
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).symm L.obj M.obj e.hom
  have hei : (Scheme.Modules.pullback ((relativeSpace A.X.hom).map
      (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))).map e.hom =
        (ei i).hom.hom.val := he i
  rw [hei]
  exact (ei i).hom.hom.property

/-- Actual rigidified isomorphism classes on an abelian scheme are determined
Zariski-locally on every test scheme. -/
theorem rigidifiedClassesZariskiSeparated :
    RigidifiedClassesZariskiSeparatedStatement.{u} := by
  classical
  intro S A T 𝒰 q r
  refine Quotient.inductionOn₂ q r ?_
  intro L M h
  apply Quotient.sound
  have hi : ∀ i, Nonempty (
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj L ≅
      (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A)
        (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ T.hom) ⟶ T)).obj M) :=
    fun i ↦ Quotient.exact (h i)
  let ei := fun i ↦ Classical.choice (hi i)
  exact rigidified_iso_of_local_isos rigidifiedIsoUniqueness
    Langlands.Scheme.Modules.OpenCoverHomGluing.openCoverHomGluing A T 𝒰 L M ei

end Langlands.AbelianScheme
