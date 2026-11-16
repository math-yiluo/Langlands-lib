import Langlands.GroupScheme.Descent.DatumRelation
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Underlying scheme solutions and their quotient maps -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}

/-- A solution for the underlying scheme, with its actual quotient map. -/
structure SchemeSolution (D : Datum p G) where
  obj : Over B
  proj : G.X.left ⟶ obj.left
  square : IsPullback G.X.hom proj p obj.hom
  relation : D.source ≫ proj = D.target ≫ proj

namespace SchemeSolution

variable {D : Datum p G} (s : SchemeSolution D)

/-- The actual slice pullback identifies with the supplied underlying scheme. -/
def iso : (Over.pullback p).obj s.obj ≅ G.X :=
  Over.isoMk s.square.flip.isoPullback.symm (by simp)

@[reassoc (attr := simp)] theorem iso_hom_proj :
    s.iso.hom.left ≫ s.proj = pullback.fst s.obj.hom p := by
  exact s.square.flip.isoPullback_inv_fst

@[reassoc (attr := simp)] theorem iso_inv_fst :
    s.iso.inv.left ≫ pullback.fst s.obj.hom p = s.proj := by
  exact s.square.flip.isoPullback_hom_fst

/-- The original relation is the entire scheme-theoretic kernel pair of the quotient. -/
theorem kernelPair : IsPullback D.source D.target s.proj s.proj := by
  have hout : IsPullback (D.source ≫ G.X.hom) D.target p (s.proj ≫ s.obj.hom) := by
    have h := D.target_pullback.flip.paste_horiz (IsPullback.of_hasPullback p p)
    rw [← D.source_base, s.square.w] at h
    exact h
  exact hout.of_right s.relation s.square

instance proj_flat [Flat p] : Flat s.proj :=
  MorphismProperty.of_isPullback (P := @Flat) s.square inferInstance

instance proj_surjective [Surjective p] : Surjective s.proj :=
  MorphismProperty.of_isPullback (P := @Surjective) s.square inferInstance

instance proj_quasiCompact [QuasiCompact p] : QuasiCompact s.proj :=
  MorphismProperty.of_isPullback (P := @QuasiCompact) s.square inferInstance

instance proj_etale [Etale p] : Etale s.proj :=
  MorphismProperty.of_isPullback (P := @Etale) s.square inferInstance

/-- The kernel pair turns relation invariance into equality above equal quotient images. -/
theorem comp_eq_of_proj_eq {T Z : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) (a b : Z ⟶ G.X.left)
    (hab : a ≫ s.proj = b ≫ s.proj) : a ≫ f = b ≫ f := by
  let r := s.kernelPair.lift a b hab
  calc
    a ≫ f = r ≫ D.source ≫ f := by simp [r]
    _ = r ≫ D.target ≫ f := by rw [hf]
    _ = b ≫ f := by simp [r]

variable [Etale p] [Surjective p]

/-- Any map constant on the datum's relation factors through the actual quotient. -/
def desc {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.obj.left ⟶ T :=
  EffectiveEpi.desc s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

@[reassoc] theorem desc_fac {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) : s.proj ≫ s.desc f hf = f := by
  exact EffectiveEpi.fac s.proj f (fun a b hab => s.comp_eq_of_proj_eq f hf a b hab)

theorem desc_unique {T : Scheme.{u}} (f : G.X.left ⟶ T)
    (hf : D.source ≫ f = D.target ≫ f) (a : s.obj.left ⟶ T)
    (ha : s.proj ≫ a = f) : a = s.desc f hf := by
  apply (cancel_epi s.proj).mp
  rw [ha, s.desc_fac]

end SchemeSolution

namespace Solution

variable {D : Datum p G} (s : Solution D)

/-- The quotient map supplied by an actual group-scheme solution. -/
def schemeProj : G.X.left ⟶ s.obj.X.left :=
  s.iso.inv.hom.hom.left ≫ pullback.fst s.obj.X.hom p

/-- The quotient square of an actual solution is a pullback. -/
theorem schemeProj_square : IsPullback G.X.hom s.schemeProj p s.obj.X.hom := by
  refine (IsPullback.of_hasPullback s.obj.X.hom p).flip.of_iso'
    (((Grp.forget (Over S)) ⋙ Over.forget S).mapIso s.iso.symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change s.iso.inv.hom.hom.left ≫ pullback.snd s.obj.X.hom p =
      G.X.hom ≫ 𝟙 S
    have hw := Over.w s.iso.inv.hom.hom
    change s.iso.inv.hom.hom.left ≫ pullback.snd s.obj.X.hom p = G.X.hom at hw
    exact hw.trans (Category.comp_id _).symm
  · rfl
  · exact (Category.id_comp p).trans (Category.comp_id p).symm
  · exact (Category.id_comp s.obj.X.hom).trans (Category.comp_id s.obj.X.hom).symm

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (q : T ⟶ U)
    {H I : GroupScheme U} (a : H ⟶ I) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst I.X.hom q =
      pullback.fst H.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Compatibility makes the quotient constant on the original relation. -/
theorem schemeProj_relation : D.source ≫ s.schemeProj = D.target ≫ s.schemeProj := by
  have h := congrArg (fun a => a.hom.hom.left ≫
    pullback.fst ((baseChange p).obj s.obj).X.hom (snd p) ≫
      pullback.fst s.obj.X.hom p) (s.compatible.inv s.iso)
  simpa only [Compatible, canonicalDatum, Grp.comp_hom_hom, Over.comp_left,
    Category.assoc, canonicalOverlap_fst, map_fst_assoc,
    Datum.source, Datum.target, schemeProj] using h

/-- Forget the group laws while retaining the actual quotient square and relation. -/
def schemeSolution : SchemeSolution D where
  obj := s.obj.X
  proj := s.schemeProj
  square := s.schemeProj_square
  relation := s.schemeProj_relation

end Solution

end Langlands.GroupScheme.Descent
