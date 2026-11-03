import Langlands.GroupScheme.Descent.AffineDatumSections
import Mathlib.Algebra.Group.TransferInstance

/-! # Group structure on an actual affine descent solution -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

namespace Langlands.GroupScheme.Descent
namespace AffineSchemeSolution

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  {D : Datum p G} (s : AffineSchemeSolution D)
  [Flat p] [Surjective p] [QuasiCompact p]

/-- The compatible-section group transferred to sections of the quotient. -/
@[instance_reducible] def sectionGroup (U : Over B) : Group (U ⟶ s.obj) :=
  (s.sectionEquiv U).group

private theorem localSection_one (U : Over B) :
    letI := s.sectionGroup U
    s.localSection (1 : U ⟶ s.obj) = 1 := by
  change ((s.sectionEquiv U) ((s.sectionEquiv U).symm 1)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem localSection_mul {U : Over B} (f g : U ⟶ s.obj) :
    letI := s.sectionGroup U
    s.localSection (f * g) = s.localSection f * s.localSection g := by
  change ((s.sectionEquiv U) ((s.sectionEquiv U).symm
    ((s.sectionEquiv U) f * (s.sectionEquiv U) g))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [Flat p] [Surjective p] [QuasiCompact p] in
@[reassoc] theorem localSection_comp {U V : Over B} (a : U ⟶ V) (f : V ⟶ s.obj) :
    s.localSection (a ≫ f) = (Over.pullback p).map a ≫ s.localSection f := by
  simp only [localSection, Functor.map_comp, Category.assoc]

private theorem section_comp_one {U V : Over B} (a : U ⟶ V) :
    letI := s.sectionGroup U
    letI := s.sectionGroup V
    a ≫ (1 : V ⟶ s.obj) = (1 : U ⟶ s.obj) := by
  apply s.localSection_injective U
  rw [s.localSection_comp, s.localSection_one, s.localSection_one]
  exact MonObj.comp_one _

private theorem section_comp_mul {U V : Over B} (a : U ⟶ V) (f g : V ⟶ s.obj) :
    letI := s.sectionGroup U
    letI := s.sectionGroup V
    a ≫ (f * g) = (a ≫ f) * (a ≫ g) := by
  apply s.localSection_injective U
  rw [s.localSection_comp, s.localSection_mul, s.localSection_mul,
    s.localSection_comp, s.localSection_comp]
  exact MonObj.comp_mul _ _ _

/-- The group-valued presheaf carried by the quotient's actual sections. -/
def sectionPresheaf : (Over B)ᵒᵖ ⥤ GrpCat.{u} where
  obj U := letI := s.sectionGroup U.unop; GrpCat.of (U.unop ⟶ s.obj)
  map {U V} a := by
    let := s.sectionGroup U.unop
    letI := s.sectionGroup V.unop
    exact GrpCat.ofHom
      { toFun := fun f => a.unop ≫ f
        map_one' := s.section_comp_one a.unop
        map_mul' := s.section_comp_mul a.unop }
  map_id U := by
    let := s.sectionGroup U.unop
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact Category.id_comp f
  map_comp {U V W} a b := by
    let := s.sectionGroup U.unop
    let := s.sectionGroup V.unop
    let := s.sectionGroup W.unop
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    change (b.unop ≫ a.unop) ≫ f = b.unop ≫ (a.unop ≫ f)
    exact Category.assoc _ _ _

/-- Its underlying presheaf is represented by the actual quotient scheme. -/
def sectionRepresentableBy : (s.sectionPresheaf ⋙ forget _).RepresentableBy s.obj where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- Reconstruct the group laws on the quotient from its represented groups of sections. -/
@[instance_reducible] def groupObj : GrpObj s.obj :=
  GrpObj.ofRepresentableBy s.obj s.sectionPresheaf s.sectionRepresentableBy

private theorem localSection_group_one (U : Over B) :
    letI := s.groupObj
    s.localSection (1 : U ⟶ s.obj) = 1 := by
  let := s.groupObj
  have h := ((yonedaGrpObjIsoOfRepresentableBy s.obj s.sectionPresheaf
    s.sectionRepresentableBy).hom.app (op U)).hom.map_one
  change (1 : U ⟶ s.obj) = _ at h
  rw [h]
  exact s.localSection_one U

private theorem localSection_group_mul {U : Over B} (f g : U ⟶ s.obj) :
    letI := s.groupObj
    s.localSection (f * g) = s.localSection f * s.localSection g := by
  let := s.groupObj
  have h := ((yonedaGrpObjIsoOfRepresentableBy s.obj s.sectionPresheaf
    s.sectionRepresentableBy).hom.app (op U)).hom.map_mul f g
  change f * g = _ at h
  rw [h]
  exact s.localSection_mul f g

/-- The quotient with its reconstructed group structure. -/
def groupScheme : GroupScheme B :=
  letI := s.groupObj
  Grp.mk s.obj

/-- The original pullback comparison preserves the reconstructed group laws. -/
theorem iso_isMonHom :
    letI := s.groupObj
    IsMonHom s.iso.hom := by
  let := s.groupObj
  constructor
  · rw [Functor.obj.η_def, Category.assoc]
    change Functor.LaxMonoidal.ε (Over.pullback p) ≫ s.localSection η[s.obj] = _
    rw [MonObj.one_eq_one, s.localSection_group_one, MonObj.comp_one,
      ← MonObj.one_eq_one]
  · rw [Functor.obj.μ_def, Category.assoc]
    change Functor.LaxMonoidal.μ (Over.pullback p) s.obj s.obj ≫ s.localSection μ[s.obj] = _
    rw [MonObj.mul_eq_mul, s.localSection_group_mul, MonObj.comp_mul]
    simp only [localSection, ← Category.assoc, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd]
    simp only [Hom.mul_def, lift_fst_comp_snd_comp]

/-- The actual group-scheme pullback isomorphism. -/
def groupIso : (baseChange p).obj s.groupScheme ≅ G := by
  letI := s.groupObj
  letI := s.iso_isMonHom
  exact Grp.mkIso' s.iso

@[simp] theorem groupIso_hom : s.groupIso.hom.hom.hom = s.iso.hom := rfl

@[simp] theorem groupIso_inv : s.groupIso.inv.hom.hom = s.iso.inv := rfl

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (q : T ⟶ U)
    {H I : GroupScheme U} (a : H ⟶ I) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst I.X.hom q =
      pullback.fst H.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Any comparison preserving the quotient projection respects the datum. -/
theorem compatible_of_proj (e : (baseChange p).obj s.groupScheme ⟶ G)
    (he : e.hom.hom.left ≫ s.proj = pullback.fst s.obj.hom p) :
    Compatible (canonicalDatum p s.groupScheme) D e := by
  let C := s.groupScheme
  let l := (baseChange (fst p)).map e ≫ D.overlap.hom
  let r := (canonicalOverlap p C).hom ≫ (baseChange (snd p)).map e
  have hb : l.hom.hom.left ≫ pullback.snd G.X.hom (snd p) =
      r.hom.hom.left ≫ pullback.snd G.X.hom (snd p) :=
    (Over.w l.hom.hom).trans (Over.w r.hom.hom).symm
  change l = r
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply s.square.hom_ext
    · simpa only [Category.assoc, pullback.condition] using
        congrArg (fun k => k ≫ snd p) hb
    · change ((baseChange (fst p)).map e).hom.hom.left ≫
          (D.overlap.hom.hom.hom.left ≫ pullback.fst G.X.hom (snd p)) ≫ s.proj =
        ((canonicalOverlap p C).hom.hom.hom.left ≫
          ((baseChange (snd p)).map e).hom.hom.left) ≫
            pullback.fst G.X.hom (snd p) ≫ s.proj
      rw [show D.overlap.hom.hom.hom.left ≫ pullback.fst G.X.hom (snd p) =
        D.target from rfl, ← s.relation]
      simp only [Category.assoc, Datum.source, map_fst_assoc, he]
      exact (canonicalOverlap_fst p C).symm
  · exact hb

/-- The pullback comparison identifies the canonical and original descent data. -/
theorem groupIso_compatible :
    Compatible (canonicalDatum p s.groupScheme) D s.groupIso.hom :=
  s.compatible_of_proj _ (by
    simpa only [s.groupIso_hom] using s.iso_hom_proj)

/-- The reconstructed group scheme solves the actual datum. -/
def solution : Solution D where
  obj := s.groupScheme
  iso := s.groupIso
  compatible := s.groupIso_compatible

end AffineSchemeSolution

namespace Datum

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  (D : Datum p G) [IsAffine B] [IsAffine S] [IsAffine G.X.left]
  [Flat p] [Surjective p]

/-- Effective descent of an actual affine group-scheme datum over affine bases. -/
def affineSolution : Solution D :=
  D.affineSchemeSolution.solution

instance affineSolution_isAffine : IsAffine D.affineSolution.obj.X.left :=
  D.affineSchemeSolution.affine

end Datum
end Langlands.GroupScheme.Descent
