import Langlands.GroupScheme.Descent.SchemeSolutionGroup
import Langlands.GroupScheme.Descent.FppfSchemeSolutionSections

/-! # Group structure on scheme solutions along fppf covers -/

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
namespace SchemeSolution

variable {B S : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  {D : Datum p G} (s : SchemeSolution D)
  [Flat p] [LocallyOfFinitePresentation p] [Surjective p]

/-- The compatible-section group transferred to sections of the quotient. -/
@[instance_reducible] def fppfSectionGroup (U : Over B) : Group (U ⟶ s.obj) :=
  (s.fppfSectionEquiv U).group

private theorem fppfLocalSection_one (U : Over B) :
    letI := s.fppfSectionGroup U
    s.localSection (1 : U ⟶ s.obj) = 1 := by
  change ((s.fppfSectionEquiv U) ((s.fppfSectionEquiv U).symm 1)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem fppfLocalSection_mul {U : Over B} (f g : U ⟶ s.obj) :
    letI := s.fppfSectionGroup U
    s.localSection (f * g) = s.localSection f * s.localSection g := by
  change ((s.fppfSectionEquiv U) ((s.fppfSectionEquiv U).symm
    ((s.fppfSectionEquiv U) f * (s.fppfSectionEquiv U) g))).val = _
  rw [Equiv.apply_symm_apply]
  rfl


private theorem fppfSection_comp_one {U V : Over B} (a : U ⟶ V) :
    letI := s.fppfSectionGroup U
    letI := s.fppfSectionGroup V
    a ≫ (1 : V ⟶ s.obj) = (1 : U ⟶ s.obj) := by
  apply s.fppfLocalSection_injective U
  rw [s.localSection_comp, s.fppfLocalSection_one, s.fppfLocalSection_one]
  exact MonObj.comp_one _

private theorem fppfSection_comp_mul {U V : Over B} (a : U ⟶ V) (f g : V ⟶ s.obj) :
    letI := s.fppfSectionGroup U
    letI := s.fppfSectionGroup V
    a ≫ (f * g) = (a ≫ f) * (a ≫ g) := by
  apply s.fppfLocalSection_injective U
  rw [s.localSection_comp, s.fppfLocalSection_mul, s.fppfLocalSection_mul,
    s.localSection_comp, s.localSection_comp]
  exact MonObj.comp_mul _ _ _

/-- The group-valued presheaf carried by the quotient's actual sections. -/
def fppfSectionPresheaf : (Over B)ᵒᵖ ⥤ GrpCat.{u} where
  obj U := letI := s.fppfSectionGroup U.unop; GrpCat.of (U.unop ⟶ s.obj)
  map {U V} a := by
    let := s.fppfSectionGroup U.unop
    letI := s.fppfSectionGroup V.unop
    exact GrpCat.ofHom
      { toFun := fun f => a.unop ≫ f
        map_one' := s.fppfSection_comp_one a.unop
        map_mul' := s.fppfSection_comp_mul a.unop }
  map_id U := by
    let := s.fppfSectionGroup U.unop
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact Category.id_comp f
  map_comp {U V W} a b := by
    let := s.fppfSectionGroup U.unop
    let := s.fppfSectionGroup V.unop
    let := s.fppfSectionGroup W.unop
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    change (b.unop ≫ a.unop) ≫ f = b.unop ≫ (a.unop ≫ f)
    exact Category.assoc _ _ _

/-- Its underlying presheaf is represented by the actual quotient scheme. -/
def fppfSectionRepresentableBy : (s.fppfSectionPresheaf ⋙ forget _).RepresentableBy s.obj where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- Reconstruct the group laws on the quotient from its represented groups of sections. -/
@[instance_reducible] def fppfGroupObj : GrpObj s.obj :=
  GrpObj.ofRepresentableBy s.obj s.fppfSectionPresheaf s.fppfSectionRepresentableBy

private theorem fppfLocalSection_group_one (U : Over B) :
    letI := s.fppfGroupObj
    s.localSection (1 : U ⟶ s.obj) = 1 := by
  let := s.fppfGroupObj
  have h := ((yonedaGrpObjIsoOfRepresentableBy s.obj s.fppfSectionPresheaf
    s.fppfSectionRepresentableBy).hom.app (op U)).hom.map_one
  change (1 : U ⟶ s.obj) = _ at h
  rw [h]
  exact s.fppfLocalSection_one U

private theorem fppfLocalSection_group_mul {U : Over B} (f g : U ⟶ s.obj) :
    letI := s.fppfGroupObj
    s.localSection (f * g) = s.localSection f * s.localSection g := by
  let := s.fppfGroupObj
  have h := ((yonedaGrpObjIsoOfRepresentableBy s.obj s.fppfSectionPresheaf
    s.fppfSectionRepresentableBy).hom.app (op U)).hom.map_mul f g
  change f * g = _ at h
  rw [h]
  exact s.fppfLocalSection_mul f g

/-- The quotient with its reconstructed group structure. -/
def fppfGroupScheme : GroupScheme B :=
  letI := s.fppfGroupObj
  Grp.mk s.obj

/-- The original pullback comparison preserves the reconstructed group laws. -/
theorem fppfIso_isMonHom :
    letI := s.fppfGroupObj
    IsMonHom s.iso.hom := by
  let := s.fppfGroupObj
  constructor
  · rw [Functor.obj.η_def, Category.assoc]
    change Functor.LaxMonoidal.ε (Over.pullback p) ≫ s.localSection η[s.obj] = _
    rw [MonObj.one_eq_one, s.fppfLocalSection_group_one, MonObj.comp_one,
      ← MonObj.one_eq_one]
  · rw [Functor.obj.μ_def, Category.assoc]
    change Functor.LaxMonoidal.μ (Over.pullback p) s.obj s.obj ≫ s.localSection μ[s.obj] = _
    rw [MonObj.mul_eq_mul, s.fppfLocalSection_group_mul, MonObj.comp_mul]
    simp only [localSection, ← Category.assoc, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd]
    simp only [Hom.mul_def, lift_fst_comp_snd_comp]

/-- The actual group-scheme pullback isomorphism. -/
def fppfGroupIso : (baseChange p).obj s.fppfGroupScheme ≅ G := by
  letI := s.fppfGroupObj
  letI := s.fppfIso_isMonHom
  exact Grp.mkIso' s.iso

@[simp] theorem fppfGroupIso_hom : s.fppfGroupIso.hom.hom.hom = s.iso.hom := rfl

@[simp] theorem fppfGroupIso_inv : s.fppfGroupIso.inv.hom.hom = s.iso.inv := rfl

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (q : T ⟶ U)
    {H I : GroupScheme U} (a : H ⟶ I) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst I.X.hom q =
      pullback.fst H.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Any comparison preserving the quotient projection respects the datum. -/
theorem fppfCompatible_of_proj (e : (baseChange p).obj s.fppfGroupScheme ⟶ G)
    (he : e.hom.hom.left ≫ s.proj = pullback.fst s.obj.hom p) :
    Compatible (canonicalDatum p s.fppfGroupScheme) D e := by
  let C := s.fppfGroupScheme
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
theorem fppfGroupIso_compatible :
    Compatible (canonicalDatum p s.fppfGroupScheme) D s.fppfGroupIso.hom :=
  s.fppfCompatible_of_proj _ (by
    simpa only [s.fppfGroupIso_hom] using s.iso_hom_proj)

/-- The reconstructed group scheme solves the actual datum. -/
def fppfSolution : Solution D where
  obj := s.fppfGroupScheme
  iso := s.fppfGroupIso
  compatible := s.fppfGroupIso_compatible

end SchemeSolution

end Langlands.GroupScheme.Descent
