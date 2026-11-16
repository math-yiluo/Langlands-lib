import Langlands.GroupScheme.Lie.DeterminantLineBundle
import Langlands.GroupScheme.RelativeLevi.ParabolicLieFiniteFrames

/-! # Actual Lie determinants of parabolic representatives -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open Langlands.AlgebraicGeometry.Picard TorusSubgroupModuli

namespace ParabolicRepresentative

variable {S : Scheme.{u}} {G : GroupScheme S} {F : ParabolicSubgroup G}

/-- The unique inclusion-compatible isomorphism between actual representatives. -/
def iso (r r' : ParabolicRepresentative F) : r.group ≅ r'.group :=
  r.represents.isoOfIsRepresentedBy r'.represents

@[reassoc]
lemma iso_hom_comp (r r' : ParabolicRepresentative F) :
    (r.iso r').hom ≫ r'.hom = r.hom :=
  r.represents.isoOfIsRepresentedBy_hom_comp r'.represents

/-- Inclusion compatibility characterizes the representative isomorphism. -/
lemma iso_unique (r r' : ParabolicRepresentative F) (e : r.group ≅ r'.group)
    (he : e.hom ≫ r'.hom = r.hom) : e = r.iso r' := by
  apply Iso.ext
  apply r'.represents.hom_ext
  rw [he, iso_hom_comp]

@[simp]
lemma iso_self (r : ParabolicRepresentative F) : r.iso r = Iso.refl r.group := by
  symm
  apply iso_unique
  exact Category.id_comp _

lemma iso_trans (r r' r'' : ParabolicRepresentative F) :
    r.iso r' ≪≫ r'.iso r'' = r.iso r'' := by
  apply iso_unique
  simp only [Iso.trans_hom, Category.assoc, iso_hom_comp]

/-- The determinant line of the actual Lie sheaf of this representative. -/
def lieDeterminant (r : ParabolicRepresentative F) : LineBundle S :=
  smoothLieDeterminant r.group r.parabolic.smooth

/-- Determinants of the unique group isomorphisms compare representatives. -/
def lieDeterminantChangeIso (r r' : ParabolicRepresentative F) :
    r.lieDeterminant ≅ r'.lieDeterminant :=
  smoothLieDeterminantIso r.parabolic.smooth r'.parabolic.smooth (r.iso r')

@[simp]
lemma lieDeterminantChangeIso_self (r : ParabolicRepresentative F) :
    r.lieDeterminantChangeIso r = Iso.refl _ := by
  simp [lieDeterminantChangeIso, lieDeterminant]

lemma lieDeterminantChangeIso_trans (r r' r'' : ParabolicRepresentative F) :
    r.lieDeterminantChangeIso r' ≪≫ r'.lieDeterminantChangeIso r'' =
      r.lieDeterminantChangeIso r'' := by
  simp only [lieDeterminantChangeIso, smoothLieDeterminantIso_comp, iso_trans]

section Restriction

variable {B : Scheme.{u}} {H : GroupScheme B} {M T : Over B}
    {K : ParabolicSubgroup ((baseChange M.hom).obj H)}

/-- Pull back an actual representative using the actual evaluated inclusion. -/
def restrict (r : ParabolicRepresentative K) (hH : IsReductive H) (a : T ⟶ M) :
    ParabolicRepresentative (ParabolicSubgroupModuli.restrict hH a K) where
  group := (baseChange a.left).obj r.group
  hom := familyHom r.hom a
  parabolic := isRelativeParabolicSubgroup_familyHom hH r.hom r.parabolic a
  represents := ⟨(isRelativeParabolicSubgroup_familyHom hH r.hom r.parabolic a).mono,
    (restrict_eq_evaluate hH K r.hom r.represents.2 a).symm⟩

/-- Changing representatives commutes with actual restriction of their groups. -/
lemma iso_restrict (r r' : ParabolicRepresentative K) (hH : IsReductive H)
    (a : T ⟶ M) :
    (r.restrict hH a).iso (r'.restrict hH a) = (baseChange a.left).mapIso (r.iso r') := by
  symm
  apply iso_unique (r.restrict hH a) (r'.restrict hH a)
  change (baseChange a.left).map (r.iso r').hom ≫
      ((baseChange a.left).map r'.hom ≫ _) = (baseChange a.left).map r.hom ≫ _
  rw [← Category.assoc, ← Functor.map_comp, iso_hom_comp]

/-- The actual Lie determinant comparison for an evaluated representative. -/
def restrictLieDeterminantIso (r : ParabolicRepresentative K) (hH : IsReductive H)
    (a : T ⟶ M) :
    (LineBundle.pullback a.left).obj r.lieDeterminant ≅
      (r.restrict hH a).lieDeterminant :=
  smoothLieDeterminantBaseChangeIso a.left r.group r.parabolic.smooth

/-- Restriction comparisons intertwine the canonical changes of representatives. -/
lemma restrictLieDeterminantIso_naturality (r r' : ParabolicRepresentative K)
    (hH : IsReductive H) (a : T ⟶ M) :
    (LineBundle.pullback a.left).mapIso (r.lieDeterminantChangeIso r') ≪≫
        r'.restrictLieDeterminantIso hH a =
      r.restrictLieDeterminantIso hH a ≪≫
        (r.restrict hH a).lieDeterminantChangeIso (r'.restrict hH a) := by
  dsimp only [lieDeterminantChangeIso, restrictLieDeterminantIso]
  rw [iso_restrict]
  exact smoothLieDeterminantBaseChangeIso_naturality a.left
    r.parabolic.smooth r'.parabolic.smooth (r.iso r')

end Restriction
end ParabolicRepresentative
end Langlands.GroupScheme.ParabolicSubgroupModuli
