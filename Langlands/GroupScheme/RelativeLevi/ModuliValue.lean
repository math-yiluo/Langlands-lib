import Langlands.GroupScheme.RelativeLevi.AmbientTransport
import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.GroupScheme.InnerAutomorphism

/-! # Actual images of relative Levi subgroups and conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {P P' U L : GroupScheme S}

namespace RelativeLevi

/-- The admissible subgroup functors are precisely the images of actual relative
Levi inclusions. Presentations are not part of an element's equality. -/
def IsLeviImage (F : SubgroupFunctor P) : Prop :=
  ∃ (L : GroupScheme S) (l : L ⟶ P),
    IsRelativeLeviSubgroup l ∧ SubgroupFunctor.range l = F

/-- The set of relative Levi subgroup images of a fixed group scheme.
It lies in `Type (u+1)` because subgroup functors test all schemes in universe `u`. -/
def LeviImage (P : GroupScheme S) : Type (u + 1) :=
  {F : SubgroupFunctor P // IsLeviImage F}

namespace LeviImage

/-- An actual relative Levi inclusion determines its image-valued moduli point. -/
def ofHom (l : L ⟶ P) (hl : IsRelativeLeviSubgroup l) : LeviImage P :=
  ⟨SubgroupFunctor.range l, L, l, hl, rfl⟩

/-- Every moduli point has an actual relative Levi presentation over the same base. -/
theorem exists_presentation (F : LeviImage P) :
    ∃ (L : GroupScheme S) (l : L ⟶ P),
      IsRelativeLeviSubgroup l ∧ SubgroupFunctor.range l = F.val :=
  F.property

@[ext]
theorem ext {F F' : LeviImage P} (h : F.val = F'.val) : F = F' :=
  Subtype.ext h

/-- Equality forgets the presenting source and retains exactly the subgroup image. -/
theorem ofHom_eq_iff {L' : GroupScheme S} (l : L ⟶ P) (l' : L' ⟶ P)
    (hl : IsRelativeLeviSubgroup l) (hl' : IsRelativeLeviSubgroup l') :
    ofHom l hl = ofHom l' hl' ↔
      SubgroupFunctor.range l = SubgroupFunctor.range l' := by
  exact Subtype.ext_iff

/-- Transport of moduli points through an actual ambient isomorphism. -/
def mapIso (e : P ≅ P') (F : LeviImage P) : LeviImage P' := by
  refine ⟨F.val.comap e.inv, ?_⟩
  obtain ⟨K, l, hl, hF⟩ := F.exists_presentation
  exact ⟨K, l ≫ e.hom, hl.comp_iso e, by
    rw [SubgroupFunctor.range_comp_iso, hF]⟩

end LeviImage

/-- Conjugation of an all-test subgroup functor by an actual point over the base. -/
def conjugateImage (g : Over.mk (𝟙 S) ⟶ P.X)
    (F : SubgroupFunctor P) : SubgroupFunctor P where
  carrier T := (F.carrier T).map (MulAut.conj (P.constantPoint g T)).toMonoidHom
  comp_mem a x := by
    rintro ⟨y, hy, rfl⟩
    exact ⟨a ≫ y, F.comp_mem a hy, P.constantPoint_conj_naturality g a y⟩

/-- Conjugating the image of an inclusion is the image of its actual inner conjugate. -/
theorem conjugateImage_range (g : Over.mk (𝟙 S) ⟶ P.X) (l : L ⟶ P) :
    conjugateImage g (SubgroupFunctor.range l) =
      SubgroupFunctor.range (l ≫ (P.innerIso g).hom) := by
  ext T x
  change (∃ y : T ⟶ P.X, (∃ z : T ⟶ L.X, z ≫ l.hom.hom = y) ∧
    MulAut.conj (P.constantPoint g T) y = x) ↔
      ∃ z : T ⟶ L.X, z ≫ (l ≫ (P.innerIso g).hom).hom.hom = x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, P.comp_innerIso_hom]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨z ≫ l.hom.hom, ⟨z, rfl⟩, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, P.comp_innerIso_hom]
    rfl

@[simp]
theorem conjugateImage_one (F : SubgroupFunctor P) :
    conjugateImage (1 : Over.mk (𝟙 S) ⟶ P.X) F = F := by
  ext T x
  change (∃ y, y ∈ F.carrier T ∧
    MulAut.conj (P.constantPoint 1 T) y = x) ↔ x ∈ F.carrier T
  have hc : P.constantPoint 1 T = 1 := MonObj.comp_one _
  simp [hc]

theorem conjugateImage_mul (g h : Over.mk (𝟙 S) ⟶ P.X)
    (F : SubgroupFunctor P) :
    conjugateImage (g * h) F = conjugateImage g (conjugateImage h F) := by
  ext T x
  change (∃ y, y ∈ F.carrier T ∧
    MulAut.conj (P.constantPoint (g * h) T) y = x) ↔
      ∃ z, (∃ y, y ∈ F.carrier T ∧
        MulAut.conj (P.constantPoint h T) y = z) ∧
          MulAut.conj (P.constantPoint g T) z = x
  have hc : P.constantPoint (g * h) T =
      P.constantPoint g T * P.constantPoint h T := MonObj.comp_mul _ _ _
  have he (y : T ⟶ P.X) :
      MulAut.conj (P.constantPoint (g * h) T) y =
        MulAut.conj (P.constantPoint g T)
          (MulAut.conj (P.constantPoint h T) y) := by
    rw [hc]
    simp only [MulAut.conj_apply]
    group
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, (he y).symm⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, he y⟩

namespace LeviImage

/-- Actual conjugation acts on the relative Levi subgroup images. -/
def conjugate (g : Over.mk (𝟙 S) ⟶ P.X) (F : LeviImage P) : LeviImage P := by
  refine ⟨conjugateImage g F.val, ?_⟩
  obtain ⟨K, l, hl, hF⟩ := F.exists_presentation
  refine ⟨K, l ≫ (P.innerIso g).hom, hl.comp_iso _, ?_⟩
  rw [← conjugateImage_range, hF]

/-- The conjugation action of a supplied homomorphism, in particular of a supplied
relative unipotent radical. No radical-existence theorem is used to define it. -/
@[instance_reducible]
def conjugationAction (r : U ⟶ P) :
    MulAction (Over.mk (𝟙 S) ⟶ U.X) (LeviImage P) where
  smul g F := F.conjugate (g ≫ r.hom.hom)
  one_smul F := by
    apply ext
    change conjugateImage (1 ≫ r.hom.hom) F.val = F.val
    rw [MonObj.one_comp, conjugateImage_one]
  mul_smul g h F := by
    apply ext
    change conjugateImage ((g * h) ≫ r.hom.hom) F.val =
      conjugateImage (g ≫ r.hom.hom) (conjugateImage (h ≫ r.hom.hom) F.val)
    rw [MonObj.mul_comp, conjugateImage_mul]

/-- On a presented Levi, the action is the image of the actual inner conjugate. -/
theorem conjugate_ofHom (g : Over.mk (𝟙 S) ⟶ P.X)
    (l : L ⟶ P) (hl : IsRelativeLeviSubgroup l) :
    (ofHom l hl).conjugate g =
      ofHom (l ≫ (P.innerIso g).hom) (hl.comp_iso _) :=
  ext (conjugateImage_range g l)

end LeviImage
end RelativeLevi
end Langlands.GroupScheme
