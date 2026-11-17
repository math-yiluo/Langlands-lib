import Langlands.GroupScheme.Descent.FpqcHomDescent
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Actual homomorphism descent along arbitrary surjective fppf maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FppfHomDescent

variable {S U : Scheme.{u}} (p : U ⟶ S) [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  {C D : GroupScheme S}
  (f : (GroupScheme.baseChange p).obj C ⟶ (GroupScheme.baseChange p).obj D)
  (hf : Compatible (canonicalDatum p C) (canonicalDatum p D) f)

private abbrev proj (C : GroupScheme S) := pullback.fst C.X.hom p

/-- Descend the underlying scheme map using its fppf effective epimorphic projection. -/
def underlying : C.X.left ⟶ D.X.left :=
  EffectiveEpi.desc (proj p C) (f.hom.hom.left ≫ proj p D)
    (fun a b hab => FpqcHomDescent.comp_eq_of_projection_eq p f hf a b hab)

@[reassoc]
theorem underlying_fac :
    proj p C ≫ underlying p f hf = f.hom.hom.left ≫ proj p D :=
  EffectiveEpi.fac _ _ _

/-- The descended underlying map respects the original structure maps. -/
theorem underlying_over : underlying p f hf ≫ D.X.hom = C.X.hom := by
  apply (cancel_epi (proj p C)).mp
  rw [← Category.assoc, underlying_fac]
  have hw : f.hom.hom.left ≫ pullback.snd D.X.hom p =
      pullback.snd C.X.hom p := Over.w f.hom.hom
  simpa only [Category.assoc, proj, pullback.condition] using
    congrArg (fun q => q ≫ p) hw

/-- The actual descended map in the category of schemes over the base. -/
def overHom : C.X ⟶ D.X :=
  Over.homMk (underlying p f hf) (underlying_over p f hf)

/-- Pullback recovers the original underlying morphism. -/
theorem pullback_overHom :
    (Over.pullback p).map (overHom p f hf) = f.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (underlying_fac p f hf)
  · exact (pullback.lift_snd _ _ _).trans (Over.w f.hom.hom).symm

/-- Faithful monoidal pullback reflects the two homomorphism laws. -/
theorem overHom_isMonHom : IsMonHom (overHom p f hf) := by
  have : IsMonHom ((Over.pullback p).map (overHom p f hf)) := by
    rw [pullback_overHom]
    infer_instance
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback p) _

/-- The actual descended group-scheme homomorphism. -/
def hom : C ⟶ D :=
  letI := overHom_isMonHom p f hf
  Grp.homMk (overHom p f hf)

/-- Pullback recovers the original group homomorphism exactly. -/
theorem baseChange_hom : (GroupScheme.baseChange p).map (hom p f hf) = f := by
  apply Grp.hom_ext
  exact pullback_overHom p f hf

/-- Exact pullback recovery uniquely characterizes the descended homomorphism. -/
theorem unique (a : C ⟶ D) (ha : (GroupScheme.baseChange p).map a = f) :
    a = hom p f hf := by
  apply Grp.hom_ext
  apply (Over.pullback p).map_injective
  change ((GroupScheme.baseChange p).map a).hom.hom =
    ((GroupScheme.baseChange p).map (hom p f hf)).hom.hom
  rw [ha, baseChange_hom]

end Langlands.GroupScheme.Descent.FppfHomDescent

namespace Langlands.GroupScheme.Descent.Solution

variable {S U : Scheme.{u}} {p : U ⟶ S} [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  {G H : GroupScheme U} {D : Datum p G} {E : Datum p H}
  (s : Solution D) (t : Solution E) (f : G ⟶ H) (hf : Compatible D E f)

/-- Descend a compatible homomorphism through supplied solutions along any fppf cover. -/
def descendHomOfFppf : s.obj ⟶ t.obj :=
  FppfHomDescent.hom p (s.iso.hom ≫ f ≫ t.iso.inv)
    ((s.compatible.comp hf).comp (t.compatible.inv t.iso))

/-- The actual descended map recovers the supplied map through the solution comparisons. -/
theorem baseChange_descendHomOfFppf :
    (GroupScheme.baseChange p).map (descendHomOfFppf s t f hf) ≫ t.iso.hom =
      s.iso.hom ≫ f := by
  rw [descendHomOfFppf, FppfHomDescent.baseChange_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The compatible recovery square uniquely determines the descended map. -/
theorem descendHomOfFppf_unique (a : s.obj ⟶ t.obj)
    (ha : (GroupScheme.baseChange p).map a ≫ t.iso.hom = s.iso.hom ≫ f) :
    a = descendHomOfFppf s t f hf := by
  apply FppfHomDescent.unique
  rw [← Category.assoc s.iso.hom f t.iso.inv, ← ha]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.Descent.Solution
