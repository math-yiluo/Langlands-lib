import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Fpqc descent of compatible group-scheme homomorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Descent.FpqcHomDescent

variable {B S : Scheme.{u}} (p : S ⟶ B) {C D : GroupScheme B}

private abbrev proj (C : GroupScheme B) := pullback.fst C.X.hom p

@[reassoc] private theorem map_fst {T U : Scheme.{u}} (q : T ⟶ U)
    {G H : GroupScheme U} (a : G ⟶ H) :
    ((baseChange q).map a).hom.hom.left ≫ pullback.fst H.X.hom q =
      pullback.fst G.X.hom q ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

variable (f : (baseChange p).obj C ⟶ (baseChange p).obj D)
    (hf : Compatible (canonicalDatum p C) (canonicalDatum p D) f)

include hf

/-- Compatibility with canonical data identifies the two values above any equal images. -/
theorem comp_eq_of_projection_eq {Z : Scheme.{u}}
    (a b : Z ⟶ ((baseChange p).obj C).X.left)
    (hab : a ≫ proj p C = b ≫ proj p C) :
    a ≫ f.hom.hom.left ≫ proj p D = b ≫ f.hom.hom.left ≫ proj p D := by
  let r : Z ⟶ Overlap p := pullback.lift
    (a ≫ pullback.snd C.X.hom p) (b ≫ pullback.snd C.X.hom p) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hab,
        Category.assoc, pullback.condition, ← Category.assoc])
  let x : Z ⟶ ((baseChange (fst p)).obj ((baseChange p).obj C)).X.left :=
    pullback.lift a r (by simp [r])
  have hx : x ≫ (canonicalOverlap p C).hom.hom.hom.left ≫
      pullback.fst ((baseChange p).obj C).X.hom (snd p) = b := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, canonicalOverlap_fst, x, pullback.lift_fst_assoc]
        using hab
    · have hw := Over.w (canonicalOverlap p C).hom.hom.hom
      change (canonicalOverlap p C).hom.hom.hom.left ≫
        pullback.snd ((baseChange p).obj C).X.hom (snd p) =
        pullback.snd ((baseChange p).obj C).X.hom (fst p) at hw
      change x ≫ (canonicalOverlap p C).hom.hom.hom.left ≫
        pullback.fst ((baseChange p).obj C).X.hom (snd p) ≫
          ((baseChange p).obj C).X.hom = b ≫ pullback.snd C.X.hom p
      simp only [pullback.condition, reassoc_of% hw,
        x, pullback.lift_snd_assoc, r, pullback.lift_snd]
  have h := congrArg
    (fun g => x ≫ g.hom.hom.left ≫
      pullback.fst ((baseChange p).obj D).X.hom (snd p) ≫ proj p D) hf
  change x ≫ (((baseChange (fst p)).map f).hom.hom.left ≫
      (canonicalOverlap p D).hom.hom.hom.left) ≫ _ ≫ _ =
    x ≫ ((canonicalOverlap p C).hom.hom.hom.left ≫
      ((baseChange (snd p)).map f).hom.hom.left) ≫ _ ≫ _ at h
  simpa only [Category.assoc, canonicalOverlap_fst, map_fst_assoc,
    reassoc_of% hx, x, pullback.lift_fst_assoc] using h

variable [Flat p] [Surjective p] [QuasiCompact p]

/-- The underlying scheme map obtained from the fpqc effective epimorphism. -/
def underlying : C.X.left ⟶ D.X.left :=
  EffectiveEpi.desc (proj p C) (f.hom.hom.left ≫ proj p D)
    (fun a b hab => comp_eq_of_projection_eq p f hf a b hab)

@[reassoc] theorem underlying_fac :
    proj p C ≫ underlying p f hf = f.hom.hom.left ≫ proj p D :=
  EffectiveEpi.fac _ _ _

/-- The descended map respects the original structure morphisms. -/
theorem underlying_over : underlying p f hf ≫ D.X.hom = C.X.hom := by
  apply (cancel_epi (proj p C)).mp
  rw [← Category.assoc, underlying_fac]
  have hw : f.hom.hom.left ≫ pullback.snd D.X.hom p =
      pullback.snd C.X.hom p := Over.w f.hom.hom
  simpa only [Category.assoc, proj, pullback.condition] using
    congrArg (fun q => q ≫ p) hw

/-- The underlying descended morphism in the slice category. -/
def overHom : C.X ⟶ D.X := Over.homMk (underlying p f hf) (underlying_over p f hf)

/-- Pullback recovers the supplied underlying morphism in the slice. -/
theorem pullback_overHom :
    (Over.pullback p).map (overHom p f hf) = f.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (underlying_fac p f hf)
  · exact (pullback.lift_snd _ _ _).trans (Over.w f.hom.hom).symm

/-- Faithful monoidal pullback reflects the unit and multiplication laws. -/
theorem overHom_isMonHom : IsMonHom (overHom p f hf) := by
  have : IsMonHom ((Over.pullback p).map (overHom p f hf)) := by
    rw [pullback_overHom]
    infer_instance
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap (Over.pullback p) _

/-- Descend the actual group-scheme homomorphism. -/
def hom : C ⟶ D :=
  letI := overHom_isMonHom p f hf
  Grp.homMk (overHom p f hf)

/-- Base change of the descended homomorphism recovers the given one. -/
theorem baseChange_hom : (baseChange p).map (hom p f hf) = f := by
  apply Grp.hom_ext
  exact pullback_overHom p f hf

/-- Descent is unique among homomorphisms with the same base change. -/
theorem unique (a : C ⟶ D) (ha : (baseChange p).map a = f) :
    a = hom p f hf := by
  apply Grp.hom_ext
  apply (Over.pullback p).map_injective
  change ((baseChange p).map a).hom.hom =
    ((baseChange p).map (hom p f hf)).hom.hom
  rw [ha, baseChange_hom]

/-- Every compatible homomorphism has exactly one descent over the base. -/
theorem existsUnique_hom :
    ∃! a : C ⟶ D, (baseChange p).map a = f :=
  ⟨hom p f hf, baseChange_hom p f hf, fun a ha => unique p f hf a ha⟩

end Langlands.GroupScheme.Descent.FpqcHomDescent

namespace Langlands.GroupScheme.Descent.Solution

variable {B S : Scheme.{u}} {p : S ⟶ B}
    {G H : GroupScheme S} {D : Datum p G} {E : Datum p H}
    [Flat p] [Surjective p] [QuasiCompact p]
    (s : Solution D) (t : Solution E) (f : G ⟶ H) (hf : Compatible D E f)

include hf

/-- Descend a compatible homomorphism through any two solutions. -/
def descendHom : s.obj ⟶ t.obj :=
  FpqcHomDescent.hom p (s.iso.hom ≫ f ≫ t.iso.inv)
    ((s.compatible.comp hf).comp (t.compatible.inv t.iso))

/-- The descended homomorphism commutes with the solution identifications. -/
theorem baseChange_descendHom :
    (baseChange p).map (descendHom s t f hf) ≫ t.iso.hom = s.iso.hom ≫ f := by
  rw [descendHom, FpqcHomDescent.baseChange_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The compatible square determines the descended homomorphism uniquely. -/
theorem descendHom_unique (a : s.obj ⟶ t.obj)
    (ha : (baseChange p).map a ≫ t.iso.hom = s.iso.hom ≫ f) :
    a = descendHom s t f hf := by
  apply FpqcHomDescent.unique
  rw [← Category.assoc s.iso.hom f t.iso.inv, ← ha]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Compatible morphisms between solved data descend uniquely. -/
theorem existsUnique_descendHom :
    ∃! a : s.obj ⟶ t.obj,
      (baseChange p).map a ≫ t.iso.hom = s.iso.hom ≫ f :=
  ⟨descendHom s t f hf, baseChange_descendHom s t f hf,
    fun a ha => descendHom_unique s t f hf a ha⟩

end Langlands.GroupScheme.Descent.Solution
