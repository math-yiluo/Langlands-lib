import Langlands.GroupScheme.Descent.AffineDatumScheme
import Langlands.GroupScheme.Descent.SectionTransport

/-! # Compatible local sections of an actual affine descent solution -/

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

variable {B S Z : Scheme.{u}} {p : S ⟶ B} {G : GroupScheme S}
  {D : Datum p G}

namespace AffineSchemeSolution

variable (s : AffineSchemeSolution D)

/-- The quotient identifies a point with its transported point. -/
theorem move_proj (a : Z ⟶ G.X.left) (z : Z ⟶ S)
    (h : a ≫ G.X.hom ≫ p = z ≫ p) :
    a ≫ s.proj = D.move a z h ≫ s.proj := by
  calc
    a ≫ s.proj = D.arrow a z h ≫ D.source ≫ s.proj := by simp
    _ = D.arrow a z h ≫ D.target ≫ s.proj := by rw [s.relation]
    _ = D.move a z h ≫ s.proj := by rw [← Category.assoc, D.arrow_target]

/-- Transport is characterized by equality in the actual quotient. -/
theorem sectionTransport_eq_iff (z₁ z₂ : Z ⟶ S) (h : z₁ ≫ p = z₂ ≫ p)
    (a : Over.mk z₁ ⟶ G.X) (b : Over.mk z₂ ⟶ G.X) :
    D.sectionTransport z₁ z₂ h a = b ↔ a.left ≫ s.proj = b.left ≫ s.proj := by
  have ha : a.left ≫ G.X.hom = z₁ := Over.w a
  have hb : b.left ≫ G.X.hom = z₂ := Over.w b
  constructor
  · intro hab
    have ht := congrArg Over.Hom.left hab
    rw [D.sectionTransport_left] at ht
    exact (s.move_proj a.left z₂ _).trans (congrArg (· ≫ s.proj) ht)
  · intro hab
    let r := s.kernelPair.lift a.left b.left hab
    have hs : r ≫ D.source = a.left := s.kernelPair.lift_fst _ _ _
    have ht : r ≫ D.target = b.left := s.kernelPair.lift_snd _ _ _
    have hm := D.move_relation r
    have htb : r ≫ D.target ≫ G.X.hom = z₂ := by
      rw [← Category.assoc, ht, hb]
    simp only [hs, ht, htb] at hm
    apply Over.OverMorphism.ext
    rw [D.sectionTransport_left]
    exact hm

private def pointSection {U : Over S} (x : U ⟶ G.X) (a : Z ⟶ U.left) :
    Over.mk (a ≫ U.hom) ⟶ G.X :=
  Over.homMk a rfl ≫ x

private theorem pair_base (U : Over B)
    (a b : Z ⟶ ((Over.pullback p).obj U).left)
    (hab : a ≫ pullback.fst U.hom p = b ≫ pullback.fst U.hom p) :
    (a ≫ ((Over.pullback p).obj U).hom) ≫ p =
      (b ≫ ((Over.pullback p).obj U).hom) ≫ p := by
  change (a ≫ pullback.snd U.hom p) ≫ p = (b ≫ pullback.snd U.hom p) ≫ p
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc, hab]
  simp only [Category.assoc]

/-- Local sections respecting transport form a subgroup. -/
def sectionSubgroup (U : Over B) :
    Subgroup ((Over.pullback p).obj U ⟶ G.X) where
  carrier x := ∀ (Z : Scheme.{u}) (a b : Z ⟶ ((Over.pullback p).obj U).left)
    (hab : a ≫ pullback.fst U.hom p = b ≫ pullback.fst U.hom p),
    D.sectionTransport (a ≫ ((Over.pullback p).obj U).hom)
      (b ≫ ((Over.pullback p).obj U).hom) (pair_base U a b hab)
      (pointSection x a) = pointSection x b
  one_mem' := by
    intro Z a b hab
    simp only [pointSection, MonObj.comp_one, map_one]
  mul_mem' hx hy := by
    intro Z a b hab
    simpa only [pointSection, MonObj.comp_mul, map_mul] using
      congrArg₂ (· * ·) (hx Z a b hab) (hy Z a b hab)
  inv_mem' hx := by
    intro Z a b hab
    simpa only [pointSection, GrpObj.comp_inv, map_inv] using
      congrArg Inv.inv (hx Z a b hab)

/-- Restriction of a section of the quotient to the covering scheme. -/
def localSection {U : Over B} (f : U ⟶ s.obj) :
    (Over.pullback p).obj U ⟶ G.X :=
  (Over.pullback p).map f ≫ s.iso.hom

@[reassoc] theorem localSection_proj {U : Over B} (f : U ⟶ s.obj) :
    (s.localSection f).left ≫ s.proj = pullback.fst U.hom p ≫ f.left := by
  simp only [localSection, Over.comp_left, Category.assoc, s.iso_hom_proj,
    Over.pullback_map_left, pullback.lift_fst]

theorem localSection_mem {U : Over B} (f : U ⟶ s.obj) :
    s.localSection f ∈ sectionSubgroup (D := D) U := by
  intro Z a b hab
  apply (s.sectionTransport_eq_iff _ _ _ _ _).mpr
  change (a ≫ (s.localSection f).left) ≫ s.proj =
    (b ≫ (s.localSection f).left) ≫ s.proj
  simpa only [Category.assoc, s.localSection_proj] using
    congrArg (· ≫ f.left) hab

variable [Flat p] [Surjective p] [QuasiCompact p]

theorem localSection_injective (U : Over B) :
    Function.Injective (s.localSection (U := U)) := by
  intro f g h
  apply (Over.pullback p).map_injective
  exact (cancel_mono s.iso.hom).mp h

omit [Flat p] [Surjective p] [QuasiCompact p] in
private theorem invariant_section {U : Over B}
    (x : sectionSubgroup (D := D) U) (a b : Z ⟶ ((Over.pullback p).obj U).left)
    (hab : a ≫ pullback.fst U.hom p = b ≫ pullback.fst U.hom p) :
    a ≫ x.val.left ≫ s.proj = b ≫ x.val.left ≫ s.proj := by
  have h := (s.sectionTransport_eq_iff _ _ _ _ _).mp (x.property Z a b hab)
  change (a ≫ x.val.left) ≫ s.proj = (b ≫ x.val.left) ≫ s.proj at h
  simpa only [Category.assoc] using h

private def sectionDescLeft {U : Over B} (x : sectionSubgroup (D := D) U) :
    U.left ⟶ s.obj.left :=
  EffectiveEpi.desc (pullback.fst U.hom p) (x.val.left ≫ s.proj)
    (fun a b hab => s.invariant_section x a b hab)

@[reassoc] private theorem sectionDescLeft_fac {U : Over B} (x : sectionSubgroup (D := D) U) :
    pullback.fst U.hom p ≫ s.sectionDescLeft x = x.val.left ≫ s.proj :=
  EffectiveEpi.fac _ _ _

private theorem sectionDescLeft_over {U : Over B} (x : sectionSubgroup (D := D) U) :
    s.sectionDescLeft x ≫ s.obj.hom = U.hom := by
  apply (cancel_epi (pullback.fst U.hom p)).mp
  rw [← Category.assoc, s.sectionDescLeft_fac]
  rw [Category.assoc, ← s.square.w, ← Category.assoc, Over.w x.val]
  exact pullback.condition.symm

/-- Descent of every compatible local section. -/
def sectionDesc {U : Over B} (x : sectionSubgroup (D := D) U) : U ⟶ s.obj :=
  Over.homMk (s.sectionDescLeft x) (s.sectionDescLeft_over x)

@[simp] theorem localSection_sectionDesc {U : Over B} (x : sectionSubgroup (D := D) U) :
    s.localSection (s.sectionDesc x) = x.val := by
  apply Over.OverMorphism.ext
  apply s.square.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · rw [s.localSection_proj]
    exact s.sectionDescLeft_fac x

/-- The descended scheme represents the compatible local sections. -/
def sectionEquiv (U : Over B) : (U ⟶ s.obj) ≃ sectionSubgroup (D := D) U where
  toFun f := ⟨s.localSection f, s.localSection_mem f⟩
  invFun := s.sectionDesc
  left_inv _f := s.localSection_injective U (s.localSection_sectionDesc _)
  right_inv x := Subtype.ext (s.localSection_sectionDesc x)

end AffineSchemeSolution
end Langlands.GroupScheme.Descent
