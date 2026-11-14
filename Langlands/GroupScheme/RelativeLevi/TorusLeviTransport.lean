import Langlands.GroupScheme.RelativeLevi.TorusLeviBaseChange
import Langlands.GroupScheme.RelativeLevi.AmbientTransport

/-! # Transport of unique Levi witnesses containing a prescribed group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi.TorusLeviWitness

variable {S : Scheme.{u}} {P Q : GroupScheme S} {T T' : CommGroupScheme S}
    {t : T.toGrp ⟶ P} {t' : T'.toGrp ⟶ P}

/-- Replacing the prescribed group by another map with the same all-test
range retains the actual Levi witness. -/
def ofRangeEq (w : TorusLeviWitness t)
    (h : SubgroupFunctor.range t' = SubgroupFunctor.range t) :
    TorusLeviWitness t' where
  group := w.group
  inclusion := w.inclusion
  isLevi := w.isLevi
  contains := h.le.trans w.contains
  unique L l hl ht := w.unique L l hl (h.ge.trans ht)

/-- Transport the actual inclusion and its unique containment property
through an isomorphism of ambient groups. -/
def compIso (w : TorusLeviWitness t) (e : P ≅ Q) :
    TorusLeviWitness (t ≫ e.hom) where
  group := w.group
  inclusion := w.inclusion ≫ e.hom
  isLevi := w.isLevi.comp_iso e
  contains := (SubgroupFunctor.range_comp_iso_le_iff t w.inclusion e).mpr w.contains
  unique L l hl ht := by
    have hc : SubgroupFunctor.range t ≤ SubgroupFunctor.range (l ≫ e.inv) :=
      (SubgroupFunctor.range_comp_iso_le_iff t (l ≫ e.inv) e).mp (by
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht)
    have hw := w.unique L (l ≫ e.inv) (hl.comp_iso e.symm) hc
    have he := (SubgroupFunctor.range_comp_iso_eq_iff (l ≫ e.inv) w.inclusion e).mpr hw
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he

/-- A commuting square with isomorphisms on the prescribed group and its
ambient group transports the actual unique Levi witness. -/
def transport (w : TorusLeviWitness t) {q : T'.toGrp ⟶ Q}
    (e : P ≅ Q) (a : T.toGrp ≅ T'.toGrp) (h : a.hom ≫ q = t ≫ e.hom) :
    TorusLeviWitness q :=
  (w.compIso e).ofRangeEq (by rw [← h, SubgroupFunctor.range_iso_comp])

@[simp] theorem transport_group (w : TorusLeviWitness t) {q : T'.toGrp ⟶ Q}
    (e : P ≅ Q) (a : T.toGrp ≅ T'.toGrp) (h : a.hom ≫ q = t ≫ e.hom) :
    (w.transport e a h).group = w.group := rfl

@[simp] theorem transport_inclusion (w : TorusLeviWitness t) {q : T'.toGrp ⟶ Q}
    (e : P ≅ Q) (a : T.toGrp ≅ T'.toGrp) (h : a.hom ≫ q = t ≫ e.hom) :
    (w.transport e a h).inclusion = w.inclusion ≫ e.hom := rfl

end Langlands.GroupScheme.RelativeLevi.TorusLeviWitness
