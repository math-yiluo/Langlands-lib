import Langlands.Representation.Category.CoproductSize

/-! # Composition of supplied coproduct cofans -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cofan

universe uC vC uI uJ

variable {C : Type uC} [Category.{vC} C]
  {I : Type uI} {J : I → Type uJ} (A : ∀ i, J i → C)

/-- Compose an outer cofan with the legs of its supplied inner cofans. -/
def sigmaCofan (t : ∀ i, Limits.Cofan (A i))
    (s : Limits.Cofan (fun i => (t i).pt)) :
    Limits.Cofan (fun p : Σ i, J i => A p.1 p.2) :=
  Limits.Cofan.mk s.pt (fun p => (t p.1).inj p.2 ≫ s.inj p.1)

/-- Iterating supplied coproduct universal properties gives the universal
property of their actual sigma-indexed composite cofan. -/
def sigmaCofanIsColimit (t : ∀ i, Limits.Cofan (A i))
    (s : Limits.Cofan (fun i => (t i).pt))
    (ht : ∀ i, IsColimit (t i)) (hs : IsColimit s) :
    IsColimit (sigmaCofan A t s) := by
  let inner (q : Limits.Cofan (fun p : Σ i, J i => A p.1 p.2)) (i : I) :
      Limits.Cofan (A i) := Limits.Cofan.mk q.pt (fun j => q.inj ⟨i, j⟩)
  let outer (q : Limits.Cofan (fun p : Σ i, J i => A p.1 p.2)) :
      Limits.Cofan (fun i => (t i).pt) :=
    Limits.Cofan.mk q.pt (fun i => (ht i).desc (inner q i))
  refine Limits.Cofan.IsColimit.mk _ (fun q => hs.desc (outer q)) ?_ ?_
  · intro q p
    have hout := hs.fac (outer q) ⟨p.1⟩
    change s.inj p.1 ≫ hs.desc (outer q) = (ht p.1).desc (inner q p.1) at hout
    change ((t p.1).inj p.2 ≫ s.inj p.1) ≫ hs.desc (outer q) = q.inj p
    rw [Category.assoc, hout]
    exact (ht p.1).fac (inner q p.1) ⟨p.2⟩
  · intro q m hm
    change s.pt ⟶ q.pt at m
    apply hs.hom_ext
    rintro ⟨i⟩
    apply (ht i).hom_ext
    rintro ⟨j⟩
    have hout := hs.fac (outer q) ⟨i⟩
    change s.inj i ≫ hs.desc (outer q) = (ht i).desc (inner q i) at hout
    have hin := (ht i).fac (inner q i) ⟨j⟩
    change (t i).inj j ≫ (ht i).desc (inner q i) = q.inj ⟨i, j⟩ at hin
    change (t i).inj j ≫ s.inj i ≫ m =
      (t i).inj j ≫ s.inj i ≫ hs.desc (outer q)
    rw [hout, hin]
    exact (Category.assoc _ _ _).symm.trans (hm ⟨i, j⟩)

section Option

variable [HasZeroMorphisms C] {K : Type uI} {B : Option K → C}

/-- Delete the `none` leg of a supplied cofan, keeping its actual vertex. -/
def someCofan (s : Limits.Cofan B) : Limits.Cofan (fun k => B (some k)) :=
  Limits.Cofan.mk s.pt (fun k => s.inj (some k))

/-- Deleting a zero `none` summand preserves the actual coproduct property. -/
def someCofanIsColimit (s : Limits.Cofan B) (hs : IsColimit s)
    (hzero : IsZero (B none)) : IsColimit (someCofan s) := by
  let extend (q : Limits.Cofan (fun k => B (some k))) : Limits.Cofan B :=
    Limits.Cofan.mk q.pt (fun k => match k with | none => 0 | some k => q.inj k)
  refine Limits.Cofan.IsColimit.mk _ (fun q => hs.desc (extend q)) ?_ ?_
  · intro q k
    exact hs.fac (extend q) ⟨some k⟩
  · intro q m hm
    apply hs.hom_ext
    rintro ⟨k⟩
    cases k with
    | none => exact hzero.eq_of_src _ _
    | some k => exact (hm k).trans (hs.fac (extend q) ⟨some k⟩).symm

end Option

end Langlands.Cofan
