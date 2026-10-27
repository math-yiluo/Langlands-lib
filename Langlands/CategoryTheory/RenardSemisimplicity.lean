import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Renard A.VII: the three semisimplicity conditions

Source: Renard, *Représentations des groupes réductifs p-adiques* (French edition
dated 9 July 2026), Appendix A.VII, printed page 265 / PDF page 271.

The three conditions of the lemma of A.VII are defined separately for an object
`X` of an arbitrary abelian category, on actual coproduct cofans, actual
categorical subobjects and actual binary coproduct comparisons. Object universe
`u`, Hom universe `v` and the index universe `w` of the coproduct condition are
independent. The source's Grothendieck and locally-finite-type hypotheses are
not needed for the definitions, and the equivalence of the three conditions is
not assumed.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard A.VII (i) at index size `w`: `X` is completely reducible, that is,
isomorphic to a direct sum of simple objects. Here `X` is the vertex of an
actual coproduct cofan of a `w`-indexed family of simple objects. The family may
be empty. -/
@[pp_with_univ]
def IsCompletelyReducible (X : C) : Prop :=
  ∃ (I : Type w) (S : I → C) (ι : ∀ i, S i ⟶ X),
    (∀ i, Simple (S i)) ∧ Nonempty (IsColimit (Cofan.mk X ι))

/-- Renard A.VII (ii): `X` is the sum of its simple subobjects, that is, `⊤` is
the least upper bound of the set of all simple subobjects of `X`. -/
def IsSumOfSimpleSubobjects (X : C) : Prop :=
  IsLUB {P : Subobject X | Simple (P : C)} ⊤

/-- Renard A.VII (iii): every subobject `P` of `X` has a complementary
subobject `Q` with `X = P ⊕ Q`, that is, the canonical map from the actual
binary coproduct `(P : C) ⨿ (Q : C)` to `X` induced by both inclusions is an
isomorphism. -/
def EverySubobjectHasComplement (X : C) : Prop :=
  ∀ P : Subobject X, ∃ Q : Subobject X, IsIso (coprod.desc P.arrow Q.arrow)

/-- A semisimple object: Renard A.VII (i) with index universe `max u v`, the
universe of `Subobject X`. The source uses "semi-simple" for the equivalent
conditions of its lemma; this alias is internal packaging, and its equivalence
with (ii) and (iii) is not asserted here. -/
def IsSemisimpleObject (X : C) : Prop :=
  IsCompletelyReducible.{max u v} X

/-- The alias `IsSemisimpleObject` unfolds to condition (i) at index universe
`max u v`. -/
theorem isSemisimpleObject_iff (X : C) :
    IsSemisimpleObject X ↔ IsCompletelyReducible.{max u v} X :=
  Iff.rfl

namespace IsCompletelyReducible

/-- Condition (i) is invariant under isomorphism. -/
theorem of_iso {X Y : C} (e : X ≅ Y) (h : IsCompletelyReducible.{w} X) :
    IsCompletelyReducible.{w} Y := by
  obtain ⟨I, S, ι, hS, ⟨hc⟩⟩ := h
  exact ⟨I, S, fun i => ι i ≫ e.hom, hS,
    ⟨IsColimit.ofIsoColimit hc (Cofan.ext e fun _ => rfl)⟩⟩

/-- Isomorphic objects satisfy condition (i) together. -/
theorem iff_of_iso {X Y : C} (e : X ≅ Y) :
    IsCompletelyReducible.{w} X ↔ IsCompletelyReducible.{w} Y :=
  ⟨of_iso e, of_iso e.symm⟩

/-- Condition (i) in the source's wording: `X` is isomorphic to the chosen
coproduct `∐ S` of a `w`-indexed family of simple objects having a coproduct. -/
theorem iff_exists_iso_sigma (X : C) :
    IsCompletelyReducible.{w} X ↔
      ∃ (I : Type w) (S : I → C) (_ : HasCoproduct S),
        (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ∐ S) := by
  constructor
  · rintro ⟨I, S, ι, hS, ⟨hc⟩⟩
    have : HasCoproduct S := HasColimit.mk ⟨_, hc⟩
    exact ⟨I, S, this, hS, ⟨hc.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩
  · rintro ⟨I, S, _, hS, ⟨e⟩⟩
    exact of_iso e.symm ⟨I, S, Sigma.ι S, hS, ⟨coproductIsCoproduct S⟩⟩

/-- A zero object is completely reducible: it is the coproduct of the empty
family. -/
theorem of_isZero {X : C} (hX : IsZero X) : IsCompletelyReducible.{w} X :=
  ⟨PEmpty, PEmpty.elim, fun i => i.elim, fun i => i.elim,
    ⟨Cofan.IsColimit.mk _ (fun s => hX.to_ s.pt) (fun _ i => i.elim)
      (fun _ _ _ => hX.eq_of_src _ _)⟩⟩

/-- A simple object is completely reducible: it is the coproduct of the
one-member family consisting of itself. -/
theorem of_simple (X : C) [Simple X] : IsCompletelyReducible.{w} X :=
  ⟨PUnit, fun _ => X, fun _ => 𝟙 X, fun _ => inferInstance,
    ⟨Cofan.IsColimit.mk _ (fun s => s.inj PUnit.unit) (fun _ _ => by simp)
      (fun _ m hm => by simpa using hm PUnit.unit)⟩⟩

end IsCompletelyReducible

/-- A zero object is semisimple. -/
theorem IsSemisimpleObject.of_isZero {X : C} (hX : IsZero X) : IsSemisimpleObject X :=
  IsCompletelyReducible.of_isZero hX

/-- Semisimplicity is invariant under isomorphism. -/
theorem IsSemisimpleObject.of_iso {X Y : C} (e : X ≅ Y) (h : IsSemisimpleObject X) :
    IsSemisimpleObject Y :=
  IsCompletelyReducible.of_iso e h

/-- A zero object satisfies condition (ii): it has no simple subobject, and its
`⊤` subobject is the least subobject. -/
theorem IsSumOfSimpleSubobjects.of_isZero {X : C} (hX : IsZero X) :
    IsSumOfSimpleSubobjects X :=
  ⟨fun _ _ => le_top, fun _ _ =>
    Subobject.le_of_comm 0 ((hX.of_mono (⊤ : Subobject X).arrow).eq_of_src _ _)⟩

/-- A zero object satisfies condition (iii). -/
theorem EverySubobjectHasComplement.of_isZero {X : C} (hX : IsZero X) :
    EverySubobjectHasComplement X := by
  intro P
  refine ⟨⊥, ?_⟩
  have hP : IsZero (P : C) := hX.of_mono P.arrow
  have hQ : IsZero ((⊥ : Subobject X) : C) := hX.of_mono (⊥ : Subobject X).arrow
  have hPQ : IsZero ((P : C) ⨿ ((⊥ : Subobject X) : C)) := by
    rw [IsZero.iff_id_eq_zero]
    ext
    · exact hP.eq_of_src _ _
    · exact hQ.eq_of_src _ _
  exact ⟨hX.to_ _, hPQ.eq_of_src _ _, hX.eq_of_src _ _⟩

end Langlands.Renard
