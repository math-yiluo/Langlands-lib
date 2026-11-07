import Langlands.Representation.Category.CoproductCompression
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Logic.Small.Basic

/-! # The size of nonzero summands in an actual smooth coproduct -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uG uV uI uC vC

namespace Langlands

namespace Cofan

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
  {I : Type uI} {A : I → C}

/-- Restrict a cofan to a subtype of its indices, with its vertex unchanged. -/
def restrictIndices (s : Limits.Cofan A) (p : I → Prop) :
    Limits.Cofan (fun i : {i // p i} => A i.val) :=
  Limits.Cofan.mk s.pt (fun i => s.inj i.val)

/-- Removing zero objects from a coproduct cofan retains its colimit property. -/
def restrictIndicesIsColimit (s : Limits.Cofan A) (hs : IsColimit s)
    (p : I → Prop) (hzero : ∀ i, ¬ p i → IsZero (A i)) :
    IsColimit (restrictIndices s p) := by
  classical
  let extend (t : Limits.Cofan (fun i : {i // p i} => A i.val)) :
      Limits.Cofan A :=
    Limits.Cofan.mk t.pt (fun i => if hi : p i then t.inj ⟨i, hi⟩ else 0)
  refine Limits.Cofan.IsColimit.mk _ (fun t => hs.desc (extend t)) ?_ ?_
  · intro t i
    change s.inj i.val ≫ hs.desc (extend t) = t.inj i
    have hfac := hs.fac (extend t) ⟨i.val⟩
    change s.inj i.val ≫ hs.desc (extend t) = (extend t).inj i.val at hfac
    exact hfac.trans (by simp [extend, i.property])
  · intro t m hm
    apply hs.hom_ext
    rintro ⟨i⟩
    by_cases hi : p i
    · have h := hm ⟨i, hi⟩
      change s.inj i ≫ m = t.inj ⟨i, hi⟩ at h
      have hfac := hs.fac (extend t) ⟨i⟩
      change s.inj i ≫ hs.desc (extend t) = (extend t).inj i at hfac
      have ht : (extend t).inj i = t.inj ⟨i, hi⟩ := by simp [extend, hi]
      change s.inj i ≫ m = s.inj i ≫ hs.desc (extend t)
      exact h.trans (ht.symm.trans hfac.symm)
    · exact (hzero i hi).eq_of_src _ _

/-- Adding zero objects to a colimiting restricted cofan retains the colimit. -/
def isColimitOfRestrictIndices (s : Limits.Cofan A) (p : I → Prop)
    (hzero : ∀ i, ¬ p i → IsZero (A i))
    (hs : IsColimit (restrictIndices s p)) : IsColimit s := by
  refine Limits.Cofan.IsColimit.mk _ (fun t => hs.desc (restrictIndices t p)) ?_ ?_
  · intro t i
    classical
    by_cases hi : p i
    · exact hs.fac (restrictIndices t p) ⟨⟨i, hi⟩⟩
    · exact (hzero i hi).eq_of_src _ _
  · intro t m hm
    apply hs.hom_ext
    rintro ⟨i⟩
    exact (hm i.val).trans (hs.fac (restrictIndices t p) ⟨i⟩).symm

end Cofan

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI}

/-- A smooth representation is a zero object exactly when its carrier is
subsingleton. -/
theorem isZero_iff_subsingleton (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsZero A ↔ Subsingleton A := by
  constructor
  · intro hA
    have hz (x : A) : x = 0 :=
      congrArg (fun f : A ⟶ A => hom f x) (hA.eq_of_src (𝟙 A) 0)
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro hA
    let := hA
    rw [IsZero.iff_id_eq_zero]
    apply ObjectProperty.hom_ext
    ext x
    exact Subsingleton.elim _ _

/-- In an actual smooth coproduct, the nonzero summands have an index type
that fits in the vertex's carrier universe, regardless of the original index
universe. -/
theorem nonzeroSummandIndex_small
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Limits.Cofan A) (hs : IsColimit s) :
    Small.{uV} {i : I // Nontrivial (A i)} := by
  classical
  have hex (i : {i : I // Nontrivial (A i)}) : ∃ x : A i.val, x ≠ 0 := by
    let := i.property
    exact exists_ne 0
  choose v hv using hex
  apply small_of_injective (f := fun i : {i : I // Nontrivial (A i)} =>
    cofanDirectSumMap A s (DirectSum.lof ℂ I (fun i => A i) i.val (v i)))
  intro i j hij
  by_contra hne
  have hji : j.val ≠ i.val := fun h => hne (Subtype.ext h.symm)
  have hsum := cofanDirectSumMap_injective A s hs hij
  have hcomponent := congrArg (fun z => DirectSum.component ℂ I (fun i => A i) i.val z) hsum
  rw [DirectSum.component.lof_self, DirectSum.component.of, dite_eq_right hji] at hcomponent
  exact hv i hcomponent

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]

/-- A zero-preserving functor that preserves carrier-sized coproducts
preserves any supplied actual smooth coproduct cofan, even at a larger index
universe. -/
def mapCofanIsColimit_of_carrierCoproducts
    (T : SmoothRep.{0, uG, uV} ℂ G ⥤ C) [T.PreservesZeroMorphisms]
    (hcop : ∀ J : Type uV, PreservesColimitsOfShape (Discrete J) T)
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Limits.Cofan A) (hs : IsColimit s) :
    IsColimit (Limits.Cofan.mk (T.obj s.pt) (fun i => T.map (s.inj i)) :
      Limits.Cofan (fun i => T.obj (A i))) := by
  classical
  let N := {i : I // Nontrivial (A i)}
  let : Small.{uV} N := nonzeroSummandIndex_small A s hs
  let : PreservesColimitsOfShape (Discrete (Shrink.{uV} N)) T := hcop _
  let : PreservesColimitsOfShape (Discrete N) T :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink N).symm) T
  have hzero (i : I) (hi : ¬ Nontrivial (A i)) : IsZero (A i) :=
    (isZero_iff_subsingleton (A i)).mpr (not_nontrivial_iff_subsingleton.mp hi)
  apply Cofan.isColimitOfRestrictIndices _ (fun i => Nontrivial (A i))
    (fun i hi => T.map_isZero (hzero i hi))
  exact isColimitCofanMkObjOfIsColimit T
    (fun i : N => A i.val) (fun i => s.inj i.val)
    (Cofan.restrictIndicesIsColimit s hs (fun i => Nontrivial (A i)) hzero)

end SmoothRep

end Langlands
