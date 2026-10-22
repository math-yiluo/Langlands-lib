import Langlands.Weil.Representation.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
# Invariants of finite-dimensional representations

A normal subgroup acts trivially on its invariant subspace. The ambient group
acts on that actual subspace, and restriction of intertwiners is functorial.
-/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The actual subspace fixed by a specified subgroup. -/
abbrev invariantSubspace (A : FiniteRepresentation K G) (I : Subgroup G) :
    Submodule K A := Representation.invariants (A.representation.comp I.subtype)

/-- For a normal subgroup, the ambient group acts on its fixed subspace. -/
def invariants (I : Subgroup G) [I.Normal] (A : FiniteRepresentation.{uK, uG, uV} K G) :
    FiniteRepresentation.{uK, uG, uV} K G :=
  of (A.representation.toInvariants I)

instance invariants_isTrivial (I : Subgroup G) [I.Normal] (A : FiniteRepresentation K G) :
    Representation.IsTrivial ((invariants I A).representation.comp I.subtype) :=
  inferInstanceAs (Representation.IsTrivial ((A.representation.toInvariants I).comp I.subtype))

/-- Inclusion of the invariant subspace is an actual intertwiner. -/
def invariantsInclusion (I : Subgroup G) [I.Normal] (A : FiniteRepresentation K G) :
    (invariants I A).representation.IntertwiningMap A.representation :=
  ⟨(invariantSubspace A I).subtype, fun _ => rfl⟩

/-- Restrict an intertwiner to the fixed subspaces. -/
def invariantsMap (I : Subgroup G) [I.Normal]
    {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G}
    (f : A.representation.IntertwiningMap B.representation) :
    (invariants I A).representation.IntertwiningMap (invariants I B).representation where
  toLinearMap :=
    (f.toLinearMap.comp (invariantSubspace A I).subtype).codRestrict
      (invariantSubspace B I) fun x i => by
        change B.representation i (f x.val) = f x.val
        rw [← Representation.IntertwiningMap.isIntertwining _ _ f]
        exact congrArg f (x.property i)
  isIntertwining' g := by
    ext x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ f g x.val

/-- Invariants define a functor on finite-dimensional representations. -/
def invariantsFunctor (I : Subgroup G) [I.Normal] :
    FiniteRepresentation.{uK, uG, uV} K G ⥤ FiniteRepresentation.{uK, uG, uV} K G where
  obj := invariants I
  map f := (homEquiv _ _).symm (invariantsMap I (homEquiv _ _ f))
  map_id A := by
    apply (homEquiv _ _).injective
    ext x
    rfl
  map_comp f g := by
    apply (homEquiv _ _).injective
    ext x
    rfl

/-- Normal-subgroup invariants respect genuine representation isomorphisms. -/
def invariantsEquiv (I : Subgroup G) [I.Normal]
    {A B : FiniteRepresentation.{uK, uG, uV} K G} (e : Equiv A B) :
    Equiv (invariants I A) (invariants I B) :=
  equivOfIso ((invariantsFunctor I).mapIso (isoOfEquiv e))

/-- The invariant-space construction descends to genuine isomorphism classes. -/
def invariantsClass (I : Subgroup G) [I.Normal] :
    IsomorphismClasses.{uK, uG, uV} K G → IsomorphismClasses.{uK, uG, uV} K G :=
  Quotient.map (invariants I) (fun _ _ ⟨e⟩ => ⟨invariantsEquiv I e⟩)

end Langlands.FiniteRepresentation
