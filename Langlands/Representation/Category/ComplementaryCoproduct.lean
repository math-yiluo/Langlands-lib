import Langlands.Representation.Category.Subquotients
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.LinearAlgebra.Projection

/-!
# Actual coproducts of complementary invariant subspaces

This internal algebraic construction turns a supplied invariant direct-sum
splitting into its actual smooth-representation coproduct universal property.
It makes no representation-theoretic existence assertion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] [TopologicalSpace G]

/-- The actual complementary subrepresentations, with `S` indexed by `true`. -/
def complementaryComponents (A : SmoothRep.{uR, uG, uV} R G)
    (S Q : Subrepresentation A.representation) : Bool → SmoothRep.{uR, uG, uV} R G
  | false => subrepresentation A Q
  | true => subrepresentation A S

/-- The literal inclusions of two invariant subspaces into their ambient object. -/
def complementaryCofan (A : SmoothRep.{uR, uG, uV} R G)
    (S Q : Subrepresentation A.representation) : Cofan (complementaryComponents A S Q) :=
  Cofan.mk A (fun b => match b with
    | false => subtype A Q
    | true => subtype A S)

set_option backward.isDefEq.respectTransparency.types false in
/-- Extend actual smooth morphisms from complementary invariant subspaces by
adding their values on the unique two components of an ambient vector. -/
def complementaryDesc {A B : SmoothRep.{uR, uG, uV} R G}
    {S Q : Subrepresentation A.representation}
    (h : IsCompl S.toSubmodule Q.toSubmodule)
    (f : subrepresentation A S ⟶ B) (k : subrepresentation A Q ⟶ B) : A ⟶ B :=
  ofHom {
    toLinearMap := LinearMap.ofIsCompl h (hom f).toLinearMap (hom k).toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      obtain ⟨s, q, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h v
      let L := LinearMap.ofIsCompl h (hom f).toLinearMap (hom k).toLinearMap
      have hs : L (A.representation g s.val) =
          hom f ((subrepresentation A S).representation g s) :=
        LinearMap.ofIsCompl_apply_left h
          (u := ⟨_, S.apply_mem_toSubmodule g s.property⟩)
      have hq : L (A.representation g q.val) =
          hom k ((subrepresentation A Q).representation g q) :=
        LinearMap.ofIsCompl_apply_right h
          (v := ⟨_, Q.apply_mem_toSubmodule g q.property⟩)
      change L (A.representation g (s.val + q.val)) =
        B.representation g (L (s.val + q.val))
      rw [map_add, map_add, hs, hq]
      dsimp only [L]
      rw [map_add, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right,
        map_add]
      rw [Representation.IntertwiningMap.isIntertwining _ _ (hom f),
        Representation.IntertwiningMap.isIntertwining _ _ (hom k)]
      rfl }

/-- The extended morphism restricts to the supplied morphism on `S`. -/
@[simp]
theorem subtype_complementaryDesc_left {A B : SmoothRep.{uR, uG, uV} R G}
    {S Q : Subrepresentation A.representation}
    (h : IsCompl S.toSubmodule Q.toSubmodule)
    (f : subrepresentation A S ⟶ B) (k : subrepresentation A Q ⟶ B) :
    subtype A S ≫ complementaryDesc h f k = f := by
  ext v
  exact LinearMap.ofIsCompl_apply_left h v

/-- The extended morphism restricts to the supplied morphism on `Q`. -/
@[simp]
theorem subtype_complementaryDesc_right {A B : SmoothRep.{uR, uG, uV} R G}
    {S Q : Subrepresentation A.representation}
    (h : IsCompl S.toSubmodule Q.toSubmodule)
    (f : subrepresentation A S ⟶ B) (k : subrepresentation A Q ⟶ B) :
    subtype A Q ≫ complementaryDesc h f k = k := by
  ext v
  exact LinearMap.ofIsCompl_apply_right h v

set_option backward.isDefEq.respectTransparency.types false in
/-- Complementarity gives the actual coproduct cofan of the supplied subspaces. -/
def complementaryCofanIsColimit (A : SmoothRep.{uR, uG, uV} R G)
    (S Q : Subrepresentation A.representation)
    (h : IsCompl S.toSubmodule Q.toSubmodule) : IsColimit (complementaryCofan A S Q) := by
  refine Cofan.IsColimit.mk _ (fun t => complementaryDesc h (t.inj true) (t.inj false)) ?_ ?_
  · intro t b
    cases b
    · exact subtype_complementaryDesc_right h _ _
    · exact subtype_complementaryDesc_left h _ _
  · intro t m hm
    change A ⟶ t.pt at m
    ext v
    obtain ⟨s, q, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h v
    have hs := congrArg (fun f => hom f s) (hm true)
    have hq := congrArg (fun f => hom f q) (hm false)
    change hom m s.val = hom (t.inj true) s at hs
    change hom m q.val = hom (t.inj false) q at hq
    change hom m (s.val + q.val) =
      LinearMap.ofIsCompl h (hom (t.inj true)).toLinearMap
        (hom (t.inj false)).toLinearMap (s.val + q.val)
    rw [map_add, map_add, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right,
      hs, hq]
    rfl

/-- Any supplied complementary invariant subspaces in the prescribed factors
provide an actual Bool-indexed component coproduct of the ambient object. -/
theorem isCoproductOfComponents_of_isCompl
    (P : Bool → ObjectProperty (SmoothRep.{uR, uG, uV} R G))
    (A : SmoothRep.{uR, uG, uV} R G) (S Q : Subrepresentation A.representation)
    (h : IsCompl S.toSubmodule Q.toSubmodule)
    (hS : P true (subrepresentation A S)) (hQ : P false (subrepresentation A Q)) :
    Renard.IsCoproductOfComponents P A := by
  refine ⟨complementaryComponents A S Q, (complementaryCofan A S Q).inj, ?_,
    ⟨complementaryCofanIsColimit A S Q h⟩⟩
  intro b
  cases b
  · exact hQ
  · exact hS

end Langlands.SmoothRep
