import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleRelationQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairEtale
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages

/-! # Reduction of the étale quotient theorem to fppf descent

The algebraic-space quotient of an étale equivalence relation exists once separated locally
quasi-finite morphisms locally of finite type satisfy effective fppf descent in sheaf form.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace AlgebraicSpace.RelationQuotient AlgebraicSpace.KernelPair

/-- The slice relation of an étale equivalence relation is an equivalence relation on points. -/
theorem EtaleEquivalenceRelation.isOverEquivRel {S : Scheme.{u}} (E : EtaleEquivalenceRelation.{u})
    (b : E.U ⟶ S) (hb : E.t ≫ b = E.s ≫ b) :
    IsOverEquivRel (U := Over.mk b) (R := Over.mk (E.t ≫ b)) (Over.homMk E.t)
      (Over.homMk E.s hb.symm) where
  ext T r r' h₁ h₂ := by
    have := E.mono_lift
    ext1
    apply (cancel_mono (prod.lift E.t E.s)).1
    apply prod.hom_ext
    · simpa using congrArg CommaMorphism.left h₁
    · simpa using congrArg CommaMorphism.left h₂
  refl T x := by
    obtain ⟨r, h₁, h₂⟩ := E.refl T.left x.left
    refine ⟨Over.homMk r ?_, by ext1; exact h₁, by ext1; exact h₂⟩
    simpa [← Category.assoc, h₁] using Over.w x
  symm T r := by
    obtain ⟨r', h₁, h₂⟩ := E.symm T.left r.left
    refine ⟨Over.homMk r' ?_, by ext1; exact h₁, by ext1; exact h₂⟩
    change r' ≫ E.t ≫ b = T.hom
    rw [← Category.assoc, h₁, Category.assoc, ← hb]
    exact Over.w r
  trans T r r' e := by
    obtain ⟨r'', h₁, h₂⟩ := E.trans T.left r.left r'.left (congrArg CommaMorphism.left e)
    refine ⟨Over.homMk r'' ?_, by ext1; exact h₁, by ext1; exact h₂⟩
    simpa [← Category.assoc, h₁] using Over.w r

/-- Effective fppf descent of separated locally quasi-finite morphisms locally of finite type
gives the algebraic-space quotient of every étale equivalence relation: the fppf sheaf quotient
of the slice relation, with the quotient map from `U`. -/
theorem etaleEquivalenceRelationAlgebraicSpaceQuotient_of
    (hD : FppfSeparatedLocallyQuasiFiniteDescentStatement.{u}) :
    EtaleEquivalenceRelationAlgebraicSpaceQuotientStatement.{u} := by
  intro S E b hb U R t s
  have hE : IsOverEquivRel t s := E.isOverEquivRel b hb
  have h := isPullback_quotientMap hE
  have := E.etale_t
  have := E.etale_s
  have ht : LocallyOfFiniteType t.left := inferInstanceAs (LocallyOfFiniteType E.t)
  have hdiag := hasRepresentableDiagonal_of_isPullback hD (quotientMap t s) h ht
  have he := isEtale_of_isPullback (quotientMap t s) hdiag h (inferInstanceAs (Etale E.s))
  have hsurj := OpenSubfunctorImages.isSurjective_of_isEtale_isLocallySurjective _ he
    inferInstance
  exact ⟨⟨quotientSheaf t s, hdiag, U, quotientMap t s, he, hsurj⟩, quotientMap t s, he, hsurj, h⟩

end Langlands.AlgebraicGeometry
