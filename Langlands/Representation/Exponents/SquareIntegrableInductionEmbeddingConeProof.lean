import Langlands.Representation.Exponents.SquareIntegrableInductionEmbeddingConeStatement
import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # The scalar cone of an actual induction embedding -/

noncomputable section

namespace Langlands

universe uF uV

/-- Restrict the inducing scalar action to the nonzero actual image of the
first-adjunction map, then apply the scalar Jacquet-subquotient cone theorem. -/
theorem squareIntegrableInductionEmbeddingCone :
    SquareIntegrableInductionEmbeddingConeStatement.{uF,uV} := by
  intro p _ F T
  let := T.topology
  intro n hn π _ hsq B σ ⟨f, hf⟩ χ hscalar x hx
  let := T.generalLinearTopologicalGroup n
  have hf0 : SmoothRep.hom f ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : π)
    apply hv
    apply hf
    rw [h]
    rfl
  let e := Parabolic.FirstAdjointness.equiv T B π.isSmooth (σ := σ.representation)
  have hq0 : e (SmoothRep.hom f) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).mpr hf0
  let g : (T.normalizedJacquetFunctor B).obj π ⟶ σ :=
    SmoothRep.ofHom (e (SmoothRep.hom f))
  let I := SmoothRep.image g
  let q : ((T.normalizedJacquetFunctor B).obj π).representation.IntertwiningMap
      I.representation :=
    { toLinearMap := (SmoothRep.hom g).toLinearMap.rangeRestrict
      isIntertwining' := fun a => by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom g) a v) }
  have hq : Function.Surjective q := by
    rintro ⟨_, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  have hI : Nontrivial I := by
    by_contra h
    have : Subsingleton I := not_nontrivial_iff_subsingleton.mp h
    apply hq0
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact congrArg Subtype.val (Subsingleton.elim (q v) 0)
  let := hI
  have hsub : SmoothRep.IsSubquotient I ((T.normalizedJacquetFunctor B).obj π) :=
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩
  have hscalarI : ∀ (a : Fin B.length → F.Carrierˣ) (v : I),
      I.representation (B.blockScalarLevi F.Carrier a) v = (χ a : ℂ) • v := by
    intro a v
    apply Subtype.ext
    exact hscalar a v.val
  exact @squareIntegrableActualJacquetCone.{uF,max uF uV}
    p _ F T n hn π hsq B I hI hsub χ hscalarI x hx

end Langlands
