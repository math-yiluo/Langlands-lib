import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.FppfProduct

/-! # Pseudo-parabolic subgroups of actual group schemes

For a smooth connected affine group over a field, a pseudo-parabolic subgroup is
a represented fppf-local product of a dynamic parabolic and a ground-field
unipotent radical. No existence or quotient theorem is asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- A pseudo-parabolic subgroup of a smooth connected affine group is the
represented fppf-local product `P_G(χ) R_{u,k}(G)` for some actual cocharacter.
The radical is over the ground field, without a splitness requirement. -/
structure IsPseudoParabolicSubgroup (i : P ⟶ G) : Prop where
  smooth : Smooth G.X.hom
  connectedSpace : ConnectedSpace G.X.left
  isAffineHom : IsAffineHom G.X.hom
  presentation :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G)
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
      IsUnipotentRadical j ∧
        (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range j) i

namespace IsPseudoParabolicSubgroup

variable {i : P ⟶ G}

/-- Closedness follows from the represented product condition. -/
theorem isClosedSubgroup (hi : IsPseudoParabolicSubgroup i) : IsClosedSubgroup i := by
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  exact hprod.isClosedSubgroup

/-- Any supplied representative of the ground-field radical may be used in a
pseudo-parabolic product presentation, by equality of radical images. -/
theorem exists_cocharacter_product (hi : IsPseudoParabolicSubgroup i)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : IsUnipotentRadical j) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (Dynamic.parabolic χ).IsFppfProduct (SubgroupFunctor.range j) i := by
  obtain ⟨V, l, χ, hl, hprod⟩ := hi.presentation
  exact ⟨χ, by simpa only [hl.range_eq hj] using hprod⟩

/-- Every represented ground-field radical is contained in a pseudo-parabolic
subgroup on all relative scheme tests. -/
theorem radical_le (hi : IsPseudoParabolicSubgroup i)
    {U : GroupScheme (Spec (CommRingCat.of k))} {j : U ⟶ G}
    (hj : IsUnipotentRadical j) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
  obtain ⟨χ, hprod⟩ := hi.exists_cocharacter_product hj
  exact hprod.right_le

/-- A pseudo-parabolic subgroup contains a dynamic parabolic on all tests for
some actual ground-field cocharacter. -/
theorem exists_cocharacter_le (hi : IsPseudoParabolicSubgroup i) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.parabolic χ ≤ SubgroupFunctor.range i := by
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  exact ⟨χ, hprod.left_le⟩

end IsPseudoParabolicSubgroup

end Langlands.GroupScheme
