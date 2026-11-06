import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Reductive.CommutingMultiplicationFiniteCenters

/-! # Descent of surjective subgroup multiplication -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- Surjectivity of the original subgroup multiplication reflects along any
surjective change of base. -/
theorem surjective_subgroupMultiplication_of_baseChange [Surjective b]
    {H K G : GroupScheme S} (j : H ⟶ G) (i : K ⟶ G)
    (hs : Surjective (subgroupMultiplication ((GroupScheme.baseChange b).map j)
      ((GroupScheme.baseChange b).map i)).left) :
    Surjective (subgroupMultiplication j i).left := by
  let := hs
  let e := subgroupMultiplicationBaseChangeIso b H K
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hs' : Surjective ((Over.pullback b).map (subgroupMultiplication j i)).left := by
    rw [← subgroupMultiplication_baseChange b j i, Over.comp_left]
    exact inferInstanceAs (Surjective (e.hom.left ≫ _))
  exact surjective_overHom_of_baseChange b _ hs'

end Base

section Field

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
    {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- A field extension detects scheme-surjectivity of the original
two-subgroup multiplication. -/
theorem surjective_subgroupMultiplication_of_fieldExtension
    (j : H ⟶ G) (i : K ⟶ G)
    (hs : Surjective (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map i)).left) :
    Surjective (subgroupMultiplication j i).left := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    (fieldExtension_fpqc k E).1
  exact surjective_subgroupMultiplication_of_baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) j i hs

/-- The actual commuting multiplication over the original field, with central
isogeny and semisimple product properties, obtained from scheme-surjectivity
after a field extension. -/
def semisimpleCommutingMultiplicationOfFieldExtension
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hG : IsSemisimple G)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map i)).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    { f : H ⊗ K ⟶ G // IsCentralIsogeny f ∧ IsSemisimple (H ⊗ K) } :=
  semisimpleCommutingMultiplication j i hj hi hG hHs hHc hKs hKc hc
    (surjective_subgroupMultiplication_of_fieldExtension j i hs) hH hK

@[simp]
theorem semisimpleCommutingMultiplicationOfFieldExtension_val
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hG : IsSemisimple G)
    (hHs : Smooth H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hKs : Smooth K.X.hom) (hKc : ConnectedSpace K.X.left)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map j)
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map i)).left)
    (hH : HasFiniteCenter H) (hK : HasFiniteCenter K) :
    (semisimpleCommutingMultiplicationOfFieldExtension
      j i hj hi hG hHs hHc hKs hKc hc hs hH hK).val =
      commutingSubgroupMultiplicationHom j i hc := rfl

end Field

end Langlands.GroupScheme
