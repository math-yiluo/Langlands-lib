import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Completeness

/-! # Banach rings from actual positive-polyradius quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- The actual quotient norm is complete over a complete coefficient field. -/
instance instCompleteSpace (A : PresentedAffinoidAlgebra K) : CompleteSpace A :=
  inferInstanceAs (CompleteSpace (GeneralizedTateAlgebra A.polyradius K ⧸ A.ideal))

open CategoryTheory

/-- Forget the chosen finite presentation, retaining its actual complete quotient
ring and the underlying bounded ring maps. -/
def toBanachRing : PresentedAffinoidAlgebra K ⥤ BanachRing where
  obj A := BanachRing.of A
  map f := f.toBoundedRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (toBanachRing K).Faithful where
  map_injective {A B} f g h := by
    apply BoundedAlgHom.ext
    intro a
    exact congrArg (fun m : BoundedRingHom A B => m a) h

@[simp] theorem toBanachRing_map_apply {A B : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (a : A) :
    ((toBanachRing K).map f : BoundedRingHom A B).toRingHom a = f a := rfl

end PresentedAffinoidAlgebra

open CategoryTheory

/-- The previously constructed normed-algebra spectrum functor is exactly the
Banach spectrum functor after forgetting the chosen presentations. -/
theorem affinoidSpectrumFunctor_eq_toBanachRing :
    affinoidSpectrumFunctor K =
      (PresentedAffinoidAlgebra.toBanachRing K).op ⋙ banachSpectrumFunctor := rfl

end Langlands.Analytic
