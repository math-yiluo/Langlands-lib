import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Two maps with the same represented kernel pair identify exactly the same
pairs of morphisms from every scheme over the base. -/
theorem same_kernel_of_common_represented_kernelPair
    {F G : Presheaf S} {R U : Over S} (t s : R ⟶ U)
    (a : (schemeYoneda S).obj U ⟶ F) (b : (schemeYoneda S).obj U ⟶ G)
    (hA : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (hB : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) b b) :
    ∀ (T : Over S) (x y : T ⟶ U),
      a.app (op T) ⟨x⟩ = a.app (op T) ⟨y⟩ ↔
        b.app (op T) ⟨x⟩ = b.app (op T) ⟨y⟩ := by
  intro T x y
  constructor
  · intro hxy
    obtain ⟨z, hzt, hzs⟩ :=
      Types.exists_of_isPullback (hA.app (op T)) ⟨x⟩ ⟨y⟩ hxy
    have h := ConcreteCategory.congr_hom (hB.app (op T)).w z
    change b.app (op T) (((schemeYoneda S).map t).app (op T) z) =
      b.app (op T) (((schemeYoneda S).map s).app (op T) z) at h
    rwa [hzt, hzs] at h
  · intro hxy
    obtain ⟨z, hzt, hzs⟩ :=
      Types.exists_of_isPullback (hB.app (op T)) ⟨x⟩ ⟨y⟩ hxy
    have h := ConcreteCategory.congr_hom (hA.app (op T)).w z
    change a.app (op T) (((schemeYoneda S).map t).app (op T) z) =
      a.app (op T) (((schemeYoneda S).map s).app (op T) z) at h
    rwa [hzt, hzs] at h

end Langlands.AlgebraicGeometry.AlgebraicSpace
