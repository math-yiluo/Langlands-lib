import Langlands.GroupScheme.Examples.HermitianFiniteSourceCoordinates
import Langlands.GroupScheme.Examples.HermitianFinitePresentationComparison

/-! # Actual rank-one Hermitian models from attained matrix presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Concrete data for the Hermitian model with an anisotropic middle of size `n - 1`. -/
def RankOneModel (n : ℕ) (G : GroupScheme (Spec (CommRingCat.of k))) :=
  Σ' (form : DiagonalForm (fieldInvolution k L) (Fin (n - 1)))
    (weights : Fin (n - 1) → Lˣ) (weights_eq : ∀ i, (weights i : L) = form.weight i)
    (_ : form.IsAnisotropic), G ≅ groupScheme k L form weights weights_eq

variable {Source : Type} [Fintype Source] [DecidableEq Source]
  {n : ℕ} (hnpos : 1 ≤ n) (hcard : Fintype.card Source = n + 1)
  (h : (Source → L) →ₗ[L] (Source → L) →ₛₗ[(fieldInvolution k L).bar.toRingHom] L)
  (hbar : ∀ x y, (fieldInvolution k L).bar (h x y) = h y x)
  (J : Matrix Source Source L)
  (hJ : ∀ z t, h z t =
    dotProduct (fun i => (fieldInvolution k L).bar (t i)) (J.mulVec z))
  (hn : h.Nondegenerate)
  (hatt : ∃ W : Submodule L (Source → L),
    (∀ a b : W, h (a : Source → L) (b : Source → L) = 0) ∧
      (Module.finrank L W : ℕ∞) = 1)
  (hbound : ∀ W : Submodule L (Source → L),
    (∀ a b : W, h (a : Source → L) (b : Source → L) = 0) →
      (Module.finrank L W : ℕ∞) ≤ 1)
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ G.X) →* Matrix.GeneralLinearGroup Source
      (SpecialLinear.WeilRoot.tensorAlgebra k L T))
  (hinj : ∀ T, Function.Injective (ρ T))
  (hrange : ∀ (T : Over (Spec (CommRingCat.of k)))
    (g : Matrix.GeneralLinearGroup Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)),
    (∃ x : T ⟶ G.X, ρ T x = g) ↔
      ((g : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SU3Root.SchemeModel.coefficientInvolution k L T).bar).transpose *
          tensorRectangularMatrix k L J T *
          (g : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
            tensorRectangularMatrix k L J T ∧ Matrix.GeneralLinearGroup.det g = 1)
  (hnat : ∀ {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ G.X),
    (ρ T' (a ≫ x) : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (ρ T x : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SpecialLinear.WeilRoot.tensorMap k L a))

include hbar hJ hn hatt hbound hinj hrange hnat hnpos hcard in
/-- An attained maximal isotropic dimension of one and a natural full matrix
presentation give actual rank-one Hermitian model data. -/
theorem nonempty_rankOneModel_of_attained_presentation :
    Nonempty (RankOneModel k L n G) := by
  obtain ⟨H, w, hw, hH, e, _he, hPQ, hQP, hP⟩ :=
    exists_rankOne_finiteSource_gram_coordinates n hnpos hcard h hbar J hJ hn hatt hbound
  exact ⟨⟨H, w, hw, hH,
    isoOfFinitePresentation k L H J (rectangularCoordinateMatrix e)
      (rectangularCoordinateMatrix e.symm) hPQ hQP hP ρ hinj hrange hnat w hw⟩⟩

/-- Choose the actual anisotropic-middle model and its group-scheme isomorphism
from an attained rank-one Hermitian matrix presentation. -/
def rankOneModelOfAttainedPresentation : RankOneModel k L n G :=
  Classical.choice (nonempty_rankOneModel_of_attained_presentation k L
    hnpos hcard h hbar J hJ hn hatt hbound ρ hinj hrange hnat)

end Langlands.GroupScheme.HermitianRoot.SchemeModel
