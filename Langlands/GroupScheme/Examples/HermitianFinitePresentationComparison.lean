import Langlands.GroupScheme.Examples.HermitianRectangularModelComparison
import Langlands.GroupScheme.Examples.HermitianRootIsometryGroupScheme

/-! # Finite-source Hermitian presentations identify the actual scheme model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Extend a rectangular coordinate matrix to actual test-scheme coefficients. -/
def tensorRectangularMatrix {α β : Type} (M : Matrix α β L)
    (T : Over (Spec (CommRingCat.of k))) :
    Matrix α β (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  M.map (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T))

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Constant rectangular coordinates commute with every test restriction. -/
theorem tensorRectangularMatrix_map {α β : Type} (M : Matrix α β L)
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) :
    (tensorRectangularMatrix k L M T).map (SpecialLinear.WeilRoot.tensorMap k L a) =
      tensorRectangularMatrix k L M T' := by
  ext i j
  change QuasiSplitUnitary.tensorCoefficientMap
    ((algΓ (CommRingCat.of k)).map a).unop.hom
    (M i j ⊗ₜ[k] (1 : SpecialLinear.WeilRoot.sectionAlgebra k T)) = M i j ⊗ₜ[k] 1
  rw [QuasiSplitUnitary.tensorCoefficientMap_tmul, map_one]

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Both coordinate inverse identities extend to each test ring. -/
theorem tensorRectangularMatrix_mul {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] (P : Matrix α β L) (Q : Matrix β α L) (hPQ : P * Q = 1)
    (T : Over (Spec (CommRingCat.of k))) :
    tensorRectangularMatrix k L P T * tensorRectangularMatrix k L Q T = 1 := by
  change P.map _ * Q.map _ = _
  rw [← Matrix.map_mul, hPQ, Matrix.map_one] <;> simp

variable {Source Middle : Type} [Fintype Source] [DecidableEq Source]
  [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (J : Matrix Source Source L) (P : Matrix (Index Middle) Source L)
  (Q : Matrix Source (Index Middle) L)
  (hPQ : P * Q = 1) (hQP : Q * P = 1)
  (hP : (P.map (fieldInvolution k L).bar).transpose * gram H * P = J)

include hP in
omit [Fintype Source] [DecidableEq Source] in
/-- The supplied full Gram congruence extends to the actual tensor form. -/
theorem tensorRectangularGramCongruence (T : Over (Spec (CommRingCat.of k))) :
    ((tensorRectangularMatrix k L P T).map
        (SU3Root.SchemeModel.coefficientInvolution k L T).bar).transpose *
      gram (tensorForm k L H T) * tensorRectangularMatrix k L P T =
        tensorRectangularMatrix k L J T := by
  let f := algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)
  have hb : ((P.map f).map (SU3Root.SchemeModel.coefficientInvolution k L T).bar).transpose =
      ((P.map (fieldInvolution k L).bar).transpose).map f := by
    ext i j
    exact (tensorInclusion_bar k L T (P j i)).symm
  change ((P.map f).map _).transpose * gram (tensorForm k L H T) * P.map f = J.map f
  rw [hb, gram_map f (fun _ => rfl), ← Matrix.map_mul, ← Matrix.map_mul, hP]

/-- Rectangular coordinate conjugation on each actual tensor general-linear group. -/
def tensorRectangularConjugation (T : Over (Spec (CommRingCat.of k))) :
    Matrix.GeneralLinearGroup Source (SpecialLinear.WeilRoot.tensorAlgebra k L T) ≃*
      Matrix.GeneralLinearGroup (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T) :=
  rectangularConjugation (tensorRectangularMatrix k L P T)
    (tensorRectangularMatrix k L Q T)
    (tensorRectangularMatrix_mul k L P Q hPQ T)
    (tensorRectangularMatrix_mul k L Q P hQP T)

include hP in
/-- Membership in the actual tensor special unitary subgroup is the raw equation. -/
theorem tensorRectangularConjugation_mem_iff (T : Over (Spec (CommRingCat.of k)))
    (g : Matrix.GeneralLinearGroup Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)) :
    tensorRectangularConjugation k L P Q hPQ hQP T g ∈
      specialUnitarySubgroup (tensorForm k L H T) ↔
      ((g : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SU3Root.SchemeModel.coefficientInvolution k L T).bar).transpose *
          tensorRectangularMatrix k L J T *
          (g : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
            tensorRectangularMatrix k L J T ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  rw [mem_specialUnitarySubgroup]
  unfold PreservesForm conjugateTranspose tensorRectangularConjugation
  rw [rectangularConjugation_preserves_iff _ _ _ _ _ _ _
    (tensorRectangularGramCongruence k L H J P hP T), rectangularConjugation_det]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
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

/-- The raw presentation, in genuine coordinates, lands in the actual unitary group. -/
def finitePresentationHom (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ G.X) →* specialUnitarySubgroup (tensorForm k L H T) where
  toFun x := ⟨tensorRectangularConjugation k L P Q hPQ hQP T (ρ T x),
    (tensorRectangularConjugation_mem_iff k L H J P Q hPQ hQP hP T _).mpr
      ((hrange T _).mp ⟨x, rfl⟩)⟩
  map_one' := by
    apply Subtype.ext
    change tensorRectangularConjugation k L P Q hPQ hQP T (ρ T 1) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    apply Subtype.ext
    change tensorRectangularConjugation k L P Q hPQ hQP T (ρ T (x * y)) =
      tensorRectangularConjugation k L P Q hPQ hQP T (ρ T x) *
        tensorRectangularConjugation k L P Q hPQ hQP T (ρ T y)
    rw [map_mul, map_mul]

/-- Faithfulness and the exact range turn the coordinate presentation into an equivalence. -/
def finitePresentationEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ G.X) ≃* specialUnitarySubgroup (tensorForm k L H T) :=
  MulEquiv.ofBijective (finitePresentationHom k L H J P Q hPQ hQP hP ρ hrange T) (by
    constructor
    · intro x y hxy
      apply hinj T
      apply (tensorRectangularConjugation k L P Q hPQ hQP T).injective
      exact congrArg Subtype.val hxy
    · intro g
      let e := tensorRectangularConjugation k L P Q hPQ hQP T
      let z := e.symm g.val
      have hz := (tensorRectangularConjugation_mem_iff k L H J P Q hPQ hQP hP T z).mp
        (by change e z ∈ specialUnitarySubgroup (tensorForm k L H T)
            simpa only [z, MulEquiv.apply_symm_apply] using g.property)
      obtain ⟨x, hx⟩ := (hrange T z).mpr hz
      refine ⟨x, Subtype.ext ?_⟩
      change e (ρ T x) = g.val
      rw [hx]
      exact e.apply_symm_apply g.val)

/-- The coordinate presentation keeps its explicit matrix value. -/
@[simp] theorem finitePresentationEquiv_val (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ G.X) :
    ((finitePresentationEquiv k L H J P Q hPQ hQP hP ρ hinj hrange T x).val :
      Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
      tensorRectangularMatrix k L P T *
        (ρ T x : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)) *
        tensorRectangularMatrix k L Q T := rfl

variable (hnat : ∀ {T T' : Over (Spec (CommRingCat.of k))}
  (a : T' ⟶ T) (x : T ⟶ G.X),
  (ρ T' (a ≫ x) : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
    (ρ T x : Matrix Source Source (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
      (SpecialLinear.WeilRoot.tensorMap k L a))

include hnat in
/-- The full matrix comparison is natural on every test scheme. -/
theorem finitePresentationEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T) (x : T ⟶ G.X) :
    ((finitePresentationEquiv k L H J P Q hPQ hQP hP ρ hinj hrange T' (a ≫ x)).val :
      Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (((finitePresentationEquiv k L H J P Q hPQ hQP hP ρ hinj hrange T x).val :
        Matrix (Index Middle) (Index Middle) (SpecialLinear.WeilRoot.tensorAlgebra k L T))).map
          (SpecialLinear.WeilRoot.tensorMap k L a) := by
  simp only [finitePresentationEquiv_val, Matrix.map_mul,
    tensorRectangularMatrix_map, hnat]

variable (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- A faithful natural finite-source presentation and full Gram coordinates identify
an actual group scheme with the supplied Hermitian equalizer model. -/
def isoOfFinitePresentation : G ≅ groupScheme k L H w hw :=
  isoOfMatrixPoints k L H w hw
    (finitePresentationEquiv k L H J P Q hPQ hQP hP ρ hinj hrange)
    (finitePresentationEquiv_naturality k L H J P Q hPQ hQP hP ρ hinj hrange hnat)

end Langlands.GroupScheme.HermitianRoot.SchemeModel
