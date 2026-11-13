import Langlands.GroupScheme.Examples.HermitianRootCocharacter
import Langlands.GroupScheme.CorepresentedAffineComparison
import Mathlib.RingTheory.Flat.Basic

/-! # The diagonal cocharacter of the weighted Hermitian scheme is nontrivial -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root
open SU3Root.SchemeModel (scalarUnit)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

omit [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Test-scheme scalars enter the actual tensor coefficients injectively. -/
theorem includeSections_injective (T : Over (Spec (CommRingCat.of k))) :
    Function.Injective (SpecialLinear.WeilRoot.includeSections k L T) :=
  Algebra.TensorProduct.includeRight_injective (R := k) (A := L)
    (B := SpecialLinear.WeilRoot.sectionAlgebra k T) (algebraMap k L).injective

/-- Over an infinite base field the actual split diagonal cocharacter of the
weighted Hermitian group scheme is not the trivial homomorphism. -/
theorem cocharacter_ne_zero [Infinite k] : cocharacter k L H w hw ≠ 0 := by
  classical
  intro hz
  obtain ⟨c, hc⟩ := ({0, 1} : Finset k).exists_notMem
  have hc' : c ≠ 0 ∧ c ≠ 1 := by simpa using hc
  let S : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) k
  let T := (algSpec (CommRingCat.of k)).obj (op S)
  let R := ((algΓ (CommRingCat.of k)).obj T).unop
  let e : R ≃ₐ[k] k := Corepresented.affineSectionsAlgEquiv S
  let t : Rˣ := Units.map (algebraMap k R).toMonoidHom (Units.mk0 c hc'.1)
  let x := (Gm.pointsEquiv (Spec (CommRingCat.of k)) T).symm t
  have hx : x ≫ (cocharacter k L H w hw).hom.hom = 1 := by
    rw [hz]
    exact MonObj.comp_one x
  have hm := pointsEquiv_cocharacter_val k L H w hw x
  rw [hx, map_one] at hm
  have he := congrArg (fun M : Matrix (Index Middle) (Index Middle)
    (SpecialLinear.WeilRoot.tensorAlgebra k L T) => M (Sum.inl ()) (Sum.inl ())) hm
  have hs : (scalarUnit k L T x : SpecialLinear.WeilRoot.tensorAlgebra k L T) = 1 := by
    simpa [diagonalMatrix, diagonalWeight, Matrix.diagonal_apply_eq] using he.symm
  have ht : SpecialLinear.WeilRoot.includeSections k L T (t : R) =
      SpecialLinear.WeilRoot.includeSections k L T 1 := by
    rw [map_one, ← hs]
    simp only [scalarUnit, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, x,
      MulEquiv.apply_symm_apply, Units.coe_map]
    rfl
  have h1 : (t : R) = 1 := includeSections_injective k L T ht
  have h2 : c = 1 := by
    have := congrArg e h1
    simpa [t] using this
  exact hc'.2 h2

end Langlands.GroupScheme.HermitianRoot.SchemeModel
