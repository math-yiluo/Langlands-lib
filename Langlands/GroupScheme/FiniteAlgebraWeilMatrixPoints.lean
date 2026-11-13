import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.GroupScheme.SpecialLinearWeilPointModels

/-! # Finite matrix algebra units in the Weil tensor convention -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.WeilMatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {N d : ℕ}
  (b : Module.Basis (Fin d) K (Matrix (Fin N) (Fin N) L))

/-- Actual finite-algebra unit points, with the coefficient-field tensor factor first. -/
def tensorMatrixEquiv (T : Over (base K)) :
    (T ⟶ (groupScheme b).X) ≃*
      Matrix.GeneralLinearGroup (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T) :=
  (MatrixPoints.tensorMatrixEquiv K L b T).trans
    (Units.mapEquiv (Algebra.TensorProduct.comm K
      ((algΓ (CommRingCat.of K)).obj T).unop L).mapMatrix.toMulEquiv)

/-- Tensor swap commutes with every actual change of test scheme. -/
theorem tensorMatrixEquiv_naturality {T T' : Over (base K)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme b).X) :
    tensorMatrixEquiv K L b T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map (SpecialLinear.WeilRoot.tensorMap K L a)
        (tensorMatrixEquiv K L b T x) := by
  change Units.mapEquiv _ (MatrixPoints.tensorMatrixEquiv K L b T' (a ≫ x)) = _
  rw [MatrixPoints.tensorMatrixEquiv_naturality]
  apply Units.ext
  ext r c
  change Algebra.TensorProduct.comm K _ L
      (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
        (AlgHom.id K L) ((MatrixPoints.tensorMatrixEquiv K L b T x).val r c)) =
    SpecialLinear.WeilRoot.tensorMap K L a
      (Algebra.TensorProduct.comm K _ L
        ((MatrixPoints.tensorMatrixEquiv K L b T x).val r c))
  induction ((MatrixPoints.tensorMatrixEquiv K L b T x).val r c)
      using TensorProduct.inductionOn with
  | tmul r l => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {K L} {b}
  {G : GroupScheme (base K)}
  (ρ : ∀ T : Over (base K), (T ⟶ G.X) →*
    Matrix.GeneralLinearGroup (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T))

/-- Reinterpret a matrix presentation as actual finite-algebra unit points. -/
def unitPoints (T : Over (base K)) : (T ⟶ G.X) →* (T ⟶ (groupScheme b).X) :=
  (tensorMatrixEquiv K L b T).symm.toMonoidHom.comp (ρ T)

variable (hρ : ∀ {T T' : Over (base K)} (a : T' ⟶ T) (x : T ⟶ G.X),
  (ρ T' (a ≫ x) : Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T')) =
    (ρ T x : Matrix (Fin N) (Fin N) (SpecialLinear.WeilRoot.tensorAlgebra K L T)).map
      (SpecialLinear.WeilRoot.tensorMap K L a))

include hρ in
/-- The reinterpretation remains natural on all test schemes. -/
theorem unitPoints_naturality {T T' : Over (base K)} (a : T' ⟶ T) (x : T ⟶ G.X) :
    unitPoints (b := b) ρ T' (a ≫ x) = a ≫ unitPoints (b := b) ρ T x := by
  apply (tensorMatrixEquiv K L b T').injective
  rw [tensorMatrixEquiv_naturality]
  simp only [unitPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  apply Units.ext
  exact hρ a x

/-- The actual group-scheme morphism supplied by a natural matrix presentation. -/
def hom : G ⟶ groupScheme b :=
  homOfPoints (unitPoints (b := b) ρ)
    (fun {_ _} a x => unitPoints_naturality ρ hρ a x)

/-- The morphism induces exactly the original presentation on every test scheme. -/
theorem tensorMatrixEquiv_hom (T : Over (base K)) (x : T ⟶ G.X) :
    tensorMatrixEquiv K L b T (x ≫ (hom (b := b) ρ hρ).hom.hom) = ρ T x := by
  have h := comp_homOfPoints (unitPoints (b := b) ρ)
    (fun {_ _} a x => unitPoints_naturality ρ hρ a x) T x
  exact (congrArg (tensorMatrixEquiv K L b T) h).trans
    ((tensorMatrixEquiv K L b T).apply_symm_apply _)

/-- An injective matrix presentation gives a monomorphism of relative schemes. -/
theorem mono_hom (hρinj : ∀ T, Function.Injective (ρ T)) :
    Mono (hom (b := b) ρ hρ).hom.hom := by
  constructor
  intro T x y hxy
  apply hρinj T
  have h := congrArg (tensorMatrixEquiv K L b T) hxy
  simpa only [tensorMatrixEquiv_hom] using h

/-- The same morphism is a monomorphism on underlying schemes. -/
theorem mono_hom_left (hρinj : ∀ T, Function.Injective (ρ T)) :
    Mono (hom (b := b) ρ hρ).hom.hom.left := by
  let : Mono (hom (b := b) ρ hρ).hom.hom := mono_hom ρ hρ hρinj
  exact Over.mono_left_of_mono _

end Langlands.GroupScheme.FiniteAlgebraUnits.WeilMatrixPoints
