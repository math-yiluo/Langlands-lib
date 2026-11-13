import Langlands.GroupScheme.Quaternionic.SpinKernelSplitCocharacter
import Langlands.GroupScheme.Quaternionic.SpinKernelOrthogonalReduction

/-! # The spin-kernel comparison from an adapted orthogonal chart -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

open FirstKindInvolution Langlands.CentralSimple

section CoordinateCocharacter

variable (l : Type) [Fintype l] [DecidableEq l] (L : Type u) [Field L] (i₀ : l)

/-- The split-torus cocharacter with coordinate `2eᵢ₀`. -/
def doubleCoordinateCocharacter :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of L)) (ULift l)) :=
  (splitTorus.cocharacterLatticeEquiv L (ULift l)).symm
    (fun c : ULift l => (Pi.single i₀ (2 : ℤ) : l → ℤ) c.down)

@[simp] theorem doubleCoordinateCocharacter_coord :
    GeneralLinear.cocharacterCoordEquiv l L (doubleCoordinateCocharacter l L i₀) =
      Pi.single i₀ 2 := by
  ext j
  exact congrFun ((splitTorus.cocharacterLatticeEquiv L (ULift l)).apply_symm_apply
    (fun c : ULift l => (Pi.single i₀ (2 : ℤ) : l → ℤ) c.down)) (ULift.up j)

/-- On all tests the double coordinate raises the selected unit to its square. -/
theorem doubleCoordinateCocharacter_points (U : Over (Spec (CommRingCat.of L)))
    (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    splitTorus.pointsEquiv (ULift l) U
        (z ≫ (CommGroupScheme.groupHom (doubleCoordinateCocharacter l L i₀)).hom.hom) =
      Pi.mulSingle (ULift.up i₀) ((Gm.pointsEquiv _ U z) ^ 2) := by
  rw [doubleCoordinateCocharacter, splitTorus.pointsEquiv_cocharacterLatticeEquiv_symm]
  ext c
  by_cases hc : c = ULift.up i₀
  · subst c
    simp
  · have hd : c.down ≠ i₀ := fun h => hc (ULift.ext _ _ h)
    simp [hd, hc]

end CoordinateCocharacter

section AdaptedCoordinates

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)
  (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {v w : n → D} (h : σ.IsHyperbolicPair q v w)
  {l : Type} [Fintype l] [DecidableEq l]
  (Φ : (GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q) ≅
    OrthogonalMatrix.groupScheme l (CommRingCat.of L)) (i₀ : l)

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

/-- Full orthogonal coordinates in which the indicated original Levi is the selected
coordinate diagonal whenever its quaternionic chart is `diag(s,1)`. -/
def IsAdaptedOrthogonalCoordinates : Prop :=
  ∀ (U : Over (Spec (CommRingCat.of L)))
    (x : U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj (σ.isometryGroup q)).X)
    (b : (restrictedSections K L U ⊗[K] D)ˣ) (s : (restrictedSections K L U)ˣ),
    chartR e (restrictedSections K L U) (b : restrictedSections K L U ⊗[K] D) =
      !![(s : restrictedSections K L U), 0; 0, 1] →
    HyperbolicScheme.matrixPointsEquiv n ((Over.map (scalarBaseMap K L)).obj U)
        (baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) U x ≫
          (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (restrictedSections K L U)
        (BinaryAction.hyperbolicLevi (σ.baseChange (restrictedSections K L U)) b) →
    (OrthogonalMatrix.pointsEquiv l (CommRingCat.of L) U (x ≫ Φ.hom.hom.hom) :
        Matrix (l ⊕ l) (l ⊕ l) Γ(U.left, ⊤)) =
      (OrthogonalMatrix.leviHom Γ(U.left, ⊤)
        (GeneralLinear.diagonalTorusUnits l Γ(U.left, ⊤)
          (Pi.mulSingle (ULift.up.{u} i₀) s)) : Matrix (l ⊕ l) (l ⊕ l) Γ(U.left, ⊤))

variable [Infinite K]
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})
  (hΦ : IsAdaptedOrthogonalCoordinates e σ h Φ i₀)

include hΦ hdim hsym hπ hsc

/-- The original binary cocharacter projects to the double selected torus coordinate. -/
theorem splitSpinCocharacter_comp_eq_diagonal :
    splitSpinCocharacter e σ hdim hsym h hπ hsc ≫
        (GroupScheme.baseChange (scalarBaseMap K L)).map π ≫ Φ.hom =
      CommGroupScheme.groupHom (doubleCoordinateCocharacter l L i₀) ≫
        OrthogonalMatrix.diagonalTorus l (CommRingCat.of L) := by
  apply hom_ext_points
  intro U z
  apply (OrthogonalMatrix.pointsEquiv l (CommRingCat.of L) U).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [OrthogonalMatrix.pointsEquiv_diagonalTorus, doubleCoordinateCocharacter_points]
  apply Subtype.ext
  apply hΦ U
    ((z ≫ (splitSpinCocharacter e σ hdim hsym h hπ hsc).hom.hom) ≫
      ((GroupScheme.baseChange (scalarBaseMap K L)).map π).hom.hom)
    (normCoverScalarUnits K D (restrictedSections K L U) (Gm.pointsEquiv _ U z) *
      (splitNormOneDiagonal e (restrictedSections K L U) (Gm.pointsEquiv _ U z)).val)
    ((Gm.pointsEquiv _ U z) ^ 2)
  · simpa only [Units.val_pow_eq_pow_val] using
      chartR_scalar_mul_splitNormOneDiagonal e
        (R := restrictedSections K L U) (Gm.pointsEquiv _ U z)
  · exact splitSpinCocharacter_ambient_points e σ hdim hsym h hπ hsc U z

/-- An adapted full orthogonal chart yields kernel generation for every Levi lift pair. -/
theorem kernelGenerator_of_adaptedCoordinates (hl : 3 ≤ Fintype.card l)
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hlift : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      π mu psi :=
  kernelGenerator_of_orthogonalCoordinates σ hdim hsym h hπ hsc hl Φ
    (splitSpinCocharacter e σ hdim hsym h hπ hsc)
    (doubleCoordinateCocharacter l L i₀)
    (splitSpinCocharacter_comp_eq_diagonal e σ h Φ i₀ hdim hsym hπ hsc hΦ)
    i₀ (doubleCoordinateCocharacter_coord l L i₀)
    (splitSpinCocharacter_root e σ hdim hsym h hπ hsc) hlift

end AdaptedCoordinates

end Langlands.GroupScheme.Quaternionic.SpinKernel
