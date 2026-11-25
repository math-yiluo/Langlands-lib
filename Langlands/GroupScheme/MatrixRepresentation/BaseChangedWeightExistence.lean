import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
import Langlands.GroupScheme.MatrixRepresentation.ScalarExtensionCoordinates
import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition
import Langlands.GroupScheme.Lie.ConjugationSemisimple
import Langlands.GroupScheme.Rational.AffineCharacterFiniteGaloisValues
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof

/-! # Every geometric character occurs in an original finite representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- An absent character has zero coefficient projector whenever character spaces span. -/
theorem characterProjector_eq_zero_of_not_weight (ρ : MatrixRepresentation G n)
    (hspan : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤)
    (χ : rationalCharacters G) (hχ : ρ.characterSpace χ = ⊥) :
    ρ.characterProjector χ = 0 := by
  have hle : (⨆ ψ : rationalCharacters G, ρ.characterSpace ψ) ≤
      LinearMap.ker (ρ.characterProjector χ) := by
    apply iSup_le
    intro ψ v hv
    change ρ.characterProjector χ v = 0
    rw [characterProjector_of_mem ρ χ ψ hv]
    by_cases heq : ψ = χ
    · subst ψ
      have hv0 : v = 0 := by simpa only [hχ, Submodule.mem_bot] using hv
      simp only [ite_true, hv0]
    · simp only [heq, ite_false]
  rw [hspan] at hle
  exact LinearMap.ker_eq_top.mp (top_unique hle)

/-- An absent character's selected functional vanishes on every universal matrix entry. -/
theorem characterCoefficient_matrix_eq_zero_of_not_weight (ρ : MatrixRepresentation G n)
    (hspan : (⨆ χ : rationalCharacters G, ρ.characterSpace χ) = ⊤)
    (χ : rationalCharacters G) (hχ : ρ.characterSpace χ = ⊥) :
    ρ.universalCharacterMatrix.map (characterCoefficient χ) = 0 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  funext i
  have h := congrArg (fun f : (n → k) →ₗ[k] (n → k) => f v i)
    (characterProjector_eq_zero_of_not_weight ρ hspan χ hχ)
  simp only [map_zero, LinearMap.zero_apply, Pi.zero_apply]
  change (AffineCoefficients.coefficientMap ρ (characterCoefficient χ) *ᵥ v) i = 0
  rw [AffineCoefficients.coefficientMap_mulVec]
  exact h

section BaseChange

open AffineCharacterFiniteGalois Langlands.Plancherel.TorusNormKernel

private local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K)))

local notation "G₁" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (S : Type u) [CommRing S] [Algebra K S] [Algebra k S] [IsScalarTower k K S]

omit [IsAffineHom G.X.hom] in
/-- The two published all-algebra base-change point comparisons agree. -/
theorem pointE_eq_scalarExtensionPoint
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    pointE k K S G x = scalarExtensionPoint S x := by
  apply (baseChangePointsEquiv (algebraBaseMap k K) G _).injective
  rw [baseChangePointsEquiv_pointE, scalarExtensionPoint, MulEquiv.apply_symm_apply]
  rfl

omit [IsAffineHom G.X.hom] in
/-- A scalar-extended representation evaluated at `pointE` has the original matrix. -/
theorem affineMatrix_pointE (ρ : MatrixRepresentation G n)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    (ρ.baseChange (algebraBaseMap k K)).affineMatrix (CommAlgCat.of K S)
        (pointE k K S G x) =
      ρ.affineMatrix (CommAlgCat.of k S) x := by
  rw [pointE_eq_scalarExtensionPoint, affineMatrix_scalarExtensionPoint]

/-- Original universal coefficients evaluate to the matrix at the extended point. -/
theorem universalCharacterMatrix_map_pointE (ρ : MatrixRepresentation G n)
    (x : G.affinePoints (CommAlgCat.of (CommRingCat.of k) S)) :
    ρ.universalCharacterMatrix.map (Lie.pointCoordinates G x) =
      ((ρ.baseChange (algebraBaseMap k K)).affineMatrix (CommAlgCat.of K S)
        (pointE k K S G x) : Matrix n n S) := by
  calc
    _ = (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) S) x : Matrix n n S) :=
      AffineCoefficients.universalCharacterMatrix_map ρ
        (CommAlgCat.of (CommRingCat.of k) S) x
    _ = _ := congrArg (fun M : GL n S => (M : Matrix n n S))
      (affineMatrix_pointE (k := k) (K := K) S ρ x).symm

variable {S}

/-- The selected character coefficient on the universal scalar-extended coordinate algebra. -/
def tensorCharacterCoefficient (χ : rationalCharacters G₁) :
    K ⊗[k] CharacterUnits.Coord G →ₗ[K] K :=
  let C := CharacterUnits.Coord G₁
  letI : Algebra k C := Algebra.compHom C (algebraMap k K)
  letI : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq' rfl
  let y := (pointE k K C G).symm (CharacterUnits.universalPoint G₁)
  (characterCoefficient χ).comp (tensorEval G K C y).toLinearMap

/-- If all original finite representations split into character spaces over `K`,
every character over `K` occurs in the scalar extension of some original representation. -/
theorem exists_weight_baseChange_of_characterSpan
    (hspan : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      (⨆ ψ : rationalCharacters G₁,
        (ρ.baseChange (algebraBaseMap k K)).characterSpace ψ) = ⊤)
    (χ : rationalCharacters G₁) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
  classical
  by_contra h
  push Not at h
  let C := CharacterUnits.Coord G₁
  let : Algebra k C := Algebra.compHom C (algebraMap k K)
  let : IsScalarTower k K C := IsScalarTower.of_algebraMap_eq' rfl
  let y : G.affinePoints (CommAlgCat.of k C) :=
    (pointE k K C G).symm (CharacterUnits.universalPoint G₁)
  let E : K ⊗[k] CharacterUnits.Coord G →ₐ[K] C := tensorEval G K C y
  let L : K ⊗[k] CharacterUnits.Coord G →ₗ[K] K := tensorCharacterCoefficient χ
  have hunit : L (tensorValue G K χ : K ⊗[k] CharacterUnits.Coord G) = 1 := by
    have he := congrArg Units.val (tensorValue_eval G K C χ y)
    change E (tensorValue G K χ) =
      (Gm.affineUnitsEquiv (CommRingCat.of K) (CommAlgCat.of K C)
        (pointE k K C G y ≫ χ.toMul.hom.hom) : C) at he
    have hy : pointE k K C G y = CharacterUnits.universalPoint G₁ :=
      (pointE k K C G).apply_symm_apply _
    rw [hy] at he
    change E (tensorValue G K χ) = (CharacterUnits.unit χ : C) at he
    change characterCoefficient χ (E (tensorValue G K χ)) = 1
    rw [he, characterCoefficient_unit]
    simp only [ite_true]
  have hcoeff (N : ℕ) (ρ : MatrixRepresentation G (Fin N)) (i j : Fin N) :
      L (1 ⊗ₜ[k] ρ.universalCharacterMatrix i j) = 0 := by
    have hzero := characterCoefficient_matrix_eq_zero_of_not_weight
      (ρ.baseChange (algebraBaseMap k K)) (hspan N ρ) χ (h N ρ)
    have hy : pointE k K C G y = CharacterUnits.universalPoint G₁ :=
      (pointE k K C G).apply_symm_apply _
    have hmat := universalCharacterMatrix_map_pointE (k := k) (K := K) C ρ y
    rw [hy] at hmat
    have hentry := congrFun (congrFun hmat i) j
    change Lie.pointCoordinates G y (ρ.universalCharacterMatrix i j) =
      (ρ.baseChange (algebraBaseMap k K)).universalCharacterMatrix i j at hentry
    have he : E (1 ⊗ₜ[k] ρ.universalCharacterMatrix i j) =
        (ρ.baseChange (algebraBaseMap k K)).universalCharacterMatrix i j := by
      simpa only [E, tensorEval, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
        map_one, one_mul] using hentry
    change characterCoefficient χ (E (1 ⊗ₜ[k] ρ.universalCharacterMatrix i j)) = 0
    rw [he]
    exact congrFun (congrFun hzero i) j
  have hright (a : CharacterUnits.Coord G) : L (1 ⊗ₜ[k] a) = 0 := by
    let f : CharacterUnits.Coord G →ₗ[k] K :=
      (L.restrictScalars k).comp
        (Algebra.TensorProduct.includeRight :
          CharacterUnits.Coord G →ₐ[k] K ⊗[k] CharacterUnits.Coord G).toLinearMap
    obtain ⟨N, ρ, ha⟩ := Lie.exists_representation_coefficient_span G a
    have hle : Submodule.span k
        (Set.range fun p : Fin N × Fin N => Lie.representationCoefficients G ρ p.1 p.2) ≤
          LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact hcoeff N ρ i j
    exact hle ha
  have hzero (z : K ⊗[k] CharacterUnits.Coord G) : L z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul c a =>
      have he : c ⊗ₜ[k] a = c • (1 ⊗ₜ[k] a : K ⊗[k] CharacterUnits.Coord G) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, map_smul, hright, smul_zero]
    | add x z hx hz => rw [map_add, hx, hz, add_zero]
  exact one_ne_zero (hunit.symm.trans (hzero _))

/-- Every character over a separable closure is a weight of some original finite
representation of a group of multiplicative type. -/
theorem exists_weight_baseChange_of_isMultiplicativeType
    [IsSepClosure k K] (hG : IsMultiplicativeType G) (χ : rationalCharacters G₁) :
    ∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      (ρ.baseChange (algebraBaseMap k K)).characterSpace χ ≠ ⊥ := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  have hGK := MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
    k K G hG
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed _ hGK
  let := hΛ
  let := hfg
  apply exists_weight_baseChange_of_characterSpan (G := G)
  intro N ρ
  exact iSup_characterSpace_eq_top_of_diagonalizable_iso Λ e _

end BaseChange

end Langlands.GroupScheme.MatrixRepresentation
