import Langlands.Global.AdelicLocalDensity
import Langlands.Global.LocalModularCharacterAdjointDeterminantStatement
import Langlands.Global.AdelicModularCharacterAdjointDeterminantStatement
import Langlands.Analysis.Local.ProductModularCharacter
import Langlands.Analysis.Local.ModularCharacterContinuity

/-! # Local restriction and assembly of actual adelic modular characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Topology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The actual local point group is continuously isomorphic to its adelic image. -/
def ofPlaceEquiv (i : Place F) : PlaceGroupPoints F G i ≃ₜ* (ofPlace F G i).range where
  toFun g := ⟨ofPlace F G i g, ⟨g, rfl⟩⟩
  invFun x := atPlace F G i x.val
  left_inv g := atPlace_ofPlace_same F G i g
  right_inv x := by
    apply Subtype.ext
    obtain ⟨g, hg⟩ := x.property
    change ofPlace F G i (atPlace F G i x.val) = x.val
    rw [← hg, atPlace_ofPlace_same]
  map_mul' g h := Subtype.ext ((ofPlace F G i).map_mul g h)
  continuous_toFun := (continuous_ofPlace F G i).subtype_mk _
  continuous_invFun := (atPlace F G i).continuous.comp continuous_subtype_val

/-- An adelic character norm on a single local insertion is its normalized local norm. -/
@[simp] theorem characterNorm_ofPlace (χ : AlgebraicCharacter F G)
    (i : Place F) (g : PlaceGroupPoints F G i) :
    characterNorm F G χ (ofPlace F G i g) = localCharacterNorm F G χ i g := by
  classical
  apply Units.ext
  apply NNReal.coe_injective
  rw [coe_characterNorm_eq_prod_localCharacterNorm]
  cases i with
  | inl w =>
    have hfin : (∏ᶠ v : FinitePlace F,
        ((localCharacterNorm F G χ (.inr v)
          (atPlace F G (.inr v) (ofPlace F G (.inl w) g)) : ℝ≥0) : ℝ)) = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      rw [atPlace_ofPlace_of_ne F G (.inl w) (.inr v) (by simp)]
      simp
    rw [hfin, mul_one, Finset.prod_eq_single w]
    · rw [atPlace_ofPlace_same]
    · intro v _ hv
      rw [atPlace_ofPlace_of_ne F G (.inl w) (.inl v) (by simpa using hv)]
      simp
    · simp
  | inr v =>
    have hinf : (∏ w : InfinitePlace F,
        ((localCharacterNorm F G χ (.inl w)
          (atPlace F G (.inl w) (ofPlace F G (.inr v) g)) : ℝ≥0) : ℝ)) = 1 := by
      apply Finset.prod_eq_one
      intro w _
      rw [atPlace_ofPlace_of_ne F G (.inr v) (.inl w) (by simp)]
      simp
    rw [hinf, one_mul, finprod_eq_single _ v]
    · rw [atPlace_ofPlace_same]
    · intro w hw
      rw [atPlace_ofPlace_of_ne F G (.inr v) (.inr w) (by simpa using hw)]
      simp

variable [LocallyOfFiniteType G.X.hom]

/-- The actual ambient modular character restricts to the local one at every place. -/
@[simp] theorem modularCharacter_ofPlace (i : Place F) (g : PlaceGroupPoints F G i) :
    Measure.modularCharacter (ofPlace F G i g) = Measure.modularCharacter g :=
  Langlands.QuotientIntegration.modularCharacter_subgroupEquiv
    (ofPlace F G i).range (isClosedEmbedding_ofPlace F G i).isClosed_range
      (ofPlaceEquiv F G i) g

/-- Local comparison with any actual rational character implies adelic comparison. -/
theorem modularCharacter_eq_characterNorm_of_local (χ : AlgebraicCharacter F G)
    (hlocal : ∀ (i : Place F) (g : PlaceGroupPoints F G i),
      Measure.modularCharacter g = (localCharacterNorm F G χ i g : ℝ≥0))
    (g : AdelicGroupPoints F G) :
    Measure.modularCharacter g = (characterNorm F G χ g : ℝ≥0) := by
  let χnorm : AdelicGroupPoints F G →ₜ* ℝ≥0 :=
    { toFun x := (characterNorm F G χ x : ℝ≥0)
      map_one' := by simp
      map_mul' x y := by simp
      continuous_toFun := Units.continuous_val.comp (characterNorm F G χ).continuous }
  have heq : Langlands.Haar.continuousModularCharacter = χnorm := by
    apply continuousMonoidHom_ext_ofPlace F G
    intro i x
    change Measure.modularCharacter (ofPlace F G i x) =
      (characterNorm F G χ (ofPlace F G i x) : ℝ≥0)
    rw [modularCharacter_ofPlace, characterNorm_ofPlace]
    exact hlocal i x
  exact DFunLike.congr_fun heq g

/-- The universal local adjoint-determinant comparison implies its adelic counterpart. -/
theorem adelicModularCharacterAdjointDeterminantStatement_of_local
    (hlocal : PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement.{u}) :
    AdelicModularCharacterAdjointDeterminantStatement.{u} := by
  intro F _ _ G _ _ hsm _
  exact modularCharacter_eq_characterNorm_of_local F G
    (Langlands.GroupScheme.Lie.adjointDeterminantCharacter G).toMul
    (hlocal F G hsm)

end Langlands.Global.AdelicGroupPoints
