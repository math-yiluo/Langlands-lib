import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Normed.Ring.Units

/-! # Basis charts on actual unramified characters (Renard V.3.20)

For an arbitrary integer basis `b` of the actual discrete valuation image, evaluating an image
character at the basis elements gives an open embedding into `κ → ℂ`. Through the published
identification of image characters with continuous unramified characters of `G(F)`, this is a
single global chart on `X(G)`. It defines the charted space used to state the complex torus
structure of `X(G)`. The unitary subgroup `Im X(G)` is included in `X(G)` by forgetting
unitarity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
variable {κ : Type v}
  (b : Module.Basis κ ℤ (Additive (rationalDiscreteValuationImage G)))

/-- The image character taking the prescribed unit values on the basis `b`. -/
def rationalImageBasisCharacter (c : κ → ℂˣ) : rationalImageCharacters G where
  toFun a := ((b.constr ℤ (fun i => Additive.ofMul (c i))) (Additive.ofMul a)).toMul
  map_one' := by
    change ((b.constr ℤ (fun i => Additive.ofMul (c i)))
      (0 : Additive (rationalDiscreteValuationImage G))).toMul = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    change ((b.constr ℤ (fun i => Additive.ofMul (c i)))
      (Additive.ofMul x + Additive.ofMul y)).toMul = _
    rw [map_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

@[simp]
theorem rationalImageBasisCharacter_basis (c : κ → ℂˣ) (i : κ) :
    rationalImageBasisCharacter G b c ((b i).toMul) = c i := by
  change ((b.constr ℤ (fun i => Additive.ofMul (c i))) (b i)).toMul = _
  rw [Module.Basis.constr_basis]
  rfl

variable [Fintype κ]

/-- The value of the reconstructed character is the Laurent monomial in the basis values. -/
theorem rationalImageBasisCharacter_apply (c : κ → ℂˣ) (a : rationalDiscreteValuationImage G) :
    rationalImageBasisCharacter G b c a = ∏ i, c i ^ (b.repr (Additive.ofMul a) i) := by
  change ((b.constr ℤ (fun i => Additive.ofMul (c i))) (Additive.ofMul a)).toMul = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul]
  rfl

/-- Evaluation at the basis `b` identifies image characters with tuples of complex units,
as topological groups. -/
def rationalImageBasisUnitCoordinates : rationalImageCharacters G ≃ₜ* (κ → ℂˣ) where
  toFun χ i := χ ((b i).toMul)
  invFun := rationalImageBasisCharacter G b
  left_inv χ := by
    apply ContinuousMonoidHom.ext
    intro a
    have he := DFunLike.congr_fun
      (b.constr_self ℤ χ.toMonoidHom.toAdditive.toIntLinearMap) (Additive.ofMul a)
    exact congrArg Additive.toMul he
  right_inv c := funext (rationalImageBasisCharacter_basis G b c)
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_eval_const ((b i).toMul)
  continuous_invFun := by
    apply (ContinuousMonoidHom.isClosedEmbedding_coe
      (A := rationalDiscreteValuationImage G) (B := ℂˣ)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro a
    change Continuous (fun c : κ → ℂˣ => rationalImageBasisCharacter G b c a)
    simp_rw [rationalImageBasisCharacter_apply]
    exact continuous_finsetProd _ fun i _ => (continuous_apply i).zpow _

@[simp]
theorem rationalImageBasisUnitCoordinates_apply (χ : rationalImageCharacters G) (i : κ) :
    rationalImageBasisUnitCoordinates G b χ i = χ ((b i).toMul) := rfl

/-- Complex coordinates of an image character: its values on the basis `b`, as complex
numbers. -/
def rationalImageBasisEvaluation (χ : rationalImageCharacters G) : κ → ℂ :=
  fun i => ((χ ((b i).toMul) : ℂˣ) : ℂ)

theorem rationalImageBasisEvaluation_eq :
    rationalImageBasisEvaluation G b =
      Pi.map (fun _ : κ => (Units.val : ℂˣ → ℂ)) ∘ rationalImageBasisUnitCoordinates G b :=
  rfl

/-- The basis coordinates are an open embedding of the image characters into `κ → ℂ`. -/
theorem isOpenEmbedding_rationalImageBasisEvaluation :
    IsOpenEmbedding (rationalImageBasisEvaluation G b) := by
  rw [rationalImageBasisEvaluation_eq]
  have hpi : IsOpenEmbedding (Pi.map (fun _ : κ => (Units.val : ℂˣ → ℂ))) :=
    isOpenEmbedding_iff_isEmbedding_isOpenMap.mpr
      ⟨IsEmbedding.piMap fun _ => Units.isOpenEmbedding_val.isEmbedding,
        IsOpenMap.piMap (fun _ => Units.isOpenEmbedding_val.isOpenMap)
          (by rw [Filter.cofinite_eq_bot]; exact Filter.eventually_bot)⟩
  exact hpi.comp (rationalImageBasisUnitCoordinates G b).toHomeomorph.isOpenEmbedding

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rationalUnramifiedComplexChartPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Complex coordinates on actual unramified characters of `G(F)` for the basis `b`: the value
of the corresponding image character on each basis element. -/
def rationalUnramifiedBasisCoordinates
    (χ : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) : κ → ℂ :=
  rationalImageBasisEvaluation G b ((rationalCanonicalImageUnramifiedContinuousEquiv G).symm χ)

omit [Fintype κ] in
/-- A coordinate is the value of the character at any rational point whose valuation image is
the corresponding basis element. -/
theorem rationalUnramifiedBasisCoordinates_apply
    (χ : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) (i : κ)
    (g : GroupScheme.rationalPoints G)
    (hg : rationalValuationImageProjection G g = (b i).toMul) :
    rationalUnramifiedBasisCoordinates G b χ i = ((χ.val g : ℂˣ) : ℂ) := by
  change (((rationalCanonicalImageUnramifiedContinuousEquiv G).symm χ ((b i).toMul) : ℂˣ) :
    ℂ) = _
  rw [← hg, rationalCanonicalImageUnramifiedContinuousEquiv_symm_projection]

theorem isOpenEmbedding_rationalUnramifiedBasisCoordinates :
    IsOpenEmbedding (rationalUnramifiedBasisCoordinates G b) :=
  (isOpenEmbedding_rationalImageBasisEvaluation G b).comp
    (rationalCanonicalImageUnramifiedContinuousEquiv G).symm.toHomeomorph.isOpenEmbedding

/-- The charted space on `X(G)` with the single global chart given by the basis coordinates
`rationalUnramifiedBasisCoordinates G b`, modelled on `κ → ℂ`. -/
@[instance_reducible]
def rationalUnramifiedBasisChartedSpace :
    ChartedSpace (κ → ℂ)
      (unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :=
  (isOpenEmbedding_rationalUnramifiedBasisCoordinates G b).singletonChartedSpace

theorem rationalUnramifiedBasisChartedSpace_chartAt
    (χ : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
    ⇑(@chartAt (κ → ℂ) _ _ _ (rationalUnramifiedBasisChartedSpace G b) χ) =
      rationalUnramifiedBasisCoordinates G b :=
  rfl

/-- The inclusion of the unitary unramified characters `Im X(G)` in `X(G)`. -/
def rationalUnitaryUnramifiedInclusion :
    unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul) →*
      unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul) :=
  Subgroup.inclusion inf_le_left

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalUnitaryUnramifiedInclusion_val
    (χ : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul)) :
    (rationalUnitaryUnramifiedInclusion G χ).val = χ.val := rfl

end CanonicalTopology

end Langlands.Plancherel
