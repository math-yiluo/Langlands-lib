import Langlands.Global.AdelicEisensteinPointwiseContinuationStatement
import Langlands.Global.AdelicEisensteinImaginaryJointContinuityReduction
import Langlands.Global.AdelicEisensteinFamilyJointContinuity
import Langlands.Global.AdelicEisensteinCentralCovariance

/-! # Joint continuity and covariance of finite Eisenstein families -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global

open GroupScheme Automorphic.GroupSchemeFunctions AdelicGroupPoints Langlands.Analysis.Meromorphic

/-- A finite entire-weighted Eisenstein family agreeing with the convergent series on a
regular patch is jointly continuous and inherits the covariances of the series throughout
its given domain of holomorphy. -/
def EisensteinFamilyRegularityStatement : Prop :=
  EisensteinPointwiseContinuationStatement.{0} → EisensteinJointRootHyperplaneStatement.{0} →
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F))) (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (q : ℕ) (v : Fin q → AdelicGroupPoints F G → ℂ)
      (b : Fin q → ComplexCharacterParameter F P → ℂ)
      (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (DE : Set (ComplexCharacterParameter F P)),
    (∀ j, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho (v j)) →
    (∀ j, IsMeromorphicInCoordinatesOn (b j) univ) →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) DE) →
    ∀ {m : ℕ} (e : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
    (∀ R : ℝ, ∃ V : Set (Fin m → ℂ), IsOpen V ∧ V.Nonempty ∧
      ∀ t ∈ V, r.IsRegularParameter hA hT R (e t) ∧
        ∀ g, E (e t) g = ∑ j, b j (e t) * hK.eisensteinSeries (v j) (e t) g) →
    ContinuousOn (fun t : (Fin m → ℂ) × AdelicGroupPoints F G => E (e t.1) t.2)
      ((e ⁻¹' DE) ×ˢ univ) ∧
    (∀ lam ∈ DE, IsLeftInvariantUnder F G (rationalSubgroup F G) (E lam)) ∧
    ∀ {x : AdelicGroupPoints F P} (s : ℂ),
      let z := map F P G p x
      (∀ g, z * g = g * z) →
      (∀ j g, v j (z * g) = s * v j g) →
      ∀ lam ∈ DE, ∀ g, E lam (g * z) = s * parameterPower F P lam x * E lam g

set_option maxHeartbeats 800000 in
/-- Use the local clearing for the pointwise continuations, and propagate the transformation
laws from the same open agreement patch by scalar meromorphic uniqueness. -/
theorem eisensteinFamilyRegularity : EisensteinFamilyRegularityStatement := by
  classical
  intro hPt hJoint F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU
    K hK N d rho hsmooth hcalc hKmax hρ q v b E DE hv hb hE m e hPatch
  obtain ⟨Ep, DP, hp, R, hR⟩ := hPt F G P M U A p iU l a r hA hT hG hU K hK
    rho hsmooth hcalc hKmax hρ (Fin q) v hv
  obtain ⟨V, hVo, hVne, hV⟩ := hPatch R
  refine ⟨?_, ?_, ?_⟩
  · let L (β : characterLattice A) := (r.rootFunctional hA hT β).comp e.toLinearMap
    refine finiteMeromorphicFamilyJointContinuity e L b Ep E (fun _ => DP) DE
      hE hp hb V hVo hVne ?_ ?_
    · intro g t ht
      rw [(hV t ht.1).2 g]
      exact Finset.sum_congr rfl fun j _ => by rw [hR (e t) (hV t ht.1).1 j]
    · intro t₀ _ j
      obtain ⟨S, k, W, H, _, hne, hWo, ht₀, hH, _, _, hEq⟩ :=
        hJoint F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc (v j)
          hKmax hρ (hv j) (Ep j) DP (hp j) ⟨R, fun lam hlam => hR lam hlam j⟩ m e t₀
      refine ⟨S, k, W, H, ?_, hWo, ht₀, hH, ?_⟩
      · intro β hβ
        obtain ⟨χ, hχ⟩ := r.exists_rootFunctional_ne_zero hA hT (hne β hβ)
        refine ⟨e.symm ((1 : ℂ) ⊗ₜ[ℤ] χ), ?_⟩
        simpa only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hχ
      · intro g t ht
        simpa only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub] using hEq g t ht.1 ht.2
  · intro lam hlam d₀ hd g
    refine (hE (d₀ * g)).eqOn_of_eqOn_open (hE g) e hVo hVne ?_ ⟨hlam, hlam⟩
    intro t ht
    change E (e t) (d₀ * g) = E (e t) g
    rw [(hV t ht.1).2 (d₀ * g), (hV t ht.1).2 g]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eisensteinSeries_leftRationalInvariant hK (hv j).1 hU r.isCompatible.levi (e t) d₀ hd g]
  · intro x s z hz hvs lam hlam g
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE g).1
    have hRhs : IsMeromorphicInCoordinatesOn
        (fun t => s * parameterPower F P t x * E t g) ((univ ∩ univ) ∩ DE) :=
      ((isMeromorphicInCoordinatesOn_const s).mul (isMeromorphicInCoordinatesOn_parameterPower x)).mul (hE g)
    refine (hE (g * z)).eqOn_of_eqOn_open hRhs e hVo hVne ?_
      ⟨hlam, ⟨mem_univ _, mem_univ _⟩, hlam⟩
    intro t ht
    change E (e t) (g * z) = s * parameterPower F P (e t) x * E (e t) g
    rw [(hV t ht.1).2 (g * z), (hV t ht.1).2 g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hz g, hK.eisensteinSeries_central_mul hz (hvs j)]
    ring

end Langlands.Global
