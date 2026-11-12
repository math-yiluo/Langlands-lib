import Langlands.Representation.RankinSelberg.SphericalWhittakerFormula
import Langlands.Representation.RankinSelberg.UnramifiedPairProof
import Langlands.Representation.Conductor.SphericalCentral
import Langlands.Representation.Conductor.Essential
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof
import Langlands.Representation.Unramified.SphericalProductVector
import Langlands.LocalField.Normalization.Proof

/-!
# Spherical tests of unramified generic constituents are Jacquet's spherical functions

Let `σ` be an unramified generic constituent of `GL_(r+1)(F)` with Satake parameters `x`
and central character `ω` with `ω(ϖ) = ∏ x_i`. The normalized spherical test of any
nonzero inverse-character Whittaker functional of `σ` is Jacquet's explicit function
`W(·; x; ψ̄)` (`Conductor.inverseSphericalWhittaker`). Both are cell functions: they are
determined by their values on dominant torus elements, which agree on partitions by
Shintani's formula (`inverseSphericalTest_torus_schur`) and transform alike under the
center.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Conductor Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.Unramified Langlands.Correspondence
open Langlands.RankinSelberg.UnramifiedWhittaker

universe uF uV

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The Satake–Schur value is homogeneous under central shifts of the weight. -/
theorem satakeSchur_add_const {n : ℕ} (x : Fin (n + 1) → ℂˣ) (lam : Fin (n + 1) → ℤ)
    (t : ℤ) :
    satakeSchur x (fun i => lam i + t) = (∏ i, (x i : ℂ)) ^ t * satakeSchur x lam := by
  have hprod : (∏ i, (x i : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (x i).ne_zero
  have hshift : (fun i => (lam i + t) - (lam (Fin.last n) + t)) =
      (fun i => lam i - lam (Fin.last n)) := by
    funext i
    ring
  simp only [satakeSchur, hshift, zpow_add₀ hprod]
  ring

section Model

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)

/-- The normalized inverse spherical test of an unramified generic constituent with
Satake parameters `x = characterValues F χ` and central character `ω`, `ω(ϖ) = ∏ x_i`,
is Jacquet's explicit spherical function `W(·; x; ψ̄)`. -/
theorem sphericalTest_eq_inverseSphericalWhittaker
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : HasIntegerConductor ψ)
    (χ : Fin (r + 1) → QuasiCharacter F)
    (hgen : IsUnramifiedGenericConstituent F ψ σ χ)
    (ω : F.Carrierˣ →* ℂˣ)
    (hω : Classification.HasGLCentralCharacter F.Carrier (r + 1) σ ω)
    (hωϖ : (ω F.canonicalTopologicalData.uniformizerUnit : ℂ) =
      ∏ i, (characterValues F χ i : ℂ))
    (ℓ : glInverseFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0) (w : SphericalTest σ ℓ) :
    sphericalTestFunction σ ℓ w =
      (inverseSphericalWhittaker hψ.1 (uniformizerUnit_isUniformizingElement F)
        F.canonicalTopologicalData.residueCardinality (characterValues F χ)).val := by
  classical
  set ϖ := F.canonicalTopologicalData.uniformizerUnit with hϖdef
  have hϖ : IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ :=
    uniformizerUnit_isUniformizingElement F
  set q := F.canonicalTopologicalData.residueCardinality
  set x := characterValues F χ
  have hθK := isIntegrallyTrivial_inverseStandardCharacter hψ.1 r
  have hK : ∀ g, ∀ k ∈ integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
      sphericalTestFunction σ ℓ w (g * k) = sphericalTestFunction σ ℓ w g :=
    fun g k hk => sphericalTestFunction_right_invariant σ ℓ w ⟨k, hk⟩ g
  have hoff : ∀ lam : Fin (r + 1) → ℤ, ¬ Antitone lam →
      sphericalTestFunction σ ℓ w (torus ϖ lam) = 0 :=
    fun lam hlam => eval_torus_eq_zero_of_not_antitone hϖ
      (sphericalTestFunction_equivariance σ ℓ w) hK
      (inverseStandardCharacter_nondegenerate F ψ hψ) hlam
  have hmem : sphericalTestFunction σ ℓ w ∈
      (equivariantFunctions (upperUnipotent (r + 1) F.Carrier)
        (inverseStandardCharacter ψ r)).toSubmodule :=
    fun u g => sphericalTestFunction_equivariance σ ℓ w u g
  -- The central shift of the test.
  have hcent : ∀ (g : Langlands.GeneralLinear (r + 1) F.Carrier) (t : ℤ),
      sphericalTestFunction σ ℓ w (g * torus ϖ (fun _ : Fin (r + 1) => t)) =
        (∏ i, (x i : ℂ)) ^ t * sphericalTestFunction σ ℓ w g := by
    intro g t
    obtain ⟨v, hv⟩ := modelMap_surjective σ ℓ w.val.val
    have hval (h : Langlands.GeneralLinear (r + 1) F.Carrier) :
        sphericalTestFunction σ ℓ w h = ℓ.val (σ h v) :=
      (congrArg (fun u : (coefficientModel σ ℓ).toSubmodule => u.val.val h) hv).symm
    rw [hval, hval, map_mul, Module.End.mul_apply, torus_const_eq_scalar, hω (ϖ ^ t) v]
    simp only [map_smul, smul_eq_mul, map_zpow, Units.val_zpow_eq_zpow_val, hωϖ]
  -- Agreement on dominant torus elements.
  have htorus : ∀ lam : Fin (r + 1) → ℤ, Antitone lam →
      sphericalTestFunction σ ℓ w (torus ϖ lam) = halfModulus q lam * satakeSchur x lam := by
    intro lam hlam
    set t := lam (Fin.last r)
    set mu : Fin (r + 1) → ℤ := fun i => lam i - t
    have hmu : IsPartitionExponent mu := by
      refine ⟨fun i j hij => sub_le_sub_right (hlam hij) t, fun i => ?_⟩
      exact sub_nonneg.mpr (hlam (Fin.le_last i))
    have hlam' : lam = fun i => mu i + t := by
      funext i
      simp [mu]
    rw [hlam', torus_add_const, hcent, satakeSchur_add_const, halfModulus_add_const,
      inverseSphericalTest_torus_schur F σ ψ hψ χ hgen ℓ hℓ w mu hmu]
    ring
  change _ = sphericalWhittaker hϖ (inverseStandardCharacter ψ r) q x
  rw [eq_cellFunction hϖ hθK hmem hK hoff,
    eq_cellFunction hϖ hθK (sphericalWhittaker_mem hϖ q x hθK)
      (fun g k hk => sphericalWhittaker_mul_integral hϖ q x hθK g hk)
      (fun lam hlam => by simp [sphericalWhittaker_torus hϖ q x hθK, hlam])]
  congr 1
  funext lam
  rw [sphericalWhittaker_torus hϖ q x hθK]
  split_ifs with hlam
  · exact htorus lam hlam
  · exact hoff lam hlam

end Model

section Unitary

/-- A normalized principal series of norm-one unramified characters is generic: it is
the product of the singleton segments `[μ_(w_k)]`, which are segment heads and pairwise
unlinked (Zelevinsky's classification, `genericSegmentProductExhaustion`). -/
theorem unitaryBlock_isGeneric (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    (w : Fin (n + 1) → ℂˣ) (hw : ∀ k, ‖(w k : ℂ)‖ = 1) :
    Whittaker.IsGeneric ψ n (unitaryBlock F w).representation := by
  let T := F.canonicalTopologicalData
  let ρ : Fin (n + 1) → T.CuspidalDatum.{uF, uF} := fun k => unramifiedCuspidalDatum F (w k)
  let A := fun k => Correspondence.rankOneSupercuspidalObject.{uF, uF} F (character F (w k))
  have h : ∑ k, (ρ k).rank = n + 1 := by simp [ρ, unramifiedCuspidalDatum]
  let d : T.SegmentProductDatum.{uF, uF} (n + 1) :=
    PadicField.TopologicalData.SegmentProductDatum.ofCuspidals T ρ h A
  have hhead (i : Fin (n + 1)) : T.IsSegmentHead (d.segments i) (d.blocks i) :=
    singletonSegment_isSegmentHead F T (ρ i) (A i) rfl
  have hsq (i : Fin (n + 1)) : T.IsSquareIntegrable (d.blocks i).representation :=
    isSquareIntegrable_castRank F T _ _ (rankOneUnitary_isSquareIntegrable F (w i) (hw i))
  have hunl : d.multisegment.IsUnlinked := by
    intro Δ hΔ Δ' hΔ'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hΔ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hΔ'
    exact Classification.squareIntegrableSegmentNonlinkage.{uF, 0} T _ _
      (d.blocks i) (d.blocks j) (hhead i) (hhead j) (hsq i) (hsq j)
  have hEq : T.cuspidalProductInduced ρ h A = unitaryBlock F w := rfl
  have e := (PadicField.TopologicalData.SegmentProductDatum.ofCuspidalsInducedIso T ρ h A).symm
  rw [hEq] at e
  exact (Classification.genericSegmentProductExhaustion.{uF, uF} (F := F) T ψ n
    (unitaryBlock F w)).mpr ⟨d, hhead, hunl, ⟨e⟩⟩

/-- The normalized principal series of `unitaryBlock F z` is the principal series
`principalSeriesOfTuple F z`, up to the `ULift` of the one-dimensional factors. -/
def unitaryBlockEquiv {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    (unitaryBlock F z).representation.Equiv (principalSeriesOfTuple F z) := by
  let T := F.canonicalTopologicalData
  have hU : (unitaryBlock F z).representation =
      T.normalizedProductInduced (BlockShape.singletons (r + 1))
        (fun k => (Correspondence.rankOneSupercuspidalObject.{uF, uF} F
          (character F (z k))).obj.representation) :=
    T.normalizedProductInductionFunctor_obj _ _
  rw [hU]
  unfold principalSeriesOfTuple principalSeries characterTuple
  exact T.normalizedProductInducedEquiv (BlockShape.singletons (r + 1)) (fun i =>
    Representation.Equiv.mk ULift.moduleEquiv (fun g => by ext v; rfl))

/-- A normalized principal series of norm-one unramified characters is generic. -/
theorem principalSeriesOfTuple_isGeneric (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    (z : Fin (r + 1) → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :
    Whittaker.IsGeneric ψ r (principalSeriesOfTuple F z) :=
  (Whittaker.isGeneric_iff_of_equiv ψ r (unitaryBlockEquiv F z)).mp
    (unitaryBlock_isGeneric F ψ z hz)

/-- The unramified principal series has a nonzero `GL_(r+1)(O)`-fixed vector. -/
theorem principalSeriesOfTuple_fixedVectors_ne_bot {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    fixedVectors (principalSeriesOfTuple F z) (sphericalSubgroup F r) ≠ ⊥ := by
  unfold principalSeriesOfTuple principalSeries
  refine Langlands.Unramified.SphericalProduct.normalizedProductInduced_fixedVectors_ne_bot F
    (borelShape r) _ (fun _ => inferInstance) (fun i => ?_)
  rw [eq_top_iff]
  intro v _
  rw [fixedVectors, Representation.mem_invariants]
  intro g
  have hdet : (characterTuple F z i).toMonoidHom (GeneralLinear.determinant g.val) = 1 :=
    characterTuple_isUnramified F z i (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp g.property))
  show (((characterTuple F z i).toMonoidHom (GeneralLinear.determinant g.val) : ℂˣ) : ℂ) • v = v
  rw [hdet, Units.val_one, one_smul]

/-- A norm-one unramified principal series is an unramified generic constituent of
itself. -/
theorem principalSeriesOfTuple_isUnramifiedGenericConstituent
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : ∀ k, ‖(z k : ℂ)‖ = 1) :
    IsUnramifiedGenericConstituent F ψ (principalSeriesOfTuple F z) (characterTuple F z) :=
  ⟨principalSeriesOfTuple_isGeneric F ψ z hz, principalSeriesOfTuple_fixedVectors_ne_bot F z,
    characterTuple_isUnramified F z,
    ⟨⊤, subrepresentationSubtype _ ⊤, fun v => ⟨⟨v, trivial⟩, rfl⟩⟩⟩

/-- The central character of the unramified principal series is `∏ χ_(z_i)`; its value at
the uniformizer is `∏ z_i`. -/
theorem principalSeriesOfTuple_hasGLCentralCharacter {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    Classification.HasGLCentralCharacter F.Carrier (r + 1) (principalSeriesOfTuple F z)
      (∏ i, (characterTuple F z i).toMonoidHom) := by
  unfold principalSeriesOfTuple principalSeries
  refine F.canonicalTopologicalData.hasScalarCharacter_normalizedProductInduced (borelShape r)
    (fun i => ?_)
  intro a v
  change ((determinantQuasiCharacter F 1 (characterTuple F z i)
    (GeneralLinear.scalar a) : ℂˣ) : ℂ) • v = _
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a) = a := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  show (((characterTuple F z i).toMonoidHom
    (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) a)) : ℂˣ) : ℂ) • v = _
  rw [hd]

theorem prod_characterTuple_uniformizer {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    (((∏ i, (characterTuple F z i).toMonoidHom) F.canonicalTopologicalData.uniformizerUnit :
      ℂˣ) : ℂ) = ∏ i, (characterValues F (characterTuple F z) i : ℂ) := by
  simp [characterValues_characterTuple, MonoidHom.finsetProd_apply, characterTuple,
    PadicField.TopologicalData.ord_uniformizer]

/-- Every nonzero inverse-character functional of a norm-one unramified principal series
has a normalized spherical test. -/
theorem principalSeriesOfTuple_nonempty_sphericalTest (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductor ψ) {r : ℕ} (z : Fin (r + 1) → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1)
    (ℓ : glInverseFunctionals ψ r (principalSeriesOfTuple F z)) (hℓ : ℓ.val ≠ 0) :
    Nonempty (SphericalTest (principalSeriesOfTuple F z) ℓ) :=
  ⟨((unramifiedSphericalVector p F r (principalSeriesOfTuple F z) ψ hψ
    (principalSeriesOfTuple_isGeneric F ψ z hz)
    (principalSeriesOfTuple_fixedVectors_ne_bot F z)).2 ℓ hℓ).choose⟩

/-- The normalized spherical test of a norm-one unramified principal series with
parameters `z` is Jacquet's explicit spherical function `W(·; z; ψ̄)`. -/
theorem principalSeriesOfTuple_sphericalTest_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductor ψ) {r : ℕ} (z : Fin (r + 1) → ℂˣ) (hz : ∀ k, ‖(z k : ℂ)‖ = 1)
    (ℓ : glInverseFunctionals ψ r (principalSeriesOfTuple F z)) (hℓ : ℓ.val ≠ 0)
    (w : SphericalTest (principalSeriesOfTuple F z) ℓ) :
    sphericalTestFunction _ ℓ w =
      (inverseSphericalWhittaker hψ.1 (uniformizerUnit_isUniformizingElement F)
        F.canonicalTopologicalData.residueCardinality z).val := by
  have h := sphericalTest_eq_inverseSphericalWhittaker F (principalSeriesOfTuple F z) ψ hψ
    (characterTuple F z) (principalSeriesOfTuple_isUnramifiedGenericConstituent F ψ z hz) _
    (principalSeriesOfTuple_hasGLCentralCharacter F z) (prod_characterTuple_uniformizer F z)
    ℓ hℓ w
  rwa [characterValues_characterTuple] at h

end Unitary

end Langlands.RankinSelberg.HighlyRamified
