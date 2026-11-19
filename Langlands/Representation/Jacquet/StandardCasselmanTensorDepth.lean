import Langlands.Representation.Jacquet.StandardCasselmanBoundedDepth
import Langlands.Representation.Jacquet.StandardTensorRayAsymptotics

/-! # Casselman depth for bi-invariant coefficient tensors -/

noncomputable section

universe u uV

open scoped TensorProduct NNReal

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Jacquet Langlands.Plancherel Langlands.Compact

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable {i : S.toGrp ⟶ G} {ν ζ : cocharacterLattice S}
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  {hG : IsConnectedReductive G} {hi : IsMaximalSplitTorus i} {hν : IsGenericCocharacter i ν}
  {hζ : IsStandardCocharacter i ν J ζ}
  {K0 L : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  {hB : CompactOpenNormalBasis K0 B}
  {hA : IsCompatibleStandardSplitComponent i ν J A q}
  {hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K}

set_option maxHeartbeats 800000 in
/-- At a basis level of bi-invariance, the same fixed-vector dimension bound
controls the actual normalized constant term of a whole coefficient tensor. -/
theorem IsStandardCasselmanDepthBound.coefficientTensorMap_eq_mul_constantTerm
    {c : ℕ} (hdepth : IsStandardCasselmanDepthBound.{u, uV}
      hG hi hν hζ hB hA hmem c)
    (hL : L ∈ B) (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
    {d : ℕ} (hd : Module.finrank ℂ (fixedVectors ρ.representation L) ≤ d)
    (t : CoefficientTensor ρ)
    (hinv : ∀ (k l : basisOpenSubgroup hB hL) (g : rationalPoints G),
      coefficientTensorMap ρ t ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap ρ t g)
    (y : cocharacterLattice S)
    (hy : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y)
    (hdeep : ∀ α ∈ simpleRelativeRoots i ν, α ∉ J → (d : ℤ) * c ≤ latticePairing S α y)
    (a : standardLeviPoints i ν J)
    (ha : (a : rationalPoints G) = Aubert.General.uniformizerPowers i (.ofAdd y)) :
    coefficientTensorMap ρ t (a : rationalPoints G) =
      standardHalfModulus i ν J a * standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) a := by
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  obtain ⟨b, hb⟩ := D.exists_isStablePairing
    (standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ.representation hρ)
  let L' := basisOpenSubgroup hB hL
  have hLc : IsCompact (L' : Set (rationalPoints G)) := (hB.1 L hL).2.2.2
  let Av := coefficientTensorBiAverage ρ L' hLc
  have ht : coefficientTensorMap ρ (Av t) = coefficientTensorMap ρ t :=
    coefficientTensorMap_biAverage_eq ρ L' hLc t hinv
  rw [← ht, standardConstantTerm_coefficientTensorMap hG hi hν hζ hB hA hmem ρ hρ hb]
  clear ht hinv
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    let v' := averageMap ρ.representation ρ.isSmooth L' hLc v
    let ℓ' := averageMap (smoothContragredient ρ.representation)
      (isSmooth_smoothContragredient ρ.representation) L' hLc ℓ
    have hv : v' ∈ fixedVectors ρ.representation L :=
      averageMap_mem_fixedVectors ρ.representation ρ.isSmooth L' hLc v
    have hℓ : ℓ' ∈ fixedVectors (smoothContragredient ρ.representation) L :=
      averageMap_mem_fixedVectors (smoothContragredient ρ.representation)
        (isSmooth_smoothContragredient ρ.representation) L' hLc ℓ
    have hAv : Av (v ⊗ₜ[ℂ] ℓ) = v' ⊗ₜ[ℂ] ℓ' := by
      simp only [Av, coefficientTensorBiAverage, LinearMap.comp_apply,
        coefficientTensorDualAverage, coefficientTensorSourceAverage, TensorProduct.map_tmul,
        LinearMap.id_apply, v', ℓ']
    rw [hAv]
    have hp := hdepth hL ρ.representation hρ hb hd hv hℓ y hy hdeep
    rw [← ha] at hp
    have hn := D.inv_sqrt_mul_eq_coefficientConstantTerm ρ.representation b
      (standardRadicalModulus i ν J) ℓ' v' a hp
    change (standardHalfModulus i ν J a)⁻¹ *
        smoothDualPairing ρ.representation ℓ' (ρ.representation a v') =
      D.coefficientConstantTerm ρ.representation b (standardRadicalModulus i ν J) ℓ' v' a at hn
    change smoothDualPairing ρ.representation ℓ' (ρ.representation a v') =
      standardHalfModulus i ν J a *
        D.coefficientConstantTerm ρ.representation b (standardRadicalModulus i ν J) ℓ' v' a
    rw [← hn, ← mul_assoc,
      mul_inv_cancel₀ (standardHalfModulus_ne_zero (i := i) (ν := ν) (J := J) a), one_mul]
  | add t s ht hs =>
    simp only [map_add, LocallyConstant.add_apply, ht, hs]
    exact (mul_add _ _ _).symm

end Langlands.BruhatTits.SpecialCompact
