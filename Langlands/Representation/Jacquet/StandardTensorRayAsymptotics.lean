import Langlands.Representation.Jacquet.FixedDimensionRayAsymptotics
import Langlands.Representation.Jacquet.StandardConstantTermFixedLevel
import Langlands.Representation.Jacquet.StandardCentralContraction

/-! # A fixed-dimensional ray threshold for the original chosen tensor constant term -/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compact averaging on the actual smooth-dual tensor factor. -/
def coefficientTensorDualAverage (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    CoefficientTensor ρ →ₗ[ℂ] CoefficientTensor ρ :=
  TensorProduct.map LinearMap.id
    (Compact.averageMap (smoothContragredient ρ.representation)
      (isSmooth_smoothContragredient ρ.representation) K hK)

theorem coefficientTensorDualAverage_eq_averageMap
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    let T := (coefficientTensorAction ρ).comp (MonoidHom.inr G G)
    let hT := isSmooth_comp (MonoidHom.inr G G)
      (continuous_const.prodMk continuous_id) (isSmooth_coefficientTensorAction ρ)
    coefficientTensorDualAverage ρ K hK = Compact.averageMap T hT K hK := by
  intro T hT
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    let E : (smoothContragredient ρ.representation).IntertwiningMap T :=
      { toLinearMap := TensorProduct.mk ℂ ρ (SmoothDual ρ.representation) v
        isIntertwining' := fun g => by
          ext y
          change v ⊗ₜ[ℂ] smoothContragredient ρ.representation g y =
            ρ.representation 1 v ⊗ₜ[ℂ] smoothContragredient ρ.representation g y
          rw [map_one, Module.End.one_apply] }
    exact LinearMap.congr_fun
      (Compact.averageMap_commute (smoothContragredient ρ.representation) T
        (isSmooth_smoothContragredient ρ.representation) hT K hK E) ℓ
  | add s t hs ht => simp only [map_add, hs, ht]

/-- Source and dual compact averages on the original coefficient tensor. -/
def coefficientTensorBiAverage (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    CoefficientTensor ρ →ₗ[ℂ] CoefficientTensor ρ :=
  (coefficientTensorSourceAverage ρ K hK).comp (coefficientTensorDualAverage ρ K hK)

theorem coefficientTensorMap_sourceAverage_eq_of_rightInvariant
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : CoefficientTensor ρ)
    (hinv : ∀ (k : K) (g : G), coefficientTensorMap ρ t (g * k) = coefficientTensorMap ρ t g) :
    coefficientTensorMap ρ (coefficientTensorSourceAverage ρ K hK t) = coefficientTensorMap ρ t := by
  rw [coefficientTensorSourceAverage_eq_averageMap]
  ext g
  let T := (coefficientTensorAction ρ).comp (MonoidHom.inl G G)
  have hT : IsSmooth T := isSmooth_comp (MonoidHom.inl G G)
    (continuous_id.prodMk continuous_const) (isSmooth_coefficientTensorAction ρ)
  let φ : CoefficientTensor ρ →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((LocallyConstant.coeFnₗ ℂ).comp (coefficientTensorMap ρ))
  have := Compact.finite_orbit_of_smooth T hT K hK t
  change φ (Compact.orbitMean (T.comp K.toSubgroup.subtype) t) = φ t
  apply HarishChandraSchwartz.map_orbitMean_of_forall_eq
  intro k
  change coefficientTensorMap ρ (coefficientTensorAction ρ ((k : G), 1) t) g =
    coefficientTensorMap ρ t g
  rw [coefficientTensorMap_action]
  simpa only [inv_one, one_mul] using hinv k g

theorem coefficientTensorMap_dualAverage_eq_of_leftInvariant
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : CoefficientTensor ρ)
    (hinv : ∀ (k : K) (g : G), coefficientTensorMap ρ t (k * g) = coefficientTensorMap ρ t g) :
    coefficientTensorMap ρ (coefficientTensorDualAverage ρ K hK t) = coefficientTensorMap ρ t := by
  rw [coefficientTensorDualAverage_eq_averageMap]
  ext g
  let T := (coefficientTensorAction ρ).comp (MonoidHom.inr G G)
  have hT : IsSmooth T := isSmooth_comp (MonoidHom.inr G G)
    (continuous_const.prodMk continuous_id) (isSmooth_coefficientTensorAction ρ)
  let φ : CoefficientTensor ρ →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((LocallyConstant.coeFnₗ ℂ).comp (coefficientTensorMap ρ))
  have := Compact.finite_orbit_of_smooth T hT K hK t
  change φ (Compact.orbitMean (T.comp K.toSubgroup.subtype) t) = φ t
  apply HarishChandraSchwartz.map_orbitMean_of_forall_eq
  intro k
  change coefficientTensorMap ρ (coefficientTensorAction ρ (1, (k : G)) t) g =
    coefficientTensorMap ρ t g
  rw [coefficientTensorMap_action]
  simp only [mul_one]
  with_reducible_and_instances exact hinv k⁻¹ g

/-- Bi-invariance of the original coefficient makes both compact tensor
averages preserve exactly that same coefficient function. -/
theorem coefficientTensorMap_biAverage_eq
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : CoefficientTensor ρ)
    (hinv : ∀ (k l : K) (g : G),
      coefficientTensorMap ρ t ((k : G) * g * (l : G)) = coefficientTensorMap ρ t g) :
    coefficientTensorMap ρ (coefficientTensorBiAverage ρ K hK t) = coefficientTensorMap ρ t := by
  have hl : coefficientTensorMap ρ (coefficientTensorDualAverage ρ K hK t) =
      coefficientTensorMap ρ t :=
    coefficientTensorMap_dualAverage_eq_of_leftInvariant ρ K hK t
      (fun k g => by simpa only [OneMemClass.coe_one, mul_one] using hinv k 1 g)
  change coefficientTensorMap ρ
    (coefficientTensorSourceAverage ρ K hK (coefficientTensorDualAverage ρ K hK t)) = _
  rw [coefficientTensorMap_sourceAverage_eq_of_rightInvariant ρ K hK _ (by
    intro k g
    rw [hl]
    simpa only [OneMemClass.coe_one, one_mul] using hinv 1 k g), hl]

end Langlands.Plancherel

namespace Langlands.Jacquet.StablePairingData

open Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The normalized ray formula for the actual source-and-dual averaged
coefficient tensor, at the same fixed-dimensional threshold for every tensor. -/
theorem IsStablePairing.biAverage_normalized_pow_asymptotics
    (D : StablePairingData G) (ρ : SmoothRep.{0, uG, uV} ℂ G)
    {b : Coinvariants (smoothContragredient ρ.representation) D.N →ₗ[ℂ]
      Coinvariants ρ.representation D.Nbar →ₗ[ℂ] ℂ}
    (hA : D.Admits ρ.representation ρ.isSmooth)
    (hb : D.IsStablePairing ρ.representation ρ.isSmooth b)
    (δ : D.M →* ℝ≥0ˣ) (m : D.M) (hm : (m : G) = D.g⁻¹)
    (K : OpenSubgroup G) (hK : D.Good K)
    [FiniteDimensional ℂ (fixedVectors ρ.representation K.toSubgroup)]
    {d : ℕ} (hd : Module.finrank ℂ (fixedVectors ρ.representation K.toSubgroup) ≤ d)
    (t : CoefficientTensor ρ) {r : ℕ} (hr : d ≤ r) :
    coefficientTensorMap ρ (coefficientTensorBiAverage ρ K (D.isCompact K hK) t) (m ^ r) =
      ((NNReal.sqrt (δ (m ^ r) : ℝ≥0) : ℝ) : ℂ) *
        D.coefficientTensorConstantTerm ρ.representation b δ
          (coefficientTensorBiAverage ρ K (D.isCompact K hK) t) (m ^ r) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    have hv := Compact.averageMap_mem_fixedVectors ρ.representation ρ.isSmooth K (D.isCompact K hK) v
    have hℓ := Compact.averageMap_mem_fixedVectors (smoothContragredient ρ.representation)
      (isSmooth_smoothContragredient ρ.representation) K (D.isCompact K hK) ℓ
    have h := hb.normalized_pow_asymptotics_of_finrank_le hA δ m hm K hK hd hv hℓ hr
    simp only [coefficientTensorBiAverage, LinearMap.comp_apply, coefficientTensorDualAverage,
      coefficientTensorSourceAverage, TensorProduct.map_tmul, LinearMap.id_apply,
      coefficientTensorMap_tmul, coefficientTensorConstantTerm_tmul, Subgroup.coe_pow,
      smoothDualPairing] at h ⊢
    convert h using 1
    rfl
  | add s t hs ht =>
    simp only [map_add, LocallyConstant.add_apply, Pi.add_apply, hs, ht, mul_add]

end Langlands.Jacquet.StablePairingData

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Jacquet Langlands.Plancherel Langlands.HarishChandraSchwartz

namespace Langlands.BruhatTits.SpecialCompact

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup standardConstantTermT2Field standardConstantTermLocallyCompact
  standardConstantTermNonarchimedean

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {J : Set (characterLattice S)} {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B) {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)

include hG hν hmem in
/-- The original chosen constant term agrees with the original tensor
coefficient along the fixed strict ray from every power beyond the ambient
fixed-space dimension. Its threshold does not depend on tensor rank. -/
theorem standardConstantTerm_ray_of_finrank_le
    (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
    {K : Subgroup (rationalPoints G)} (hKB : K ∈ B)
    {d : ℕ}
    (hd : Module.finrank ℂ (fixedVectors ρ.representation
      (basisOpenSubgroup hB hKB).toSubgroup) ≤ d)
    (t : CoefficientTensor ρ)
    (hinv : ∀ (k l : basisOpenSubgroup hB hKB) (g : rationalPoints G),
      coefficientTensorMap ρ t ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap ρ t g)
    {r : ℕ} (hr : d ≤ r) :
    let m := (hA.centralStrictElement i ν hi hζ : standardLeviPoints i ν J)
    coefficientTensorMap ρ t ((m ^ r : standardLeviPoints i ν J) : rationalPoints G) =
      standardHalfModulus i ν J (m ^ r) *
        standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) (m ^ r) := by
  intro m
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ.representation ρ.isSmooth :=
    standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ.representation hρ
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hAd
  have hK := good_of_mem hG hi hν hζ hB hA hmem hKB
  have := hρ.2 (basisOpenSubgroup hB hKB)
  let t' := coefficientTensorBiAverage ρ (basisOpenSubgroup hB hKB)
    (D.isCompact _ hK) t
  have heq := coefficientTensorMap_biAverage_eq ρ (basisOpenSubgroup hB hKB)
    (D.isCompact _ hK) t hinv
  have hm : (m : rationalPoints G) = D.g⁻¹ := by
    change hA.strictElement i ν hi hζ = ((hA.strictElement i ν hi hζ)⁻¹)⁻¹
    rw [inv_inv]
  have h := hb.biAverage_normalized_pow_asymptotics D ρ hAd
    (standardRadicalModulus i ν J) m hm (basisOpenSubgroup hB hKB) hK hd t hr
  have hct := standardConstantTerm_coefficientTensorMap hG hi hν hζ hB hA hmem ρ hρ hb t'
  change coefficientTensorMap ρ t' (m ^ r) = _ at h
  rw [← hct] at h
  simp only [t', heq, Subgroup.coe_pow, standardHalfModulus] at h ⊢
  convert h using 1
  rfl

end Langlands.BruhatTits.SpecialCompact
