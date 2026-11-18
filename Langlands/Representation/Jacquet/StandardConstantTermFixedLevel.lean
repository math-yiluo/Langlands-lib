import Langlands.Representation.Jacquet.StandardTensorConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FixedLevelCoefficientAnnihilators
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.AdmissibleCoefficientSpace

/-! # The same actual constant term as a coefficient from its fixed Jacquet level -/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Compact averaging on the source factor of the actual coefficient tensor. -/
def coefficientTensorSourceAverage (ρ : SmoothRep.{0, uG, uV} ℂ G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    CoefficientTensor ρ →ₗ[ℂ] CoefficientTensor ρ :=
  TensorProduct.map (Compact.averageMap ρ.representation ρ.isSmooth K hK) LinearMap.id

/-- Averaging only the source factor is the compact average for the first
coordinate of the actual coefficient-tensor action. -/
theorem coefficientTensorSourceAverage_eq_averageMap
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    let T := (coefficientTensorAction ρ).comp (MonoidHom.inl G G)
    let hT := isSmooth_comp (MonoidHom.inl G G)
      (continuous_id.prodMk continuous_const) (isSmooth_coefficientTensorAction ρ)
    coefficientTensorSourceAverage ρ K hK = Compact.averageMap T hT K hK := by
  intro T hT
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    let E : ρ.representation.IntertwiningMap T :=
      { toLinearMap := (TensorProduct.mk ℂ ρ (SmoothDual ρ.representation)).flip ℓ
        isIntertwining' := fun g => by
          ext y
          change ρ.representation g y ⊗ₜ[ℂ] ℓ =
            ρ.representation g y ⊗ₜ[ℂ] smoothContragredient ρ.representation 1 ℓ
          rw [map_one, Module.End.one_apply] }
    exact LinearMap.congr_fun
      (Compact.averageMap_commute ρ.representation T ρ.isSmooth hT K hK E) v
  | add s t hs ht =>
    simp only [map_add, hs, ht]

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open Plancherel Langlands.Compact

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient of the source-averaged tensor has all source vectors
in the fixed space of the original representation. -/
theorem coefficientTensorSourceAverage_mem_coefficientSpaceFrom
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : CoefficientTensor ρ) :
    (fun g => coefficientTensorMap ρ (coefficientTensorSourceAverage ρ K hK t) g) ∈
      coefficientSpaceFrom ρ.representation (fixedVectors ρ.representation K.toSubgroup) := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    exact Submodule.subset_span ⟨ℓ.val, averageMap ρ.representation ρ.isSmooth K hK v,
      averageMap_mem_fixedVectors ρ.representation ρ.isSmooth K hK v, rfl⟩
  | add s t hs ht =>
    simp only [map_add, LocallyConstant.add_apply]
    with_reducible_and_instances exact Submodule.add_mem _ hs ht

/-- A right compact-open invariant coefficient sum of a smooth representation
is a coefficient sum with all source vectors in that same compact-open fixed
space. No admissibility or bound on tensor rank is needed. -/
theorem mem_coefficientSpaceFrom_fixedVectors_of_rightInvariant
    (ρ : SmoothRep.{0, uG, uV} ℂ G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {f : G → ℂ} (hf : f ∈ coefficientFunctionSpace ρ)
    (hinv : ∀ (k : K) (g : G), f (g * k) = f g) :
    f ∈ coefficientSpaceFrom ρ.representation (fixedVectors ρ.representation K.toSubgroup) := by
  classical
  rw [coefficientFunctionSpace_eq_map] at hf
  obtain ⟨f₀, ⟨t, rfl⟩, rfl⟩ := hf
  change ∀ (k : K) (g : G),
    coefficientTensorMap ρ t (g * k) = coefficientTensorMap ρ t g at hinv
  change (fun g => coefficientTensorMap ρ t g) ∈ _
  let T := (coefficientTensorAction ρ).comp (MonoidHom.inl G G)
  have hT : IsSmooth T := isSmooth_comp (MonoidHom.inl G G)
    (continuous_id.prodMk continuous_const) (isSmooth_coefficientTensorAction ρ)
  have heq :
      (fun g => coefficientTensorMap ρ (coefficientTensorSourceAverage ρ K hK t) g) =
        (fun g => coefficientTensorMap ρ t g) := by
    rw [coefficientTensorSourceAverage_eq_averageMap]
    funext g
    let φ : CoefficientTensor ρ →ₗ[ℂ] ℂ :=
      (LinearMap.proj g).comp ((LocallyConstant.coeFnₗ ℂ).comp (coefficientTensorMap ρ))
    have := finite_orbit_of_smooth T hT K hK t
    change φ (orbitMean (T.comp K.toSubgroup.subtype) t) = φ t
    refine map_orbitMean_of_forall_eq (T.comp K.toSubgroup.subtype) t φ (φ t) ?_
    intro k
    change coefficientTensorMap ρ (coefficientTensorAction ρ ((k : G), 1) t) g =
      coefficientTensorMap ρ t g
    rw [coefficientTensorMap_action]
    simpa only [inv_one, one_mul] using hinv k g
  rw [← heq]
  exact coefficientTensorSourceAverage_mem_coefficientSpaceFrom ρ K hK t

end Langlands.HarishChandraSchwartz

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

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

/-- The ordinary coinvariant realization of the original actual normalized
standard Jacquet module, with its original radical modulus. -/
def standardOrdinaryJacquetObject (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) :
    SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J) :=
  SmoothRep.of
    (normalizedActionOfModulus ρ.representation (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
      (standardRadicalModulus i ν J))
    (isSmooth_normalizedActionOfModulus ρ.representation (standardUnipotentPoints i ν J)
      (standardLeviPoints i ν J) (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
      (standardRadicalModulus i ν J) isOpen_ker_standardRadicalModulus ρ.isSmooth)

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν J ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B) {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)
  (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
  {b : Coinvariants (smoothContragredient ρ.representation)
      (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
    Coinvariants ρ.representation (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
  (hb : (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing
    ρ.representation ρ.isSmooth b)

include hρ hb in
/-- Every original coefficient tensor has its chosen actual standard constant
term in the coefficient space of that same actual normalized Jacquet module. -/
theorem standardConstantTerm_mem_sameJacquet_coefficientSpace (t : CoefficientTensor ρ) :
    standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) ∈
      coefficientFunctionSpace (standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ) := by
  rw [standardConstantTerm_coefficientTensorMap hG hi hν hζ hB hA hmem ρ hρ hb t]
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ.representation ρ.isSmooth :=
    standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ.representation hρ
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    exact hb.coefficientConstantTerm_mem_coefficientFunctionSpace hAd
      (standardRadicalModulus i ν J) isOpen_ker_standardRadicalModulus ℓ v
  | add s t hs ht =>
    simp only [map_add]
    convert Submodule.add_mem _ hs ht using 1
    rfl

include hρ hb in
/-- Right invariance at one actual Levi level realizes the chosen constant
term as a finite sum of coefficients from precisely that Jacquet fixed space. -/
theorem standardConstantTerm_mem_fixedJacquet_coefficientSpace
    (t : CoefficientTensor ρ) (K : OpenSubgroup (standardLeviPoints i ν J))
    (hK : IsCompact (K : Set (standardLeviPoints i ν J)))
    (hinv : ∀ (k : K) (m : standardLeviPoints i ν J),
      standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) (m * k) =
        standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) m) :
    let Jρ := standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ
    standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) ∈
      coefficientSpaceFrom Jρ.representation (fixedVectors Jρ.representation K.toSubgroup) :=
  mem_coefficientSpaceFrom_fixedVectors_of_rightInvariant
    (standardOrdinaryJacquetObject (i := i) (ν := ν) (J := J) ρ) K hK
    (standardConstantTerm_mem_sameJacquet_coefficientSpace hG hi hν hζ hB hA hmem ρ hρ hb t) hinv

end Langlands.BruhatTits.SpecialCompact
