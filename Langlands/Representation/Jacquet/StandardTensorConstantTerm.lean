import Langlands.Representation.Jacquet.StandardCasselmanConstantTerm
import Langlands.Representation.Plancherel.CoefficientTensors

/-! # Actual standard constant terms of coefficient tensors via the same Jacquet module -/

noncomputable section

open scoped NNReal TensorProduct

namespace Langlands.Jacquet.StablePairingData

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The constant-term coefficients of one actual pairing, extended linearly to
coefficient tensors. All summands use the same normalized action on the actual
coinvariant module. -/
def coefficientTensorConstantTerm (D : StablePairingData G) (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ)
    (δ : D.M →* ℝ≥0ˣ) : V ⊗[ℂ] SmoothDual ρ →ₗ[ℂ] (D.M → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun v ℓ => D.coefficientConstantTerm ρ b δ ℓ v)
    (by intro v w ℓ; ext m; simp [coefficientConstantTerm])
    (by intro c v ℓ; ext m; simp [coefficientConstantTerm])
    (by intro v ℓ ℓ'; ext m; simp [coefficientConstantTerm])
    (by intro c v ℓ; ext m; simp [coefficientConstantTerm]))

@[simp] theorem coefficientTensorConstantTerm_tmul
    (D : StablePairingData G) (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ)
    (δ : D.M →* ℝ≥0ˣ) (v : V) (ℓ : SmoothDual ρ) :
    D.coefficientTensorConstantTerm ρ b δ (v ⊗ₜ[ℂ] ℓ) = D.coefficientConstantTerm ρ b δ ℓ v := rfl

end Langlands.Jacquet.StablePairingData

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Jacquet Langlands.Plancherel Langlands.HarishChandraSchwartz

namespace Langlands.BruhatTits.SpecialCompact

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
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
  (hB : CompactOpenNormalBasis K0 B) {q : T.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J T q)
  (hmem : ∀ K ∈ B, StandardParabolicBasisMember i ν J q K)
  (ρ : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hρ : ρ.IsAdmissible)
  {b : Coinvariants (smoothContragredient ρ.representation)
      (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
    Coinvariants ρ.representation (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ}
  (hb : (standardCasselmanPairingData hG hi hν hζ hB hA hmem).IsStablePairing
    ρ.representation ρ.isSmooth b)

include hρ hb in
/-- The explicit tensor coefficient of the same actual normalized Jacquet
module is a right-finite constant term of the original coefficient tensor. -/
theorem coefficientTensorConstantTerm_spec (t : CoefficientTensor ρ) :
    IsRightFinite (standardComponentHom hA).range
        ((standardCasselmanPairingData hG hi hν hζ hB hA hmem).coefficientTensorConstantTerm
          ρ.representation b (standardRadicalModulus i ν J) t) ∧
      IsStandardConstantTerm hA (fun g => coefficientTensorMap ρ t g)
        ((standardCasselmanPairingData hG hi hν hζ hB hA hmem).coefficientTensorConstantTerm
          ρ.representation b (standardRadicalModulus i ν J) t) := by
  let D := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : D.Admits ρ.representation ρ.isSmooth :=
    standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem ρ.representation hρ
  have hδ := isOpen_ker_standardRadicalModulus (i := i) (ν := ν) (J := J)
  have hbasis : HasIwahoriContractionBasis D.Nbar D.M D.N :=
    hasIwahoriContractionBasis_standard hi hζ hB hA hmem
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    obtain ⟨Bρ, hBρ, hfBρ⟩ := hb.exists_admissible_coefficientConstantTerm
      hAd (standardRadicalModulus i ν J) hδ hρ hbasis ℓ v
    refine ⟨isRightFinite_of_mem_coefficientFunctionSpace hBρ _
      (standardComponentHom_range_central hA) hfBρ, ?_⟩
    exact isStandardConstantTerm_coefficientConstantTerm hG hi hν hζ hB hA hmem
      ρ.representation hρ hb ℓ v
  | add s t hs ht =>
    simp only [map_add, LocallyConstant.add_apply]
    exact ⟨hs.1.add ht.1, hs.2.add hA ht.2⟩

include hρ hb in
/-- The target's chosen standard constant term equals the explicit tensor
coefficient on the same actual normalized coinvariant action, for every pairing
satisfying the actual stable-pairing property. -/
theorem standardConstantTerm_coefficientTensorMap (t : CoefficientTensor ρ) :
    standardConstantTerm hA (fun g => coefficientTensorMap ρ t g) =
      (standardCasselmanPairingData hG hi hν hζ hB hA hmem).coefficientTensorConstantTerm
        ρ.representation b (standardRadicalModulus i ν J) t := by
  obtain ⟨hR, hCT⟩ := coefficientTensorConstantTerm_spec hG hi hν hζ hB hA hmem ρ hρ hb t
  exact standardConstantTerm_eq hi hζ hA hR hCT

end Langlands.BruhatTits.SpecialCompact
