import Langlands.Representation.Aubert.General.CartanCentralSupport
import Langlands.Representation.Aubert.General.RationalCartanSupportReduction
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Bounded actual Cartan coordinates give full central-quotient support -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Vanishing simple-root coordinates force a uniformizer power to lie in the
full abstract center. Genericity and root negation are the only root inputs. -/
theorem uniformizerPowers_mem_center_of_simpleRootPairing_eq_zero
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (x : cocharacterLattice S) (hx : ∀ β : SimpleRoot i ν, simpleRootPairing i ν β x = 0) :
    uniformizerPowers i (.ofAdd x) ∈ Subgroup.center (rationalPoints G) := by
  let ev : characterLattice S →+ ℤ := ((latticePairing S).flip x).toAddMonoidHom
  have hclosure : AddSubgroup.closure (simpleRelativeRoots i ν) ≤ ev.ker := by
    apply (AddSubgroup.closure_le _).mpr
    intro α hα
    exact hx ⟨α, hα⟩
  have hcentral : IsCentral (CommGroupScheme.groupHom x ≫ i) :=
    rootAnnihilatorCentrality F G S hS i x (fun α hα =>
      hclosure (relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots i ν hν hneg hα))
  exact hcentral.map_mem_center
    ((Gm.affinePointsEquiv (𝟙 _)).symm (SplitTorusValuation.uniformizerUnit F))

/-- Actual simple-root coordinates determine uniformizer classes modulo the
full abstract point-group center. -/
def RationalCartanDetectionModuloCenter : Prop :=
  CartanDetectionModulo (fun β x => simpleRootPairing i ν β x)
    (fun x => QuotientGroup.mk' (Subgroup.center (rationalPoints G))
      (uniformizerPowers i (.ofAdd x)))

/-- Actual simple-root coordinates determine the class of a uniformizer power
modulo the full abstract point-group center. -/
theorem cartanDetectionModulo_center
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) :
    RationalCartanDetectionModuloCenter i ν := by
  intro x y hxy
  dsimp only at hxy
  apply QuotientGroup.eq.mpr
  have hz := uniformizerPowers_mem_center_of_simpleRootPairing_eq_zero i ν hS hν hneg
    (y - x) (fun β => by rw [map_sub, hxy β, sub_self])
  simpa only [sub_eq_neg_add, ofAdd_add, ofAdd_neg, map_mul, map_inv] using hz

variable [IsAffine G.X.left]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A bounded actual Cartan expression gives compact support on the full point
center quotient. The root-system input is retained explicitly. -/
theorem hasCompactSupport_centerQuotient_of_cartanSupportBound
    [Mono i.hom.hom.left] [IsTopologicalGroup (rationalPoints G)]
    [T2Space (rationalPoints G)] {E : Type v} [Zero E]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (F₀ : Finset (centralizerPoints i))
    (hcover : ∀ g : rationalPoints G,
      ∃ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i) (a : rationalPoints S.toGrp),
        k₁ ∈ K ∧ k₂ ∈ K ∧ f ∈ F₀ ∧
        a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) ∧
        g = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂)
    (φ : rationalPoints G ⧸ Subgroup.center (rationalPoints G) → E)
    (hbound : RationalCartanSupportBound i ν K F₀ (fun g => φ (QuotientGroup.mk g))) :
    HasCompactSupport φ := by
  have := hG.smooth
  have := hG.connectedSpace
  have := (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν).to_subtype
  have : IsClosed (Subgroup.center (rationalPoints G) : Set (rationalPoints G)) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set (rationalPoints G)))
  obtain ⟨B, hB⟩ := hbound
  apply hasCompactSupport_of_bounded_cartan_image
    (QuotientGroup.mk' (Subgroup.center (rationalPoints G))) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective _) (K : Set (rationalPoints G)) hK
    (Subtype.val '' (F₀ : Set (centralizerPoints i))) (F₀.finite_toSet.image _)
    (fun x => uniformizerPowers i (.ofAdd x)) (fun β x => simpleRootPairing i ν β x)
    (cartanDetectionModulo_center i ν hi.isSplitSubtorus.1 hν
      (fun _ hα => hRoots.neg_mem_relativeRoots i hi.isSplitSubtorus.1 hα)) 0 B φ
  intro g hg
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hrep⟩ := hcover g
  obtain ⟨x, rfl, hx⟩ := exists_cocharacter_of_mem_CAplus i ν ha
  have he : rationalPoints.map i (CocharacterUniformizer.latticeSection F S (.ofAdd x)) =
      uniformizerPowers i (.ofAdd x) := rfl
  rw [he] at hrep
  have hxT : uniformizerPowers i (.ofAdd x) ∈ torusPoints i :=
    (mem_torusPoints i _).mpr ⟨CocharacterUniformizer.latticeSection F S (.ofAdd x), rfl⟩
  have hcomm : (f : rationalPoints G) * uniformizerPowers i (.ofAdd x) =
      uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) :=
    (centralizerPoints_le_pointCentralizer i f.property _ hxT).symm
  have hrep' : g = k₁ * uniformizerPowers i (.ofAdd x) * (f : rationalPoints G) * k₂ := by
    rw [mul_assoc k₁, hcomm, ← mul_assoc] at hrep
    exact hrep
  have hupper := hB k₁ k₂ f x hk₁ hk₂ hf hx (by simpa only [← hrep', QuotientGroup.mk'_apply] using hg)
  exact ⟨k₁, hk₁, f, ⟨f, hf, rfl⟩, x, k₂, hk₂,
    fun β => ⟨hx β, hupper β⟩, hrep⟩

/-- The literal finite Cartan covering and uniform bounds give compact support
on the full point center quotient. -/
theorem hasCompactSupport_centerQuotient_of_finiteCartanCovering
    [Mono i.hom.hom.left] [IsTopologicalGroup (rationalPoints G)]
    [T2Space (rationalPoints G)] {E : Type v} [Zero E]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hcover : FiniteCartanCovering F i ν K)
    (φ : rationalPoints G ⧸ Subgroup.center (rationalPoints G) → E)
    (hbound : ∀ F₀ : Finset (centralizerPoints i),
      RationalCartanSupportBound i ν K F₀ (fun g => φ (QuotientGroup.mk g))) :
    HasCompactSupport φ := by
  obtain ⟨F₀, hF₀⟩ := hcover
  exact hasCompactSupport_centerQuotient_of_cartanSupportBound i ν hG hi hν hRoots
    K hK F₀ hF₀ φ (hbound F₀)

end Langlands.Aubert.General
