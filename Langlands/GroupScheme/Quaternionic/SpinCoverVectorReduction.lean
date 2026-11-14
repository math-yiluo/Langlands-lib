import Langlands.GroupScheme.Quaternionic.SpinCoverIndexComparison
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaWeightMultiplicity
import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationStatement
import Langlands.GroupScheme.OrthogonalMatrix.NumberedVectorBasisDescent
import Langlands.GroupScheme.Torus.TowerCharacterDescent
import Langlands.GroupScheme.SimplyConnected.SpinCoverVectorWeightsStatement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Reduction of aligned spin vector weights to split representation inputs -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

local instance vectorWeightsReductionAffine {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ inferInstance

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

/-- The actual character family, root equations and original division-algebra
weight multiplicities required by the host spin-cover vector statement. -/
def HasSpinVectorWeights (d : TitsIndexData G) {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hn : 4 ≤ n) {D : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    {m : ℕ} (degree : ℕ) (σ : Quaternionic.FirstKindInvolution K D)
    (q : σ.QuadraticForms (Fin m)) (π : G ⟶ σ.isometryGroup q) : Prop :=
  ∃ ε : Fin n → characterLattice
      ((CommGroupScheme.baseChange
        (algebraBaseMap K (SeparableClosure K))).obj d.pinning.torus),
    (∀ (a : d.Vertex) (h : (e a).val + 1 < n),
      d.pinning.rootDatum.root a.val = ε (e a) - ε ⟨(e a).val + 1, h⟩) ∧
    (∀ (a : d.Vertex) (h : (e a).val + 1 = n),
      d.pinning.rootDatum.root a.val =
        ε ⟨n - 2, by omega⟩ + ε ⟨n - 1, by omega⟩) ∧
    (∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ α : d.pinning.rootIndex,
      d.pinning.rootDatum.root α = (s : ℤ) • ε i + (t : ℤ) • ε j) ∧
    ∀ (ν : cocharacterLattice d.splitTorus) (c : ℤ),
      Nat.card {p : Fin n × ℤˣ //
          (p.2 : ℤ) * latticePairing d.splitTorus
            ((characterLattice.baseChangeEquiv
                (algebraBaseMap K (SeparableClosure K)) d.splitTorus
                d.maximalSplit.1.1).symm
              ((CommGroupScheme.baseChange
                  (algebraBaseMap K (SeparableClosure K))).map d.torusMap ≫
                ε p.1)) ν = c} =
        degree * Module.finrank D (σ.cocharacterWeightSpace q
          (CommGroupScheme.groupHom ν ≫ d.splitInclusion ≫ π) c)

end TitsIndexData

namespace Quaternionic.OrthogonalMorita

/-- A character eigenbasis computes signed multiplicities after two descents
and restriction along an actual torus map. -/
theorem weight_card_of_descended_eigenbasis
    {K F L D : Type u} [Field K] [Field F] [Field L] [Algebra K L]
    [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    {m n degree : ℕ} {sigma : FirstKindInvolution K D}
    {q : sigma.QuadraticForms (Fin m)}
    (mor : OrthogonalMoritaComparison sigma q L degree n)
    (hdegree : 0 < degree) (hdim : finrank K D = degree ^ 2)
    (b0 : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (b1 : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of F))
    (S : CommGroupScheme (Spec (CommRingCat.of K))) (hS : IsSplitTorus S.toGrp)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsSplitTorus T.toGrp)
    (f : (CommGroupScheme.baseChange b0).obj S ⟶ T)
    (rho : ((CommGroupScheme.baseChange b1).obj T).toGrp ⟶
      OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))
    (eps : Fin n → characterLattice ((CommGroupScheme.baseChange b1).obj T))
    (b : Basis (Fin n × ℤˣ) L ((Fin n ⊕ Fin n) → L))
    (hb : OrthogonalMatrix.IsCharacterEigenbasis rho
      (fun a : Fin n × ℤˣ => (a.2 : ℤ) • eps a.1) b)
    (nu : cocharacterLattice S)
    (f0 : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ sigma.isometryGroup q)
    (hf : Dynamic.baseChangeCocharacter (algebraBaseMap K L) f0 ≫ mor.groupIso.hom =
      CommGroupScheme.groupHom (cocharacterLattice.baseChange b1 T
        (cocharacterLattice.baseChange b0 S nu ≫ f)) ≫ rho)
    (c : ℤ) :
    Nat.card {a : Fin n × ℤˣ // (a.2 : ℤ) * latticePairing S
      (characterLattice.descendRestrictFamilyTower b0 b1 S hS T hT f eps a.1) nu = c} =
      degree * finrank D (sigma.cocharacterWeightSpace q f0 c) := by
  exact (signed_weight_card_descendFamily_tower b0 b1 S hS T hT f eps nu c).trans
    (weight_card_of_characterBasis mor hdegree hdim f0
      ((CommGroupScheme.baseChange b1).obj T)
      (cocharacterLattice.baseChange b1 T (cocharacterLattice.baseChange b0 S nu ≫ f))
      rho hf (fun a : Fin n × ℤˣ => (a.2 : ℤ) • eps a.1) b hb c)

end Quaternionic.OrthogonalMorita

section SuppliedComparison

variable {K L D : Type u} [Field K] [Field L]
  [Algebra K L] [Algebra (SeparableClosure K) L]
  [IsScalarTower K (SeparableClosure K) L]
  [Algebra.IsAlgebraic (SeparableClosure K) L]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {m n degree : ℕ} {sigma : Quaternionic.FirstKindInvolution K D}
  {q : sigma.QuadraticForms (Fin m)}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (e : d.Vertex ≃ Fin n) (hn : 4 ≤ n)
  (mor : Quaternionic.OrthogonalMoritaComparison sigma q L degree n)
  {pi : G ⟶ sigma.isometryGroup q} (hpi : sigma.IsSpinCover q pi)

local instance hostReductionOrthogonalSmooth :
    Smooth (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of L)

local instance hostReductionOrthogonalAffine :
    IsAffineHom (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of L)

/-- A supplied character eigenbasis with the numbered root equations computes
all of the host weights on the original division-algebra representation. -/
theorem spinCoverVectorWeights_of_basis
    (hdegree : 0 < degree) (hdim : finrank K D = degree ^ 2)
    (eps : Fin n → characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap (SeparableClosure K) L)).obj
        d.pinning.toSplitPinning.torus))
    (hroots : d.pinning.toSplitPinning.NumberedRootFamily (by omega : 2 ≤ n) e
      (characterLattice.descendFamily (algebraBaseMap (SeparableClosure K) L)
        d.pinning.toSplitPinning.torus d.pinning.toSplitPinning.isSplitTorus eps))
    (b : Basis (Fin n × ℤˣ) L ((Fin n ⊕ Fin n) → L))
    (hb : OrthogonalMatrix.IsCharacterEigenbasis
      (Quaternionic.OrthogonalMorita.splitCoverTowerTorusMap
        (F := SeparableClosure K) mor hpi d.pinning.torus d.pinning.inclusion)
      (fun a : Fin n × ℤˣ => (a.2 : ℤ) • eps a.1) b) :
    d.HasSpinVectorWeights e hn degree sigma q pi := by
  refine ⟨characterLattice.descendFamily (algebraBaseMap (SeparableClosure K) L)
    d.pinning.toSplitPinning.torus d.pinning.toSplitPinning.isSplitTorus eps,
    hroots.1, hroots.2.1, hroots.2.2, ?_⟩
  intro nu c
  exact Quaternionic.OrthogonalMorita.weight_card_of_descended_eigenbasis
    mor hdegree hdim
    (algebraBaseMap K (SeparableClosure K)) (algebraBaseMap (SeparableClosure K) L)
    d.splitTorus d.maximalSplit.1.1 d.pinning.toSplitPinning.torus
    d.pinning.toSplitPinning.isSplitTorus
    ((CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map d.torusMap)
    (Quaternionic.OrthogonalMorita.splitCoverTowerTorusMap
      (F := SeparableClosure K) mor hpi d.pinning.torus d.pinning.inclusion)
    eps b hb nu (CommGroupScheme.groupHom nu ≫ d.splitInclusion ≫ pi)
    (d.spinVectorCocharacter_square L mor hpi nu) c

include mor hpi in
/-- Supplied Morita coordinates and the numbered-cover input yield the exact
host data without choosing a concrete algebraic-closure implementation. -/
theorem spinCoverVectorWeights_of_comparison
    (hNumbered : OrthogonalMatrix.NumberedCoverVectorStatement.{u})
    (hdegree : 0 < degree) (hdim : finrank K D = degree ^ 2)
    (hcartan : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (halign : ∀ v : d.Vertex, (e v).val = 0 →
      d.FundamentalWeightTrivialOnKernel v pi) :
    d.HasSpinVectorWeights e hn degree sigma q pi := by
  classical
  let p := d.pinning.toSplitPinning
  have halignL := Quaternionic.OrthogonalMorita.splitCoverTower_numbered_alignment
    mor hpi p e (fun v hv =>
      (d.fundamentalWeightTrivialOnKernel_iff v pi).mp (halign v hv))
  obtain ⟨eps, hroots, b, hb⟩ := p.numberedVectorBasis_baseChange_of_statement
    hNumbered hn
    (Quaternionic.OrthogonalMorita.isSimplyConnected_splitCoverTower hpi
      (SeparableClosure K))
    (Quaternionic.OrthogonalMorita.splitCoverTower mor hpi (SeparableClosure K))
    (Quaternionic.OrthogonalMorita.isCentralIsogeny_splitCoverTower mor hpi
      (SeparableClosure K)) e hcartan halignL
  exact spinCoverVectorWeights_of_basis d e hn mor hpi hdegree hdim eps hroots b hb

end SuppliedComparison

end Langlands.GroupScheme
