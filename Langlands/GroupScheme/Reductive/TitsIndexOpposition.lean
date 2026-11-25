import Langlands.LinearAlgebra.RootDatumNegation
import Langlands.GroupScheme.Reductive.TitsIndexIndependenceProof

/-! # Opposition preserves the actual distinguished vertices -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme

namespace GaloisPinningData

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Retain the actual torus and root datum, and choose root vectors for the
negative base. -/
def opposite (p : GaloisPinningData k E G) : GaloisPinningData k E G :=
  { p with
    base := p.base.map (negAut p.rootDatum)
    pinning := RootPinning.ofSplitMaximalTorus p.isConnectedReductive p.isSplitTorus
      _ p.isMaximalTorus p.rootDatum p.isRootDatum (p.base.map (negAut p.rootDatum)) }

end GaloisPinningData

namespace TitsIndexData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- Opposite compatible choices keep both tori and negate the positive
cocharacter while replacing the absolute base by its negative. -/
def opposite : TitsIndexData G where
  isSemisimple := d.isSemisimple
  pinning := d.pinning.opposite
  maximalTorus := d.maximalTorus
  splitTorus := d.splitTorus
  splitInclusion := d.splitInclusion
  maximalSplit := d.maximalSplit
  torusMap := d.torusMap
  square := d.square
  positiveCocharacter := -d.positiveCocharacter
  generic := by
    intro α hα
    rw [map_neg]
    exact neg_ne_zero.mpr (d.generic α hα)
  compatible := by
    intro a ha
    change (d.pinning.base.map (negAut d.pinning.rootDatum)).IsPos a ↔
      0 < latticePairing d.splitTorus (d.rootRestriction a) (-d.positiveCocharacter)
    rw [isPos_map_negAut, d.compatible a ha, map_neg]
    change (¬ 0 < latticePairing d.splitTorus (d.rootRestriction a)
      d.positiveCocharacter) ↔
        0 < -latticePairing d.splitTorus (d.rootRestriction a) d.positiveCocharacter
    have hne := d.generic _ (TitsIndexIndependence.rootRestriction_mem_relativeRoots d ha)
    omega

/-- Negation of an absolute root negates its actual restriction. -/
theorem rootRestriction_negAut (a : d.pinning.rootIndex) :
    d.rootRestriction ((negAut d.pinning.rootDatum).indexEquiv a) =
      -d.rootRestriction a := by
  have hroot :
      d.pinning.rootDatum.root ((negAut d.pinning.rootDatum).indexEquiv a) =
        -d.pinning.rootDatum.root a :=
    ((negAut d.pinning.rootDatum).root_weightMap_apply _ _ a).symm
  change (characterLattice.baseChangeEquiv (algebraBaseMap k (SeparableClosure k))
      d.splitTorus d.maximalSplit.1.1).symm
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map d.torusMap ≫
      d.pinning.rootDatum.root ((negAut d.pinning.rootDatum).indexEquiv a)) = _
  rw [hroot, Preadditive.comp_neg, AddEquiv.map_neg]
  rfl

/-- The canonical based representative of minus identity on the full lattices. -/
def oppositionAut : d.pinning.toSplitPinning.basedRootDatumAut :=
  d.pinning.toSplitPinning.basedRootDatumProjection
    (negAut d.pinning.toSplitPinning.rootDatum)

/-- Opposition commutes with every based automorphism of the full root datum. -/
theorem oppositionAut_comm (e : d.pinning.toSplitPinning.basedRootDatumAut) :
    d.oppositionAut * e = e * d.oppositionAut := by
  have h := congrArg d.pinning.toSplitPinning.basedRootDatumProjection
    (negAut_comm d.pinning.toSplitPinning.rootDatum e.val)
  change d.pinning.toSplitPinning.basedRootDatumProjection
      (negAut d.pinning.toSplitPinning.rootDatum) * e =
    e * d.pinning.toSplitPinning.basedRootDatumProjection
      (negAut d.pinning.toSplitPinning.rootDatum)
  simpa only [map_mul, SplitPinning.basedRootDatumProjection_of_based] using h

/-- The canonical opposition automorphism is involutive. -/
theorem oppositionAut_mul_self : d.oppositionAut * d.oppositionAut = 1 := by
  change d.pinning.toSplitPinning.basedRootDatumProjection
      (negAut d.pinning.toSplitPinning.rootDatum) *
    d.pinning.toSplitPinning.basedRootDatumProjection
      (negAut d.pinning.toSplitPinning.rootDatum) = 1
  rw [← map_mul, negAut_mul_self, map_one]

/-- The canonical opposition preserves zero restriction of every absolute root. -/
theorem rootRestriction_opposition_eq_zero_iff (a : d.pinning.rootIndex) :
    d.rootRestriction (d.oppositionAut.val.indexEquiv a) = 0 ↔
      d.rootRestriction a = 0 := by
  obtain ⟨g, φ, ε, hg, he, hb, hz⟩ :=
    TitsIndexIndependence.exists_based_conj d d.opposite
  change d.pinning.toSplitPinning.rootDatum.Aut at ε
  obtain ⟨w, hw, hwχ⟩ := StarActionIndependence.exists_weyl_of_isNormalizingPoint
    d.pinning.toSplitPinning hg
  have hew : ε = w := by
    apply RootPairing.Equiv.weightHom_injective d.pinning.rootDatum
    ext χ
    exact (he χ).trans (hwχ χ).symm
  have hε : ε ∈ d.pinning.rootDatum.weylGroup := hew ▸ hw
  let θ : d.pinning.toSplitPinning.basedRootDatumAut :=
    ⟨negAut d.pinning.toSplitPinning.rootDatum * ε, fun j =>
      (hb j).trans (mem_support_map_negAut d.pinning.rootDatum d.pinning.base
        (ε.indexEquiv j))⟩
  have hθ : θ.val * (negAut d.pinning.toSplitPinning.rootDatum)⁻¹ ∈
      d.pinning.rootDatum.weylGroup := by
    have hmul : θ.val * (negAut d.pinning.toSplitPinning.rootDatum)⁻¹ = ε := by
      rw [negAut_inv]
      change (negAut d.pinning.toSplitPinning.rootDatum * ε) *
        negAut d.pinning.toSplitPinning.rootDatum = ε
      rw [negAut_comm, mul_assoc, negAut_mul_self, mul_one]
    rw [hmul]
    exact hε
  have hθopp : θ = d.oppositionAut :=
    d.pinning.toSplitPinning.basedRootDatum_representative_unique
      (negAut d.pinning.toSplitPinning.rootDatum) θ d.oppositionAut hθ
      (d.pinning.toSplitPinning.basedRootDatumProjection_correction _)
  rw [← hθopp]
  change d.rootRestriction ((negAut d.pinning.rootDatum).indexEquiv
    (ε.indexEquiv a)) = 0 ↔ d.rootRestriction a = 0
  rw [d.rootRestriction_negAut, neg_eq_zero]
  exact (hz a).symm

/-- Opposition as a permutation of the actual simple vertices. -/
def opposition : d.Vertex ≃ d.Vertex :=
  d.oppositionAut.val.indexEquiv.subtypeEquiv d.oppositionAut.property

theorem opposition_involutive (a : d.Vertex) : d.opposition (d.opposition a) = a := by
  apply Subtype.ext
  exact congrArg
    (fun e : d.pinning.toSplitPinning.basedRootDatumAut => e.val.indexEquiv a.val)
    d.oppositionAut_mul_self

theorem opposition_cartan (a b : d.Vertex) :
    d.cartan (d.opposition a) (d.opposition b) = d.cartan a b :=
  RootPairing.Hom.pairing d.oppositionAut.val.toHom

theorem opposition_mem_zero_iff (a : d.Vertex) :
    d.opposition a ∈ d.zeroVertices ↔ a ∈ d.zeroVertices :=
  d.rootRestriction_opposition_eq_zero_iff a.val

theorem opposition_mem_distinguished_iff (a : d.Vertex) :
    d.opposition a ∈ d.distinguishedVertices ↔ a ∈ d.distinguishedVertices :=
  not_congr (d.opposition_mem_zero_iff a)

theorem opposition_star (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex) :
    d.opposition (d.star σ a) = d.star σ (d.opposition a) := by
  apply Subtype.ext
  exact congrArg
    (fun e : d.pinning.toSplitPinning.basedRootDatumAut => e.val.indexEquiv a.val)
    (d.oppositionAut_comm (d.pinning.starAction σ))

/-- Canonical opposition is an automorphism of the actual Tits index,
including every element of its absolute Galois star action. -/
def oppositionIndexEquiv : TitsIndexEquiv d d where
  vertices := d.opposition
  cartan_eq := d.opposition_cartan
  zero_iff := fun a => (d.opposition_mem_zero_iff a).symm
  star_eq := d.opposition_star

end TitsIndexData

end Langlands.GroupScheme
