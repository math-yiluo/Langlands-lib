import Langlands.GroupScheme.Reductive.CanonicalRhoFrobeniusDetection
import Langlands.GroupScheme.Rational.TorusUnipotence.StandardUnipotentAction
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The root-count upper bound for the canonical induced space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj DirectSum

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace Standard

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i)

include hG hT hi

/-- The Lie dimension of the actual standard unipotent group is the number
of relative roots positive for its defining cocharacter. -/
theorem finrank_lieKernel_unipotentScheme_empty :
    Module.finrank k (Additive (lieKernel (unipotentScheme i ν ∅) k)) =
      Nat.card (positiveRelativeRoots i ν) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let : Smooth (unipotentScheme i ν ∅).X.hom :=
    smooth_unipotentScheme_empty i ν hT
  let b := unipotentAction i ν hT
  let W := RelativeRoot.actionWeightSpace b
  let S := {χ : characterLattice T // W χ ≠ ⊥}
  let e : S ≃ positiveRelativeRoots i ν :=
    Equiv.subtypeEquivRight (actionWeightSpace_unipotentAction_ne_bot_iff i ν hT)
  let : Finite (positiveRelativeRoots i ν) :=
    (hT.finite_positiveRelativeRoots i ν).to_subtype
  let : Finite S := Finite.of_equiv _ e.symm
  let : Fintype S := Fintype.ofFinite S
  have hdim (χ : S) : Module.finrank k (W χ) = 1 := by
    have hχ : χ.val ∈ positiveRelativeRoots i ν :=
      (actionWeightSpace_unipotentAction_ne_bot_iff i ν hT χ.val).mp χ.property
    change Module.finrank k
      (RelativeRoot.actionWeightSpace (unipotentAction i ν hT) χ.val) = 1
    rw [finrank_actionWeightSpace_unipotentAction i ν hT hχ]
    obtain ⟨l⟩ := splitRootLieLine k G hG T hT i hi χ.val hχ.1
    rw [← l.finrank_eq, Module.finrank_self]
  let : ∀ χ : S, Module.Free k (W χ) :=
    fun χ => Module.Free.of_divisionRing k (W χ)
  let : ∀ χ : S, Module.Finite k (W χ) :=
    fun χ => Module.finite_of_finrank_eq_succ (hdim χ)
  have hI : DirectSum.IsInternal (fun χ : S => W χ) :=
    DirectSum.isInternal_ne_bot_iff.mpr
      (RelativeRoot.isInternal_actionWeightSpace b hT)
  calc
    Module.finrank k (Additive (lieKernel (unipotentScheme i ν ∅) k)) =
        Module.finrank k (⨁ (χ : S), W χ) :=
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun χ : S => W χ)) hI).finrank_eq.symm
    _ = ∑ χ : S, Module.finrank k (W χ) := Module.finrank_directSum k _
    _ = Nat.card S := by simp [hdim, Nat.card_eq_fintype_card]
    _ = Nat.card (positiveRelativeRoots i ν) := Nat.card_congr e

end Standard

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) [Fintype p.rootIndex]
    (hspan : p.rootDatum.corootSpan ℤ = ⊤)

local notation "ν₀" =>
  p.rootDatum.Polarization (Langlands.IntegralWeylVector.rho p.rootDatum p.base hspan)
local notation "U" => Standard.unipotentScheme p.inclusion (-ν₀) ∅

/-- Negating actual roots identifies the supplied positive-root indices
with the positive roots of the opposite-rho chamber. -/
def oppositeRhoPositiveRootEquiv :
    {s : p.rootIndex // p.base.IsPos s} ≃
      positiveRelativeRoots p.inclusion (-ν₀) :=
  Equiv.ofBijective
    (fun s => ⟨-p.rootDatum.root s, by
      refine ⟨p.isRootDatum.neg_mem_roots (p.root_mem_relativeRoots s), ?_⟩
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using
        (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
          p.base hspan s).mpr s.property⟩)
    (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact p.rootDatum.root.injective (neg_injective (congrArg Subtype.val h))
      · intro a
        have hneg := p.isRootDatum.neg_mem_roots a.property.1
        obtain ⟨s, hs⟩ : ∃ s, p.rootDatum.root s = -a.val := by
          rwa [← p.isRootDatum.2.1, Set.mem_range] at hneg
        have hpos : p.base.IsPos s := by
          apply (p.isRootDatum.latticePairing_root_polarization_rho_pos_iff
            p.base hspan s).mp
          rw [hs]
          simpa only [map_neg, LinearMap.neg_apply] using a.property.2
        exact ⟨⟨s, hpos⟩, Subtype.ext (by simp only [hs, neg_neg])⟩)

/-- The actual opposite-rho unipotent Lie dimension equals the number of
positive roots in the supplied root datum. -/
theorem finrank_lieKernel_oppositeRho :
    Module.finrank k (Additive (lieKernel U k)) =
      Nat.card {s : p.rootIndex // p.base.IsPos s} := by
  rw [Standard.finrank_lieKernel_unipotentScheme_empty p.inclusion (-ν₀)
    p.isConnectedReductive p.isSplitTorus p.isMaximalTorus]
  exact Nat.card_congr (p.oppositeRhoPositiveRootEquiv hspan).symm

variable [IsAlgClosed k]

/-- The entire canonical covariant space satisfies the root-count
Steinberg upper bound at the same Frobenius height. -/
theorem finrank_canonicalRhoCovariantSubspace_le_rootCount
    (q : ℕ) [ExpChar k q] (r : ℕ) :
    Module.finrank k (p.canonicalRhoCovariantSubspace hspan (q ^ r - 1)) ≤
      (q ^ r) ^ Nat.card {s : p.rootIndex // p.base.IsPos s} := by
  have h := p.finrank_canonicalRhoCovariantSubspace_le hspan q r
  rwa [p.finrank_lieKernel_oppositeRho hspan] at h

end SplitPinning

end Langlands.GroupScheme
