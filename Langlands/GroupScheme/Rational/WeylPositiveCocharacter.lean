import Langlands.GroupScheme.Rational.NormalizerWeightSupport
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Positive central cocharacters by integral Weyl averaging -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {M : GroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ M) [Mono t.hom.hom.left]

/-- The actual normalizer acts on integral cocharacters by postcomposition. -/
def normalizerCocharacterAction :
    normalizerPoints t →* (cocharacterLattice T ≃ₗ[ℤ] cocharacterLattice T) where
  toFun n := cocharacterAut (normalizingAut t n)
  map_one' := by
    have h : normalizingAut t 1 = Iso.refl T :=
      (isNormalizingPoint_normalizingAut t 1).unique t IsNormalizingPoint.one
    apply LinearEquiv.ext
    intro ν
    simp only [h, cocharacterAut_apply, Iso.refl_hom, Category.comp_id]
    rfl
  map_mul' n m := by
    have h : normalizingAut t (n * m) = normalizingAut t m ≪≫ normalizingAut t n :=
      (isNormalizingPoint_normalizingAut t (n * m)).unique t
        ((isNormalizingPoint_normalizingAut t n).mul (isNormalizingPoint_normalizingAut t m))
    apply LinearEquiv.ext
    intro ν
    simp only [h, cocharacterAut_apply, LinearEquiv.mul_apply, Iso.trans_hom,
      Category.assoc]

/-- Centralizing points act trivially on actual integral cocharacters. -/
theorem normalizerCocharacterAction_eq_one_of_mem_centralizerPoints
    {n : normalizerPoints t}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X) ∈ centralizerPoints t) :
    normalizerCocharacterAction t n = 1 := by
  have h : normalizingAut t n = Iso.refl T :=
    (isNormalizingPoint_normalizingAut t n).unique t hn
  apply LinearEquiv.ext
  intro ν
  change cocharacterAut (normalizingAut t n) ν = ν
  simp only [h, cocharacterAut_apply, Iso.refl_hom, Category.comp_id]

/-- The actual quotient of rational normalizers by centralizers acts on the
integral cocharacter lattice. -/
def relativeWeylCocharacterAction :
    relativeWeylGroup t →* (cocharacterLattice T ≃ₗ[ℤ] cocharacterLattice T) :=
  QuotientGroup.lift _ (normalizerCocharacterAction t) fun _ hn =>
    normalizerCocharacterAction_eq_one_of_mem_centralizerPoints t hn

@[simp] theorem relativeWeylCocharacterAction_mk (n : normalizerPoints t) :
    relativeWeylCocharacterAction t (QuotientGroup.mk n) =
      cocharacterAut (normalizingAut t n) := rfl

/-- The integral character and cocharacter actions of the actual quotient
preserve the original lattice pairing. -/
theorem latticePairing_relativeWeyl (w : relativeWeylGroup t)
    (χ : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing T (relativeWeylCharacterAction t w χ)
        (relativeWeylCocharacterAction t w ν) = latticePairing T χ ν := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact latticePairing_characterAut_cocharacterAut (normalizingAut t n) χ ν

/-- Move a Weyl action from a cocharacter to the inverse action on a character. -/
theorem latticePairing_relativeWeyl_right (w : relativeWeylGroup t)
    (χ : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing T χ (relativeWeylCocharacterAction t w ν) =
      latticePairing T (relativeWeylCharacterAction t w⁻¹ χ) ν := by
  have h := latticePairing_relativeWeyl t w (relativeWeylCharacterAction t w⁻¹ χ) ν
  have hc : relativeWeylCharacterAction t w (relativeWeylCharacterAction t w⁻¹ χ) = χ := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rwa [hc] at h

section Finite

variable [Fintype (relativeWeylGroup t)]

/-- The integral sum of all actual Weyl translates, with no division by the
group order. -/
def relativeWeylCocharacterSum : cocharacterLattice T →ₗ[ℤ] cocharacterLattice T :=
  ∑ w : relativeWeylGroup t, (relativeWeylCocharacterAction t w).toLinearMap

theorem relativeWeylCocharacterSum_apply (ν : cocharacterLattice T) :
    relativeWeylCocharacterSum t ν =
      ∑ w : relativeWeylGroup t, relativeWeylCocharacterAction t w ν := by
  simp only [relativeWeylCocharacterSum, LinearMap.sum_apply]
  rfl

/-- The integral average is fixed by every actual Weyl class. -/
theorem relativeWeylCocharacterSum_fixed (ν : cocharacterLattice T)
    (w : relativeWeylGroup t) :
    relativeWeylCocharacterAction t w (relativeWeylCocharacterSum t ν) =
      relativeWeylCocharacterSum t ν := by
  classical
  simp only [relativeWeylCocharacterSum_apply, map_sum]
  simp_rw [← LinearEquiv.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun _ => rfl)

/-- A stable family of strictly positive characters stays strictly positive
on the integral Weyl average. -/
theorem latticePairing_relativeWeylCocharacterSum_pos
    (Φ : Set (characterLattice T))
    (hΦ : ∀ (w : relativeWeylGroup t) (χ : characterLattice T),
      χ ∈ Φ → relativeWeylCharacterAction t w χ ∈ Φ)
    (ν : cocharacterLattice T)
    (hpos : ∀ χ ∈ Φ, 0 < latticePairing T χ ν)
    (χ : characterLattice T) (hχ : χ ∈ Φ) :
    0 < latticePairing T χ (relativeWeylCocharacterSum t ν) := by
  classical
  rw [relativeWeylCocharacterSum_apply, map_sum]
  apply Finset.sum_pos
  · intro w _
    rw [latticePairing_relativeWeyl_right]
    exact hpos _ (hΦ w⁻¹ χ hχ)
  · exact Finset.univ_nonempty

variable [IsAffineHom M.X.hom]

omit [Fintype (relativeWeylGroup t)] in
include t in
/-- Every root reflection negates its actual integral root character when
the torus is split. -/
theorem IsRelativeReflection.relativeWeylCharacterAction_apply_self
    (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} {w : relativeWeylGroup t}
    (hw : IsRelativeReflection t α w) :
    relativeWeylCharacterAction t w α = -α := by
  apply hT.character_toRat_injective
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  have h := congrArg Subtype.val hw.relativeWeylAction_apply_self
  rw [coe_relativeWeylAction_mk_apply, ratAut_toRat] at h
  exact h.trans (map_neg toRat α).symm

/-- Actual root reflections force the integral Weyl average to annihilate
every actual root. -/
theorem latticePairing_relativeWeylCocharacterSum_eq_zero
    (hT : IsSplitTorus T.toGrp)
    (href : ∀ α ∈ relativeRoots t, ∃ w, IsRelativeReflection t α w)
    (ν : cocharacterLattice T) (α : characterLattice T) (hα : α ∈ relativeRoots t) :
    latticePairing T α (relativeWeylCocharacterSum t ν) = 0 := by
  obtain ⟨w, hw⟩ := href α hα
  have h := latticePairing_relativeWeyl t w α (relativeWeylCocharacterSum t ν)
  rw [hw.relativeWeylCharacterAction_apply_self t hT,
    relativeWeylCocharacterSum_fixed, map_neg, LinearMap.neg_apply] at h
  omega

variable [Smooth M.X.hom] [ConnectedSpace M.X.left]

/-- The Weyl average has an actual central image on every test scheme. -/
theorem relativeWeylCocharacterSum_mem_centralCocharacters
    (hT : IsSplitTorus T.toGrp)
    (href : ∀ α ∈ relativeRoots t, ∃ w, IsRelativeReflection t α w)
    (ν : cocharacterLattice T) :
    relativeWeylCocharacterSum t ν ∈ centralCocharacters t :=
  rootAnnihilatorCentrality k M T hT t _ fun α hα =>
    latticePairing_relativeWeylCocharacterSum_eq_zero t hT href ν α hα

end Finite

section RootSystem

variable [IsAffineHom M.X.hom] [Smooth M.X.hom] [ConnectedSpace M.X.left]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : M ⟶ G) (F : SubgroupFunctor G)
    (hF : (AutomorphicAction.conjugation j).IsStable F)

include hF in
/-- The actual root-system realization and normalization turn any strictly
positive direction for the subgroup support into an actual central one.
The root-system realization remains an explicit input. -/
theorem HasRelativeRootSystem.exists_centralCocharacter_positive
    (hroot : HasRelativeRootSystem t) (hT : IsSplitTorus T.toGrp)
    (ν : cocharacterLattice T)
    (hpos : ∀ χ ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation (t ≫ j)) F, 0 < latticePairing T χ ν) :
    ∃ νc : cocharacterLattice T, νc ∈ centralCocharacters t ∧
      ∀ χ ∈ RelativeRoot.actionWeightSupport
        (AutomorphicAction.conjugation (t ≫ j)) F, 0 < latticePairing T χ νc := by
  let := relativeWeylGroupFintype t hroot
  refine ⟨relativeWeylCocharacterSum t ν,
    relativeWeylCocharacterSum_mem_centralCocharacters t hT
      (fun _ hα => hroot.exists_isRelativeReflection hα) ν, ?_⟩
  apply latticePairing_relativeWeylCocharacterSum_pos t _ _ ν hpos
  intro w χ hχ
  exact (RelativeRoot.relativeWeylCharacterAction_mem_actionWeightSupport_iff j t hF w χ).mpr hχ

end RootSystem

end Langlands.GroupScheme
