import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.Rational.DominantHighestWeight

/-! # Star-fixed weights as differences of dominant star-fixed weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k K G)

/-- Root-datum automorphisms preserve the pairing of weights with coroots. -/
theorem pairing_weightEquiv_coroot (e : d.toSplitPinning.rootDatum.Aut)
    (x : characterLattice d.toSplitPinning.torus) (i : d.toSplitPinning.rootIndex) :
    d.toSplitPinning.rootDatum.toLinearMap (e.weightEquiv x)
        (d.toSplitPinning.rootDatum.coroot (e.indexEquiv i)) =
      d.toSplitPinning.rootDatum.toLinearMap x (d.toSplitPinning.rootDatum.coroot i) := by
  have h := RootPairing.Equiv.coroot'_weightEquiv e i x
  simpa only [RootPairing.coroot', LinearMap.flip_apply] using h

/-- A weight fixed by an automorphism has the same pairing with a coroot and with its
image. -/
theorem pairing_coroot_indexEquiv_of_fixed (e : d.toSplitPinning.rootDatum.Aut)
    {lam : characterLattice d.toSplitPinning.torus} (hfix : e.weightEquiv lam = lam)
    (i : d.toSplitPinning.rootIndex) :
    d.toSplitPinning.rootDatum.toLinearMap lam
        (d.toSplitPinning.rootDatum.coroot (e.indexEquiv i)) =
      d.toSplitPinning.rootDatum.toLinearMap lam (d.toSplitPinning.rootDatum.coroot i) := by
  conv_lhs => rw [← hfix]
  exact d.pairing_weightEquiv_coroot e lam i

/-- The sum of two dominant weights is dominant. -/
theorem isDominantWeight_add {lam mu : characterLattice d.toSplitPinning.torus}
    (hl : d.toSplitPinning.IsDominantWeight lam) (hm : d.toSplitPinning.IsDominantWeight mu) :
    d.toSplitPinning.IsDominantWeight (lam + mu) := fun a => by
  rw [map_add, LinearMap.add_apply]
  exact add_nonneg (hl a) (hm a)

variable (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)

/-- The positive part `∑ max(⟨λ, α_a^∨⟩, 0) ϖ_a` of a weight in the fundamental-weight basis. -/
def dominantPart (lam : characterLattice d.toSplitPinning.torus) :
    characterLattice d.toSplitPinning.torus :=
  (Langlands.RootDatum.fundamentalWeightBasis d.toSplitPinning.rootDatum d.toSplitPinning.base
    hspan).equivFun.symm
      (fun a => max (d.toSplitPinning.rootDatum.toLinearMap lam
        (d.toSplitPinning.rootDatum.coroot a)) 0)

theorem pairing_dominantPart (lam : characterLattice d.toSplitPinning.torus)
    (a : d.toSplitPinning.base.support) :
    d.toSplitPinning.rootDatum.toLinearMap (d.dominantPart hspan lam)
        (d.toSplitPinning.rootDatum.coroot a) =
      max (d.toSplitPinning.rootDatum.toLinearMap lam (d.toSplitPinning.rootDatum.coroot a)) 0 := by
  classical
  rw [← Langlands.RootDatum.fundamentalWeightBasis_repr d.toSplitPinning.rootDatum
    d.toSplitPinning.base hspan, ← Module.Basis.equivFun_apply, dominantPart,
    LinearEquiv.apply_symm_apply]

theorem isDominantWeight_dominantPart (lam : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.IsDominantWeight (d.dominantPart hspan lam) := fun a => by
  rw [d.pairing_dominantPart hspan lam a]
  exact le_max_right _ _

theorem isDominantWeight_dominantPart_sub (lam : characterLattice d.toSplitPinning.torus) :
    d.toSplitPinning.IsDominantWeight (d.dominantPart hspan lam - lam) := fun a => by
  rw [map_sub, LinearMap.sub_apply, d.pairing_dominantPart hspan lam a, sub_nonneg]
  exact le_max_left _ _

variable [LocallyOfFiniteType G.X.hom]

/-- Star-fixed weights are closed under subtraction. -/
theorem isStarFixedWeight_sub {lam mu : characterLattice d.toSplitPinning.torus}
    (hl : d.IsStarFixedWeight lam) (hm : d.IsStarFixedWeight mu) :
    d.IsStarFixedWeight (lam - mu) := fun σ => by
  rw [map_sub, hl σ, hm σ]

theorem isStarFixedWeight_dominantPart {lam : characterLattice d.toSplitPinning.torus}
    (hfix : d.IsStarFixedWeight lam) : d.IsStarFixedWeight (d.dominantPart hspan lam) := by
  classical
  intro σ
  set e := (d.starAction σ).val with he
  have hbased : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support := (d.starAction σ).2
  apply (Langlands.RootDatum.fundamentalWeightBasis d.toSplitPinning.rootDatum
    d.toSplitPinning.base hspan).ext_elem
  intro i
  rw [Langlands.RootDatum.fundamentalWeightBasis_repr,
    Langlands.RootDatum.fundamentalWeightBasis_repr]
  have hj : e.indexEquiv.symm (i : d.toSplitPinning.rootIndex) ∈ d.toSplitPinning.base.support :=
    (hbased _).mpr (by rw [Equiv.apply_symm_apply]; exact i.2)
  set j : d.toSplitPinning.base.support := ⟨_, hj⟩ with hjdef
  have hij : (i : d.toSplitPinning.rootIndex) = e.indexEquiv j := by
    rw [hjdef]; exact (Equiv.apply_symm_apply _ _).symm
  rw [hij, d.pairing_weightEquiv_coroot e, d.pairing_dominantPart hspan lam j,
    d.pairing_dominantPart hspan lam ⟨e.indexEquiv j, by rw [← hij]; exact i.2⟩]
  congr 1
  exact (d.pairing_coroot_indexEquiv_of_fixed e (hfix σ) j).symm

include hspan in
/-- Every star-fixed weight is a difference of two dominant star-fixed weights. -/
theorem exists_dominant_sub {lam : characterLattice d.toSplitPinning.torus}
    (hfix : d.IsStarFixedWeight lam) :
    ∃ a b : characterLattice d.toSplitPinning.torus,
      d.toSplitPinning.IsDominantWeight a ∧ d.toSplitPinning.IsDominantWeight b ∧
        d.IsStarFixedWeight a ∧ d.IsStarFixedWeight b ∧ lam = a - b :=
  ⟨d.dominantPart hspan lam, d.dominantPart hspan lam - lam,
    d.isDominantWeight_dominantPart hspan lam, d.isDominantWeight_dominantPart_sub hspan lam,
    d.isStarFixedWeight_dominantPart hspan hfix,
    d.isStarFixedWeight_sub (d.isStarFixedWeight_dominantPart hspan hfix) hfix, by abel⟩

end Langlands.GroupScheme.GaloisPinningData
