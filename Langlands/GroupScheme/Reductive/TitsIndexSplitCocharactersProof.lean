import Langlands.GroupScheme.Reductive.TitsIndexSplitCocharactersStatement
import Langlands.GroupScheme.Reductive.TitsIndexStarProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Torus.GaloisInvariantLatticesProof
import Langlands.LinearAlgebra.RootDatumZeroFace
import Langlands.LinearAlgebra.AdjointRootDatum

/-! # The integral maximal split cocharacters from the Tits index -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open TitsIndexStarProof

namespace TitsIndexSplitCocharacters

/-- If `w` fixes a coweight `μ`, then `w * δ` and `δ` act on `μ` in the same way. -/
private theorem coweightEquiv_mul_of_fixed {J X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] (Q : RootDatum J X Y)
    (μ : Y) (w δ : Q.Aut) (h : w.coweightEquiv μ = μ) :
    (w * δ).coweightEquiv μ = δ.coweightEquiv μ := by
  change δ.coweightEquiv (w.coweightEquiv μ) = δ.coweightEquiv μ
  exact congrArg δ.coweightEquiv h

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "bK" => algebraBaseMap k (SeparableClosure k)
local notation "P" => d.pinning.rootDatum
local notation "TK" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) d.pinning.torus

/-- A cocharacter annihilating the simple roots of `Δ₀` annihilates every absolute root
that vanishes on the base change `nuK d` of the generic cocharacter of the index. -/
private theorem zeroRoot_pairing_eq_zero (μ : cocharacterLattice TK)
    (hμ : ∀ a ∈ d.zeroVertices, (P).root' a.val μ = 0)
    {i : d.pinning.rootIndex} (hi : (P).root' i (nuK d) = 0) : (P).root' i μ = 0 := by
  let f := (P).toLinearMap.flip (nuK d)
  let g := (P).toLinearMap.flip μ
  have hker : AddSubmonoid.closure
      ((P).root '' {j | j ∈ d.pinning.base.support ∧ f ((P).root j) = 0}) ≤
        g.toAddMonoidHom.ker.toAddSubmonoid := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨j, ⟨hj, hfj⟩, rfl⟩
    exact hμ ⟨j, hj⟩ ((rootRestriction_eq_zero_iff d j).mpr hfj)
  have hpos {x : characterLattice TK}
      (hx : x ∈ AddSubmonoid.closure ((P).root '' d.pinning.base.support))
      (hzero : f x = 0) : g x = 0 :=
    hker (RootDatumZeroFace.mem_closure_zero_of_mem_closure_nonneg (P).root _ f
      (dominant d) hx hzero)
  rcases d.pinning.base.root_mem_or_neg_mem i with h | h
  · exact hpos h hi
  · have hzero : f (-(P).root i) = 0 := by
      rw [map_neg]
      exact neg_eq_zero.mpr hi
    have hg := hpos h hzero
    rw [map_neg, neg_eq_zero] at hg
    exact hg

/-- Two cocharacters over the separable closure with the same pairings with all absolute
simple roots are equal: the simple roots form a basis of the root lattice, which has
finite index in the character lattice because the group is semisimple. -/
private theorem coweight_eq_of_simple (μ ν : cocharacterLattice TK)
    (h : ∀ a : d.Vertex, (P).root' a.val μ = (P).root' a.val ν) : μ = ν := by
  let hG : IsSemisimple ((GroupScheme.baseChange bK).obj G) :=
    d.isSemisimple.baseChange_of_algebraicExtension
  let := hG.isConnectedReductive.isAffineHom
  have hfinite := hG.finite_quotient_rootSpan d.pinning.isSplitTorus
    d.pinning.isMaximalTorus.2.1 d.pinning.isRootDatum
  apply AdjointRootDatum.injective_fromRootDatum_coweightMap P hfinite
  apply d.pinning.base.toWeightBasisInt.ext
  intro a
  have ha : d.pinning.base.toWeightBasisInt a = (P).rootSpanMem ℤ a := by
    ext
    simp
  rw [ha]
  exact h a

set_option maxHeartbeats 800000 in
/-- On a cocharacter annihilating the simple roots of `Δ₀`, the star automorphism and the
ordinary Galois automorphism of the root datum act in the same way. -/
private theorem coweightEquiv_star_apply (μ : cocharacterLattice TK)
    (hμ : ∀ a ∈ d.zeroVertices, (P).root' a.val μ = 0)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (d.pinning.starAction σ).val.coweightEquiv μ =
      (d.pinning.galoisAction σ).coweightEquiv μ := by
  obtain ⟨w, hw, h⟩ := exists_star_correction d σ
  let Q := d.pinning.toSplitPinning.rootDatum
  have hsub : RootDatumWeylChambers.reflectionSubgroup Q {i | Q.root' i (nuK d) = 0} ≤
      RootDatumWeylChambers.reflectionSubgroup Q {i | Q.root' i μ = 0} := by
    apply Subgroup.closure_mono
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, zeroRoot_pairing_eq_zero d μ hμ hj, rfl⟩
  have hfix : w.coweightEquiv μ = μ :=
    RootDatumBasedCorrection.fixes_coweight Q μ ⟨w, hsub hw⟩
  exact (congrArg (fun θ : Q.Aut => θ.coweightEquiv μ) h).trans
    (coweightEquiv_mul_of_fixed Q μ w (d.pinning.galoisAction σ) hfix)

/-- Every cocharacter of the maximal `k`-torus factors uniquely through the maximal split
torus of the index, which is the largest split subtorus of that torus. -/
private theorem existsUnique_factor (ν : cocharacterLattice d.pinning.torus) :
    ∃! η : cocharacterLattice d.splitTorus, η ≫ d.torusMap = ν := by
  have : IsClosedImmersion d.pinning.inclusion.hom.hom.left := d.maximalTorus.2.1
  have : IsAffineHom d.pinning.torus.toGrp.X.hom := by
    rw [← Over.w d.pinning.inclusion.hom.hom]
    infer_instance
  have : LocallyOfFiniteType d.pinning.torus.toGrp.X.hom := by
    rw [← Over.w d.pinning.inclusion.hom.hom]
    infer_instance
  have : IsAffine d.pinning.torus.toGrp.X.left :=
    isAffine_of_isAffineHom d.pinning.torus.toGrp.X.hom
  have hmax : IsMaximalSplitTorus (CommGroupScheme.groupHom d.torusMap) :=
    IsMaximalSplitTorus.of_comp d.maximalTorus.2.1 (by rw [d.square]; exact d.maximalSplit)
  obtain ⟨f, hf, huniq⟩ := hmax.isLargestSplitSubtorus.2
    (Gm (Spec (CommRingCat.of k))) (CommGroupScheme.groupHom ν) isSplitTorus_gm
  exact ⟨Additive.ofMul f, hf, fun x hx => congrArg Additive.ofMul (huniq x.toMul hx)⟩

/-- The pairing of an absolute root with the base change of `η ≫ d.torusMap` is the pairing
of its restriction to the split torus with `η`. -/
private theorem root'_baseChange (η : cocharacterLattice d.splitTorus)
    (a : d.pinning.rootIndex) :
    (P).root' a (cocharacterLattice.baseChange bK d.pinning.torus (η ≫ d.torusMap)) =
      latticePairing d.splitTorus (d.rootRestriction a) η := by
  change (P).toLinearMap ((P).root a) _ = _
  rw [d.pinning.isRootDatum.1, FaceSimpleRootRestriction.latticePairing_baseChange_comp,
    ← baseChange_rootRestriction, latticePairing_baseChange]

end TitsIndexSplitCocharacters

set_option maxHeartbeats 800000 in
open TitsIndexSplitCocharacters in
/-- The integral cocharacters defined by the Tits-index equations descend uniquely
through the actual maximal split torus. -/
theorem titsIndexSplitCocharacters : TitsIndexSplitCocharactersStatement.{u} := by
  intro k _ G _ _ d b μ
  constructor
  · rintro ⟨η, rfl, -⟩
    refine ⟨fun a ha => ?_, fun σ a => ?_⟩
    · rw [root'_baseChange d, show d.rootRestriction a.val = 0 from ha, map_zero]
      rfl
    · rw [root'_baseChange d, root'_baseChange d]
      exact congrArg (fun a => latticePairing d.splitTorus a η)
        (rootRestriction_star d σ a.val)
  · rintro ⟨hzero, hstar⟩
    let K := SeparableClosure k
    have hfixStar (σ : K ≃ₐ[k] K) : (d.pinning.starAction σ).val.coweightEquiv μ = μ := by
      exact coweight_eq_of_simple d _ _ (fun a => by
        let θ := (d.pinning.starAction σ).val
        calc
          d.pinning.rootDatum.root' a.val (θ.coweightEquiv μ) =
              d.pinning.rootDatum.root' (d.star σ a).val μ := by
            exact (θ.root'_coweightEquiv a.val (θ.coweightEquiv μ)).symm.trans
              (congrArg (d.pinning.rootDatum.root' (d.star σ a).val)
                (θ.coweightEquiv.symm_apply_apply μ))
          _ = d.pinning.rootDatum.root' a.val μ := hstar σ a)
    have hfix (σ : K ≃ₐ[k] K) :
        cocharacterLattice.galoisRepresentation k K d.pinning.torus σ μ = μ := by
      have hd := (coweightEquiv_star_apply d μ hzero σ⁻¹).symm.trans (hfixStar σ⁻¹)
      change cocharacterLattice.galoisRepresentation k K d.pinning.torus (σ⁻¹)⁻¹ μ = μ at hd
      simpa only [inv_inv] using hd
    have : IsAffineHom d.pinning.torus.X.hom := by
      have : IsClosedImmersion d.pinning.inclusion.hom.hom.left := d.maximalTorus.2.1
      change IsAffineHom d.pinning.torus.toGrp.X.hom
      rw [← Over.w d.pinning.inclusion.hom.hom]
      infer_instance
    obtain ⟨ν, hν⟩ := (galoisInvariantLattices k K d.pinning.torus).2.surjective ⟨μ, hfix⟩
    have hμ : cocharacterLattice.baseChange (algebraBaseMap k K) d.pinning.torus ν = μ :=
      congrArg Subtype.val hν
    obtain ⟨η, hη, huniq⟩ := existsUnique_factor d ν
    refine ⟨η, ?_, ?_⟩
    · exact (congrArg (cocharacterLattice.baseChange b d.pinning.torus) hη).trans hμ
    · intro η' hη'
      apply huniq
      exact cocharacterLattice.algebraBaseChange_injective k K d.pinning.torus
        (hη'.trans hμ.symm)

end Langlands.GroupScheme
