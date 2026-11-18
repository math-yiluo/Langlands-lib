import Langlands.GroupScheme.Reductive.RankOneLocalCell
import Langlands.GroupScheme.Reductive.RankOneLocalRootCell
import Langlands.GroupScheme.Rational.RankOneCocharacterSymmetrization
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.RootedSolvableQuotientNormalizerProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.Absolute.RootedProperBorel
import Langlands.GroupScheme.Absolute.PrescribedBorelQuotient

/-! # Root cells in semisimple rank one from local line data

For a connected reductive `G` over an algebraically closed field with nonempty, pairwise
dependent roots, a Weyl point negating every root comes from an ordinary proper Borel quotient.
Given a root `α`, a cocharacter `ν` positive on `α`, and the local facts that `α` and `-α` are
the only roots of each sign on `ν` with one-dimensional root spaces, the open cell, the coroot
and a root cell follow. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RankOneLocalAssembly

variable {k : Type u} [Field k] [IsAlgClosed k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **A Weyl point negating every root.** An ordinary proper Borel subgroup containing the
torus gives a nonidentity Weyl class; in semisimple rank one it acts by `-1` on the roots. -/
theorem exists_weylPoint (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom; α ∈ roots i) :
    ∃ (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (σ : T ≅ T),
      IsNormalizingPoint i n σ ∧
      ∀ β : characterLattice T, (haveI := hG.isAffineHom; β ∈ roots i) →
        σ.hom ≫ β = -β ∧ (haveI := hG.isAffineHom; -β ∈ roots i) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨B, b, t, hpair, -, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    solvableMaximalTorusConjugacy k B hpair.1.isSolvableGroupScheme
  let D := hpair.1.properQuotientData_of_solvableProperFixedPoint solvableProperFixedPoint
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive i hi hT hα b hpair.1.isClosedSubgroup
    hpair.1.isSolvableGroupScheme t ht hconj D.projection D.fibers
  let := hi.2.1.mono
  refine ⟨n.val, normalizingAut i n.val, isNormalizingPoint_normalizingAut i n.val, ?_⟩
  intro β hβ
  have h := hG.weylAction_eq_neg_of_rankOne i hi hT hdep n.val n.property β hβ
  have hmem := weylAction_mapsTo_relativeRoots i n.val hβ
  refine ⟨?_, h ▸ hmem⟩
  rw [weylAction_apply] at h
  have h' : (normalizingAut i n.val).hom ≫ ((normalizingAut i n.val).inv ≫ β) = β := by
    simp
  rw [h, Preadditive.comp_neg] at h'
  exact neg_eq_iff_eq_neg.mp h'

omit [IsAlgClosed k] in
/-- A nonzero character of a split torus is positive on some cocharacter. -/
theorem exists_latticePairing_pos (hT : IsSplitTorus T.toGrp) {α : characterLattice T}
    (hα : α ≠ 0) : ∃ ν : cocharacterLattice T, 0 < latticePairing T α ν := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply hα
  apply hT.isPerfPair_latticePairing.separatingLeft α
  intro ν
  have h1 := h ν
  have h2 := h (-ν)
  rw [map_neg] at h2
  omega

omit [IsAlgClosed k] in
/-- **The roots are `±α`.** If the roots are pairwise dependent, `α` is a root positive on `ν`,
and the only roots positive (negative) on `ν` are `α` (`-α`), then every root is `α` or `-α`. -/
theorem eq_or_eq_neg_of_mem_roots (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom; α ∈ roots i)
    {ν : cocharacterLattice T} (hν : 0 < latticePairing T α ν)
    (hpos : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, 0 < latticePairing T β ν → β = α)
    (hneg : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, latticePairing T β ν < 0 → β = -α)
    {β : characterLattice T} (hβ : haveI := hG.isAffineHom; β ∈ roots i) :
    β = α ∨ β = -α := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAddTorsionFree (TensorProduct ℤ ℚ (characterLattice T)) :=
    IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice T) :=
    hT.character_toRat_injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
  rcases lt_trichotomy (latticePairing T β ν) 0 with h | h | h
  · exact Or.inr (hneg β hβ h)
  · exfalso
    have hβ0 : β ≠ 0 := (mem_relativeRoots.mp hβ).1
    have hl := hdep α hα β hβ
    rw [LinearIndependent.pair_iff] at hl
    push Not at hl
    obtain ⟨m, l, hml, hne⟩ := hl
    have hp := congrArg (fun χ => latticePairing T χ ν) hml
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, h, map_zero,
      LinearMap.zero_apply, smul_eq_mul, mul_zero, add_zero] at hp
    have hm : m = 0 := by
      rcases mul_eq_zero.mp hp with hm | hm
      · exact hm
      · exact absurd hm hν.ne'
    subst hm
    have hl0 : l ≠ 0 := by
      intro hl0
      exact hne rfl hl0
    rw [zero_smul, zero_add] at hml
    exact hβ0 ((IsAddTorsionFree.zsmul_eq_zero_iff_right hl0).mp hml)
  · exact Or.inl (hpos β hβ h)

/-- **Root cell from local line data.** In semisimple rank one over an algebraically closed
field, if `α` is a root, `⟨α, ν⟩ > 0`, the only roots positive (negative) on `ν` are `α` (`-α`)
and the root spaces of `±α` are lines, then there are a coroot `h` with `⟨α, h⟩ = 2` and root
groups forming a root cell for `(α, h)`. -/
theorem exists_isRootCell (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom; α ∈ roots i)
    {ν : cocharacterLattice T} (hν : 0 < latticePairing T α ν)
    (hpos : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, 0 < latticePairing T β ν → β = α)
    (hneg : haveI := hG.isAffineHom;
      ∀ β ∈ roots i, latticePairing T β ν < 0 → β = -α)
    (hline : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i α))
    (hline' : haveI := hG.isAffineHom; Nonempty (k ≃ₗ[k] weightSpace i (-α))) :
    ∃ (h : cocharacterLattice T) (xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G),
      latticePairing T α h = 2 ∧ RootCell.IsRootCell i α h xp xm := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨n, σ, hn, hσ⟩ := exists_weylPoint hG hT i hi hdep hα
  have hα' : -α ∈ roots i := (hσ α hα).2
  have hZ := rankOne_centralizer_isRepresentedBy dynamicCentralizerReductive hG hT i hi hdep
    α hα ν hν.ne'
  obtain ⟨xp, xm, -, -, hxpc, hxmc, hopen⟩ :=
    RankOneLocalCell.exists_cell hG hT i hi α hα hα' ν hν hZ hpos hneg hline hline'
  let D : RankOneRootCellRelation.CellData k :=
    { G := G, T := T, i := i, xp := xp, xm := xm, α := α, hxp := hxpc, hxm := hxmc,
      open_cell := hopen }
  have : IrreducibleSpace D.G.X.left := DynamicConnected.irreducibleSpace_of_smooth G
  have : Mono i.hom.hom.left := hi.2.1.mono
  have : Mono D.i.hom.hom := Over.mono_of_mono_left _
  have hα0 : α ≠ 0 := (mem_relativeRoots.mp hα).1
  obtain ⟨h, xm', pair, hrc⟩ := RankOneLocalRootCell.exists_isRootCell D
    (inferInstanceAs (IsSeparated G.X.hom)) hT hα0 hZ hn (hσ α hα).1
  exact ⟨h, xp, xm', pair, hrc⟩

end RankOneLocalAssembly

end Langlands.GroupScheme
