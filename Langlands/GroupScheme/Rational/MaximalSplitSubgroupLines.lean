import Langlands.GroupScheme.Rational.MaximalSplitRankOneLine
import Langlands.GroupScheme.Rational.MaximalSplitRankOneRelation
import Langlands.GroupScheme.Rational.MaximalSplitGeneratedWeyl
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.GroupScheme.Rational.RootSubgroupRationalNontrivial
import Langlands.Geometry.Building.QuasiSplitApartmentOpposite

/-! # Rank-one line pairs at the nonmultipliable relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open LocalSplitCell (rootPoint)

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **A rank-one line pair at a nonmultipliable relative root.** Let `i` be a maximal split
torus of a connected reductive group and `d` a relative root with `2d` not a root. There are
monic lines `x`, `y` of weights `d`, `-d` in the root groups `U_(d)`, `U_(-d)`, a cocharacter
`ν` with `⟨d, ν⟩ = 2` and a rational point `n = y(-1) x(1) y(-1)` normalizing the torus
through the reflection `s_d`, such that the rank-one relation holds on every test scheme. -/
theorem exists_linePair (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) {d : characterLattice S}
    (hd : haveI := hG.isAffineHom; d ∈ roots i)
    (h2 : haveI := hG.isAffineHom; (2 : ℤ) • d ∉ roots i) :
    haveI := hG.isAffineHom
    ∃ (x y : RootCell.Ga k ⟶ G) (ν : cocharacterLattice S)
      (hpair : latticePairing S d ν = 2) (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      VectorGroup.IsTorusEquivariant i x d ∧ Mono x.hom.hom ∧
      SubgroupFunctor.range x ≤ RelativeRoot.subgroup i d ∧
      VectorGroup.IsTorusEquivariant i y (-d) ∧ Mono y.hom.hom ∧
      SubgroupFunctor.range y ≤ RelativeRoot.subgroup i (-d) ∧
      n = rootPoint y (Over.mk (𝟙 _)) (-1) * rootPoint x (Over.mk (𝟙 _)) 1 *
        rootPoint y (Over.mk (𝟙 _)) (-1) ∧
      IsNormalizingPoint i n (latticeReflectionIso d ν hpair) ∧
      ∀ Z : Over (Spec (CommRingCat.of k)), RootCell.RelationOver i ν x y Z := by
  have := hG.isAffineHom
  have := hG.smooth
  have : Mono i.hom.hom.left := hi.1.mono
  have hT : IsSplitTorus S.toGrp := hi.1.1
  have hd0 : d ≠ 0 := hd.1
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs i hT).mp
      (rootRankOneFactorization k G hG S i hi)
  have hhigh : RelativeRoot.HasNoHigherRoots i d :=
    hE.hasNoHigherRoots_of_two_not_mem i hT h2
  obtain ⟨U, jU, hjU, -, -, -⟩ := RelativeRoot.subgroup_has_smooth_closed_representative hT i d hd0
  obtain ⟨u, hu, hu1⟩ := RelativeRoot.exists_rootPoint_actual hT i hd
  obtain ⟨x, hx, hxm, hxr, -⟩ := exists_line_through_rootPoint hT i hd0 hhigh hjU u hu hu1
  have := hxm
  obtain ⟨ν, hpair, n, hy, hym, hyr, hn, hnorm, hrel⟩ :=
    exists_rankOneRelation hG i hi hd h2 x hx hxr
  exact ⟨x, oppositeLine x n, ν, hpair, n, hx, hxm, hxr, hy, hym, hyr, hn, hnorm, hrel⟩

/-- **The reflection of a normalizing point preserves the roots.** If a rational point
normalizes `i` through the lattice reflection `s_d`, then `c - ⟨c, ν⟩ d` is a root for every
root `c`. -/
theorem sub_pairing_smul_mem_roots [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}
    {d : characterLattice S} {ν : cocharacterLattice S} {hpair : latticePairing S d ν = 2}
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hn : IsNormalizingPoint i n (latticeReflectionIso d ν hpair)) {c : characterLattice S}
    (hc : c ∈ roots i) : c - latticePairing S c ν • d ∈ roots i := by
  rw [← reflection_inv_comp_character hpair c]
  exact (mem_roots_iff_of_isNormalizingPoint hn c).mpr hc

/-- **Commutation of opposite root groups at distinct base roots.** If no `n d - m e` with
`n, m > 0` is zero or a root, the points of `U_(d)` and `U_(-e)` commute on every test. -/
theorem commute_of_root_groups [IsAffineHom G.X.hom] [Smooth G.X.hom] (i : S.toGrp ⟶ G)
    (hT : IsSplitTorus S.toGrp) {d e : characterLattice S} (hd : d ≠ 0) (he : e ≠ 0)
    (hde : ∀ n m : ℕ, 0 < n → 0 < m → n • d - m • e ≠ 0 ∧ n • d - m • e ∉ roots i)
    {Z : Over (Spec (CommRingCat.of k))} {g h : Z ⟶ G.X}
    (hg : g ∈ (RelativeRoot.subgroup i d).carrier Z)
    (hh : h ∈ (RelativeRoot.subgroup i (-e)).carrier Z) : Commute g h := by
  refine Langlands.Geometry.Building.commute_of_no_strict_root_combinations i hT d (-e) hd
    (neg_ne_zero.mpr he) (fun n m hn hm => ?_) hg hh
  rw [smul_neg, ← sub_eq_add_neg]
  exact hde n m hn hm

end Langlands.GroupScheme.MaximalSplitSubgroup
