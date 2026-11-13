import Langlands.Global.SplitRankOneCellPoints
import Langlands.GroupScheme.Reductive.SplitRootRankOneRelations
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Rational.RankOneCharacterComparison
import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Reductive.RankOneRootCellFactorPairs
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # Rank-one cell data for a split rank-one parabolic line

From the hypotheses of the split rank-one height statement (a connected reductive group
whose maximal split torus is a maximal torus, a single simple root `α`, and a coordinate
vector `e_j` whose exact line stabilizer is the minimal standard parabolic), this module
produces the raising and lowering root maps, the coroot, the open big cell, the torus
character `lam` of `e_j`, its coroot weight `k`, and the integral relation
`d • lam = eta|_T + b • α` with `d * k = 2 * b`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.SplitRankOne

open Langlands.GroupScheme
open Langlands.GroupScheme.MatrixRepresentation
open Langlands.LinearAlgebra.RationalSpan

variable {F : Type u} [Field F] {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A character whose rationalization lies on the rational line of another character of a
split torus is integrally dependent on it. -/
theorem not_linearIndependent_of_toRat_mem_span (hT : IsSplitTorus T.toGrp)
    {α β : characterLattice T} (h : toRat β ∈ Submodule.span ℚ {toRat α}) :
    ¬ LinearIndependent ℤ ![α, β] := by
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp h
  have hint : (q.den : ℤ) • β = q.num • α := by
    apply hT.character_toRat_injective
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, ← hq,
      smul_smul, Int.cast_natCast, Rat.den_mul_eq_num]
  rw [LinearIndependent.pair_iff]
  push Not
  refine ⟨q.num, -(q.den : ℤ), ?_, fun _ => by simp [q.den_nz]⟩
  rw [neg_smul, hint, add_neg_cancel]

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- With a single simple relative root and a maximal split torus, the roots are pairwise
integrally dependent. -/
theorem roots_pairwise_dependent_of_simpleRelativeRoots [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α}) :
    ∀ β ∈ roots i, ∀ δ ∈ roots i, ¬ LinearIndependent ℤ ![β, δ] := by
  have hT : IsSplitTorus T.toGrp := hi.1.1
  have hspan := relativeRootSpan_eq_span_singleton_of_simpleRelativeRoots i hG hi ν hν α hα
  have hαmem : α ∈ simpleRelativeRoots i ν := by rw [hα]; rfl
  have hα0 : α ≠ 0 := hαmem.1.1.1
  have hdep : ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] := by
    intro β hβ
    have hβspan : toRat β ∈ relativeRootSpan i := toRat_mem_ratSpan hβ
    rw [hspan] at hβspan
    exact not_linearIndependent_of_toRat_mem_span hT hβspan
  intro β hβ δ hδ
  exact RootReducedness.not_linearIndependent_of_not_linearIndependent hT hα0 hδ.1
    (hdep β hβ) (hdep δ hδ)

/-- Restrictions of rational characters of `G` pair to zero with every coroot. -/
theorem latticePairing_torusCharacterRestrict_coroot [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hT : IsSplitTorus T.toGrp) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (r : J) (eta : rationalCharacters G) :
    latticePairing T (torusCharacterRestrict i eta) (P.coroot r) = 0 := by
  obtain ⟨g, σ, hg, hσ⟩ := hP.2.2 r
  let g' : normalizerPoints i := ⟨g, σ, hg⟩
  have hσ' : normalizingAut i g' = σ :=
    IsNormalizingPoint.unique i (isNormalizingPoint_normalizingAut i g') hg
  have hfix := weylAction_torusCharacterRestrict i g' eta
  have hfix' : P.reflection r (torusCharacterRestrict i eta) = torusCharacterRestrict i eta := by
    rw [← hσ]
    change characterAut σ _ = _
    rw [← hσ']
    exact hfix
  rw [RootPairing.reflection_apply, sub_eq_self] at hfix'
  have hc : P.coroot' r (torusCharacterRestrict i eta) = 0 := by
    by_contra hne
    exact RootReducedness.zsmul_ne_zero hT (P.ne_zero r) hne hfix'
  rw [← hc, RootPairing.coroot', hP.1]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The rank-one data attached to a split rank-one parabolic line. -/
structure CellData (ρ : MatrixRepresentation G n) (j : n) (i : T.toGrp ⟶ G)
    (α : characterLattice T) where
  /-- The raising root map. -/
  xp : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ G
  /-- The lowering root map. -/
  xm : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ G
  /-- The coroot. -/
  cor : cocharacterLattice T
  /-- The torus character of the coordinate line. -/
  lam : characterLattice T
  /-- The coroot weight of the coordinate line. -/
  k : ℕ
  /-- The positive multiple in the line-character relation. -/
  d : ℕ
  /-- The root multiple in the line-character relation. -/
  b : ℕ
  /-- The ambient rational character in the line-character relation. -/
  eta : rationalCharacters G
  hyp : CellHyp ρ j i xp xm cor α lam k
  openCell : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left
  pairing_root : latticePairing T α cor = 2
  d_pos : 0 < d
  rel : d • lam = torusCharacterRestrict i eta + b • α
  dk : d * k = 2 * b

/-- **Existence of the rank-one cell data.** -/
theorem nonempty_cellData [Infinite F] [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (hmax : IsMaximalTorus i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (ρ : MatrixRepresentation G n) (j : n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j) :
    Nonempty (CellData ρ j i α) := by
  have hT : IsSplitTorus T.toGrp := hi.1.1
  have := hi.isSplitSubtorus.mono
  have : IsAffineHom T.X.hom := hi.isSplitSubtorus.1.isAffineHom
  obtain ⟨J, _, P, hP, -⟩ := rootDatumExistence F G hG T hT i hmax
  have hαmem : α ∈ simpleRelativeRoots i ν := by rw [hα]; rfl
  have hαroot : α ∈ Set.range P.root := by rw [hP.2.1]; exact hαmem.1.1
  obtain ⟨r, hr⟩ := hαroot
  have hrank := roots_pairwise_dependent_of_simpleRelativeRoots hG i hi ν hν α hα
  obtain ⟨xp, xm, hxp, hxm, hopen, -, hrel⟩ :=
    splitRankOneRootCell F G hG T hT i hmax J P hP hrank r
  rw [hr] at hxp hxm
  have hpairα : latticePairing T α (P.coroot r) = 2 := by
    rw [← hr, ← hP.1]
    exact P.root_coroot_two r
  have : Finite (relativeWeylGroup i) := hG.finite_relativeWeylGroup i hi
  let := Fintype.ofFinite (relativeWeylGroup i)
  obtain ⟨hTline, d, b, hd, -, eta, hdrel⟩ :=
    ρ.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer i hG hi ν hν α hα j hstab
  set lam := ρ.torusCoordinateLineCharacter i j hTline with hlam
  have hfix : (ρ.restrict xp).IsFixedVector (Pi.single j 1) := by
    apply isFixedVector_single_of_isUnipotent _ (VectorGroup.isUnipotent F 1) j
    intro Z v
    have hmem := RelativeRoot.subgroup_le_standardParabolic_empty i ν hαmem Z
      (RankOneRootCellRelation.comp_mem_rootSubgroup i α xp hxp v)
    obtain ⟨c, hc⟩ := (hstab Z (v ≫ xp.hom.hom)).mp hmem
    exact ⟨c, by rw [pointMatrix_restrict]; exact hc⟩
  have hline : ∀ (A : CommAlgCat.{u} F) (τ : GroupScheme.affinePoints T.toGrp A),
      ((ρ.restrict i).affineMatrix A τ : Matrix n n A) *ᵥ (Pi.single j (1 : A) : n → A) =
        ((Lie.characterValue lam τ : Aˣ) : A) • (Pi.single j (1 : A) : n → A) := by
    intro A τ
    have h := characterSpace_affine
      (coordinateLine_mem_characterSpace (ρ.restrict i) j hTline) A τ
    have hs : (fun r => algebraMap F A ((Pi.single j (1 : F) : n → F) r)) =
        (Pi.single j (1 : A) : n → A) := by
      funext r
      by_cases hr : r = j <;> simp [hr]
    rw [hs] at h
    exact h
  have hyp0 : CellHyp ρ j i xp xm (P.coroot r) α lam (latticePairing T lam (P.coroot r)) :=
    ⟨fun Z => hrel Z, VectorGroup.isTorusEquivariant_of_weightPointAction hxm, hfix, hline,
      rfl⟩
  have hk := hyp0.pairing_nonneg
  set k := (latticePairing T lam (P.coroot r)).toNat with hkdef
  have hkk : (k : ℤ) = latticePairing T lam (P.coroot r) := Int.toNat_of_nonneg hk
  have hyp : CellHyp ρ j i xp xm (P.coroot r) α lam k := by rw [hkk]; exact hyp0
  have heta0 := latticePairing_torusCharacterRestrict_coroot i hT P hP r eta
  have hpair := congrArg (fun χ => latticePairing T χ (P.coroot r)) hdrel
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, heta0, hpairα,
    zero_add, nsmul_eq_mul] at hpair
  have hdk : d * k = 2 * b := by
    have : ((d * k : ℕ) : ℤ) = ((2 * b : ℕ) : ℤ) := by
      push_cast
      rw [hkk, hpair]
      ring
    exact_mod_cast this
  exact ⟨⟨xp, xm, P.coroot r, lam, k, d, b, eta, hyp, hopen, hpairα, hd, hdrel, hdk⟩⟩

end Langlands.Global.SplitRankOne
