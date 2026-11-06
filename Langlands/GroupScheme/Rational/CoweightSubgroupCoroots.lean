import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Actual subgroup coroots selected by a supplied coweight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {iH : T.toGrp ⟶ H}
    {J : Type v} {K : Type w}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {R : RootDatum K (characterLattice T) (cocharacterLattice T)}

/-- A supplied zero-coweight description of actual subgroup roots gives the
corresponding root-range identity on the original integral character lattice. -/
theorem IsRootDatumOf.root_range_eq_coweight_zero
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf iH R)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots iH =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    Set.range R.root = P.root '' {p | P.root' p ν = 0} := by
  rw [hR.2.1]
  change relativeRoots iH = _
  rw [hroots]
  ext α
  constructor
  · rintro ⟨hα, hzero⟩
    have hmem : α ∈ Set.range P.root := by
      rw [hP.2.1]
      exact hα
    obtain ⟨p, rfl⟩ := hmem
    refine ⟨p, ?_, rfl⟩
    change P.toLinearMap (P.root p) ν = 0
    rwa [hP.1]
  · rintro ⟨p, hzero, rfl⟩
    refine ⟨?_, ?_⟩
    · change P.root p ∈ roots i
      rw [← hP.2.1]
      exact Set.mem_range_self p
    · change P.toLinearMap (P.root p) ν = 0 at hzero
      rwa [hP.1] at hzero

variable [LocallyOfFiniteType G.X.hom]

/-- Actual closed split-torus geometry supplies the integral root/coroot
embedding for a subgroup described by the zeros of a supplied coweight.
Neither maximality nor reducedness is an input. -/
def IsRootDatumOf.coweightSubgroupRootEmbedding
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf iH R)
    (j : H ⟶ G) (hcomp : iH ≫ j = i)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots iH =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    SameTorusRootDatumEmbedding P R := by
  haveI : IsClosedImmersion i.hom.hom.left := hi
  haveI : Finite (weylImage i) := splitTorusWeylImageFinite k G T hT i hi
  apply hP.sameTorusSubgroupEmbedding i iH j hcomp hR
  intro α hα
  change α ∈ relativeRoots iH at hα
  rw [hroots] at hα
  exact hα.1

/-- The actual subgroup's entire integral coroot span is the span of all
ambient coroots whose roots vanish on the supplied coweight. -/
theorem IsRootDatumOf.corootSpan_eq_coweight_zero
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf iH R)
    (j : H ⟶ G) (hcomp : iH ≫ j = i)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots iH =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    R.corootSpan ℤ = Submodule.span ℤ (P.coroot '' {p | P.root' p ν = 0}) :=
  (hP.coweightSubgroupRootEmbedding hR j hcomp hT hi ν hroots).corootSpan_eq _
    (hP.root_range_eq_coweight_zero hR ν hroots)

/-- The coroot comparison preserves the annihilator on the entire actual
character lattice, including characters outside the root span. -/
theorem IsRootDatumOf.annihilator_iff_coweight_zero
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf iH R)
    (j : H ⟶ G) (hcomp : iH ≫ j = i)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots iH =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0})
    (x : characterLattice T) :
    (∀ r, R.toLinearMap x (R.coroot r) = 0) ↔
      ∀ p, P.root' p ν = 0 → P.toLinearMap x (P.coroot p) = 0 := by
  have hspan := hP.corootSpan_eq_coweight_zero hR j hcomp hT hi ν hroots
  constructor
  · intro hx
    have hker : R.corootSpan ℤ ≤ (P.toLinearMap x).ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨r, rfl⟩
      change P.toLinearMap x (R.coroot r) = 0
      rw [hP.1, ← hR.1]
      exact hx r
    rw [hspan] at hker
    intro p hp
    exact hker (Submodule.subset_span ⟨p, hp, rfl⟩)
  · intro hx
    have hker : Submodule.span ℤ (P.coroot '' {p | P.root' p ν = 0}) ≤
        (P.toLinearMap x).ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨p, hp, rfl⟩
      exact hx p hp
    rw [← hspan] at hker
    intro r
    have hzero := hker (Submodule.subset_span (Set.mem_range_self r))
    change P.toLinearMap x (R.coroot r) = 0 at hzero
    rwa [hP.1, ← hR.1] at hzero

end Langlands.GroupScheme
