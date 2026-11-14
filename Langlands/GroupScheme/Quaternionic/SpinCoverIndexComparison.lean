import Langlands.GroupScheme.Quaternionic.SpinCoverCocharacterComparison
import Langlands.GroupScheme.Reductive.PinningNumberingBaseChange

/-! # The actual indexed torus cocharacter in a split spin comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

local instance spinIndexComparisonAffine {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ inferInstance

namespace Quaternionic.OrthogonalMorita

variable {K F L D : Type u} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [Algebra.IsAlgebraic F L]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {m n degree : ℕ} {sigma : FirstKindInvolution K D}
  {q : sigma.QuadraticForms (Fin m)}
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom]
  {pi : G ⟶ sigma.isometryGroup q}
  (mor : OrthogonalMoritaComparison sigma q L degree n)
  (hpi : sigma.IsSpinCover q pi)

local instance spinIndexComparisonOrthogonalSmooth :
    Smooth (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of L)

local instance spinIndexComparisonOrthogonalAffine :
    IsAffineHom (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of L)

/-- Transport the alignment of all vertices with label zero, using the
actual simple-vertex equivalence rather than identifying the two supports. -/
theorem splitCoverTower_numbered_alignment
    (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap K F)).obj G))
    (e : p.base.support ≃ Fin n)
    (h : ∀ v : p.base.support, (e v).val = 0 →
      p.FundamentalWeightTrivialOnKernel v
        ((GroupScheme.baseChange (algebraBaseMap K F)).map pi)) :
    ∀ v : (p.baseChange (F := L)).base.support,
      (p.baseChangeNumbering (L := L) e v).val = 0 →
      (p.baseChange (F := L)).FundamentalWeightTrivialOnKernel v
        (splitCoverTower mor hpi F) := by
  intro v hv
  let v0 := (p.baseChangeSimpleEquiv (F := L)).symm v
  have hv0 : (e v0).val = 0 := hv
  have h0 := splitCoverTower_alignment mor hpi F p v0 (h v0 hv0)
  simpa only [v0, Equiv.apply_symm_apply] using h0

end Quaternionic.OrthogonalMorita

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

variable (L : Type u) [Field L] [Algebra (SeparableClosure K) L]

/-- Lift a cocharacter of the index's actual split torus to the twice
extended pinning torus, using the index's supplied torus map. -/
def spinVectorCocharacter (nu : cocharacterLattice d.splitTorus) :
    cocharacterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap (SeparableClosure K) L)).obj
        d.pinning.toSplitPinning.torus) :=
  cocharacterLattice.baseChange (algebraBaseMap (SeparableClosure K) L)
    d.pinning.toSplitPinning.torus
    (cocharacterLattice.baseChange (algebraBaseMap K (SeparableClosure K))
        d.splitTorus nu ≫
      (CommGroupScheme.baseChange (algebraBaseMap K (SeparableClosure K))).map d.torusMap)

theorem spinVectorCocharacter_eq (nu : cocharacterLattice d.splitTorus) :
    d.spinVectorCocharacter L nu =
      cocharacterLattice.baseChange (algebraBaseMap (SeparableClosure K) L)
        d.pinning.toSplitPinning.torus
        (cocharacterLattice.baseChange (algebraBaseMap K (SeparableClosure K))
          d.pinning.torus (nu ≫ d.torusMap)) := by
  rw [cocharacterLattice.baseChange_comp]
  rfl

variable [Algebra K L] [IsScalarTower K (SeparableClosure K) L]
  {D : Type u} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {m n degree : ℕ} {sigma : Quaternionic.FirstKindInvolution K D}
  {q : sigma.QuadraticForms (Fin m)}
  {pi : G ⟶ sigma.isometryGroup q}
  (mor : Quaternionic.OrthogonalMoritaComparison sigma q L degree n)
  (hpi : sigma.IsSpinCover q pi)

/-- The index's torus square identifies the original cocharacter action
with the actual twice-extended split action in the supplied Morita coordinates. -/
theorem spinVectorCocharacter_square (nu : cocharacterLattice d.splitTorus) :
    Dynamic.baseChangeCocharacter (algebraBaseMap K L)
        (CommGroupScheme.groupHom nu ≫ d.splitInclusion ≫ pi) ≫ mor.groupIso.hom =
      CommGroupScheme.groupHom (d.spinVectorCocharacter L nu) ≫
        Quaternionic.OrthogonalMorita.splitCoverTowerTorusMap
          (F := SeparableClosure K) mor hpi d.pinning.torus d.pinning.inclusion := by
  have horig : CommGroupScheme.groupHom (nu ≫ d.torusMap) ≫
      d.pinning.inclusion ≫ pi =
      CommGroupScheme.groupHom nu ≫ d.splitInclusion ≫ pi := by
    change (CommGroupScheme.groupHom nu ≫ CommGroupScheme.groupHom d.torusMap) ≫
      d.pinning.inclusion ≫ pi = _
    rw [Category.assoc, ← Category.assoc (CommGroupScheme.groupHom d.torusMap),
      d.square]
  have h := Quaternionic.OrthogonalMorita.splitCoverTower_cocharacter
    (F := SeparableClosure K) mor hpi d.pinning.torus d.pinning.inclusion
    (nu ≫ d.torusMap)
  rw [horig] at h
  rw [spinVectorCocharacter_eq]
  exact h

end TitsIndexData

end Langlands.GroupScheme
