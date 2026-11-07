import Langlands.AlgebraicGeometry.PointTopology.FiniteAffineNeighborhoodsOpenShrinking
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Separatedness from finite-set affine neighborhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Every scheme with finite-set affine neighborhoods is separated. -/
def FiniteAffineNeighborhoodsSeparatedStatement : Prop :=
  ∀ (X : Scheme.{u}), HasFiniteAffineNeighborhoods X → X.IsSeparated

/-- Every morphism whose source is AF is separated. -/
theorem isSeparated_of_hasFiniteAffineNeighborhoods
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hX : HasFiniteAffineNeighborhoods X) :
    IsSeparated f := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i : 𝒰.I₀) : ((𝒰.pullback₁ f).X i).OpenCover :=
    ((𝒰.pullback₁ f).X i).openCoverOfIsOpenCover
    (fun U : ((𝒰.pullback₁ f).X i).affineOpens => U.val)
    (iSup_affineOpens_eq_top _)
  have hV (i : 𝒰.I₀) (j : (𝒱 i).I₀) : IsAffine ((𝒱 i).X j) := j.property
  have htop : Scheme.Pullback.diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ := by
    apply top_unique
    rintro x _
    simp only [Scheme.Pullback.diagonalCoverDiagonalRange,
      Scheme.Pullback.openCoverOfBase_I₀, Scheme.Pullback.openCoverOfBase_X,
      Scheme.Pullback.openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe,
      Scheme.Hom.coe_opensRange, Opens.mem_mk, Set.mem_iUnion, Set.mem_range, Sigma.exists]
    let i := 𝒰.idx (f (pullback.fst f f x))
    obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f (pullback.fst f f x)⟩ :=
      𝒰.covers (f (pullback.fst f f x))
    obtain ⟨z₁, hz₁, _⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hy.symm
    have hy₂ : 𝒰.f i y = f (pullback.snd f f x) := by
      rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    obtain ⟨z₂, hz₂, _⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hy₂.symm
    have hlocal : HasFiniteAffineNeighborhoods (pullback f (𝒰.f i)) :=
      hasFiniteAffineNeighborhoods_of_isOpenImmersion (pullback.fst f (𝒰.f i)) hX
    obtain ⟨V, hV⟩ := hlocal {z₁, z₂} (by simp)
    refine ⟨i, V, ?_⟩
    rw [Scheme.Pullback.diagonalCover_map]
    change x ∈ Set.range _
    simp only [Scheme.Pullback.diagonalCover, Scheme.Pullback.openCoverOfBase_I₀,
      Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
      Precoverage.ZeroHypercover.bind_toPreZeroHypercover, Scheme.Pullback.openCoverOfBase_X,
      PreZeroHypercover.bind_X, Scheme.Pullback.openCoverOfLeftRight_I₀,
      Scheme.Pullback.openCoverOfLeftRight_X]
    rw [Scheme.Pullback.range_map]
    constructor
    · refine ⟨⟨z₁, hV (by simp)⟩, ?_⟩
      exact hz₁
    · refine ⟨⟨z₂, hV (by simp)⟩, ?_⟩
      exact hz₂
  constructor
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun _ : PUnit.{0} => ⊤) (by simp) fun _ => ?_
  rw [← htop]
  exact isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱

/-- The absolute separatedness statement holds in every universe. -/
theorem finiteAffineNeighborhoodsSeparated :
    FiniteAffineNeighborhoodsSeparatedStatement.{u} := by
  intro X hX
  exact ⟨isSeparated_of_hasFiniteAffineNeighborhoods (terminal.from X) hX⟩

/-- In particular an AF scheme is quasi-separated. -/
theorem quasiSeparatedSpace_of_hasFiniteAffineNeighborhoods
    {X : Scheme.{u}} (hX : HasFiniteAffineNeighborhoods X) :
    QuasiSeparatedSpace X := by
  let : X.IsSeparated := finiteAffineNeighborhoodsSeparated X hX
  infer_instance

end Langlands.AlgebraicGeometry.PointTopology
