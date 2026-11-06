import Langlands.GroupScheme.Reductive.PinnedRigidityStatement
import Langlands.GroupScheme.Reductive.PinnedRootFixedness
import Langlands.GroupScheme.Rational.RootSubgroupAutomorphismRigidity
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement

/-! # Pinned automorphism rigidity from actual opposite-pair existence -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

namespace RootPinning

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {J : Type u} {i : T.toGrp ⟶ G}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {b : P.Base}
    (p : RootPinning i P b)

/-- Fixing the chosen root vector fixes its entire actual Lie weight line. -/
theorem targetMapLinear_eq_self_of_rootVector (f : G ⟶ G) (a : b.support)
    (hf : Lie.targetMapLinear f k (p.rootVector a) = p.rootVector a)
    (X : Additive (lieKernel G k)) (hX : X ∈ weightSpace i (P.root a)) :
    Lie.targetMapLinear f k X = X := by
  let c := (p.trivialization a).symm ⟨X, hX⟩
  have hx : X = c • p.rootVector a := by
    simpa only [c, LinearEquiv.apply_symm_apply] using p.trivialization_apply_val a c
  rw [hx, map_smul, hf]

end RootPinning

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- With all higher positive roots absent, the actual root tangent image lies
in the single original Lie weight space. -/
theorem tangentSubmodule_subgroup_le_weightSpace_of_noHigherRoots
    [Smooth G.X.hom] (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a) :
    tangentSubmodule (subgroup i a) ≤ weightSpace i a := by
  rw [tangentSubmodule_subgroup i a hT ha, semigroupWeightSpan]
  apply iSup_le
  rintro ⟨χ, n, hn, hn0, rfl⟩
  rw [actionWeightSpace_conjugation]
  by_cases hn1 : n = 1
  · simpa only [hn1, one_smul] using le_refl (weightSpace i a)
  · have hn2 : 2 ≤ n := by omega
    have hzero : weightSpace i (n • a) = ⊥ := by
      by_contra hne
      exact hhigh n hn2 ⟨hT.nsmul_ne_zero ha (by omega), hne⟩
    rw [hzero]
    exact bot_le

end RelativeRoot

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Reducedness of the supplied actual datum excludes every higher positive root multiple. -/
theorem hasNoHigherRoots (a : p.rootIndex) :
    RelativeRoot.HasNoHigherRoots p.inclusion (p.rootDatum.root a) := by
  let : p.rootDatum.IsReduced := p.isReduced
  let : IsAddTorsionFree (ℚ ⊗[ℤ] characterLattice p.torus) :=
    IsAddTorsionFree.of_module_rat _
  let : IsAddTorsionFree (characterLattice p.torus) :=
    p.isSplitTorus.character_toRat_injective.isAddTorsionFree toRat
  intro n hn
  let : n.AtLeastTwo := ⟨hn⟩
  rw [relativeRoots_eq_roots, ← p.isRootDatum.2.1]
  exact p.rootDatum.nsmul_notMem_range_root

/-- The exact pinning differential hypothesis fixes each full simple-root
functor on every test scheme. No opposite-pair premise is needed for this step. -/
theorem simple_root_isFixedBy_of_rootVector
    (σ : G ≅ G) (hi : p.inclusion ≫ σ.hom = p.inclusion) (a : p.base.support)
    (hf : Lie.targetMapLinear σ.hom k (p.pinning.rootVector a) =
      p.pinning.rootVector a) :
    RelativeRoot.IsFixedBy p.inclusion σ.hom (p.rootDatum.root a) := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  have ha := p.root_mem_relativeRoots a
  obtain ⟨U, j, hj, hjclosed, _, _⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero p.isSplitTorus
      p.inclusion (p.rootDatum.root a) ha.1
  let : IsAffineHom U.X.hom := hjclosed.isAffineHom
  let : Mono j.hom.hom := hj.1
  obtain ⟨n, e, he⟩ := RelativeRoot.exists_weightVectorCoordinates_of_noHigherRoots
    p.isSplitTorus p.inclusion ha.1 (p.hasNoHigherRoots a) hj
  apply RelativeRoot.isFixedBy_of_weightCoordinates_of_targetMap_fixed
    p.inclusion (p.rootDatum.root a) j hj p.isSplitTorus ha.1 σ hi he
  intro x
  apply p.pinning.targetMapLinear_eq_self_of_rootVector σ.hom a hf
  apply RelativeRoot.tangentSubmodule_subgroup_le_weightSpace_of_noHigherRoots
    p.isSplitTorus p.inclusion ha.1 (p.hasNoHigherRoots a)
  rw [← hj.2, RelativeRoot.tangentSubmodule_range j]
  exact ⟨x, rfl⟩

/-- Pinned rigidity with only actual pair existence and actual torus
self-centralization retained as geometric premises. -/
theorem automorphism_eq_refl_of_oppositeFactorPairs
    (hE : RelativeRoot.HasOppositeFactorPairs p.inclusion)
    (hself : torusCentralizer p.inclusion = SubgroupFunctor.range p.inclusion)
    (σ : G ≅ G) (hi : p.inclusion ≫ σ.hom = p.inclusion)
    (hf : ∀ a : p.base.support,
      Lie.targetMapLinear σ.hom k (p.pinning.rootVector a) = p.pinning.rootVector a) :
    σ = Iso.refl G := by
  apply Iso.ext
  exact p.eq_id_of_fixed_simple_rootSubgroups hE hself σ.hom hi
    (fun a => p.simple_root_isFixedBy_of_rootVector σ hi a (hf a))

end SplitPinning

/-- The two geometric prerequisites retained by the pinned-rigidity reduction. -/
def PinnedAutomorphismRigidityPrerequisites : Prop :=
  MaximalTorusCentralizerStatement.{u} ∧
    ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom G.X.hom] (p : SplitPinning G),
      RelativeRoot.HasOppositeFactorPairs p.inclusion

/-- The exact published pinned-rigidity statement follows from the two
explicit geometric prerequisites; neither prerequisite is asserted here. -/
theorem pinnedAutomorphismRigidity_of_prerequisites
    (h : PinnedAutomorphismRigidityPrerequisites.{u}) :
    PinnedAutomorphismRigidityStatement.{u} := by
  intro k _ G _ p σ hi hf
  exact p.automorphism_eq_refl_of_oppositeFactorPairs (h.2 k G p)
    (h.1 k G p.isConnectedReductive p.torus p.inclusion p.isMaximalTorus) σ hi hf

end Langlands.GroupScheme
