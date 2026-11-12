import Langlands.Geometry.Building.KPSharpCoverImageStatement
import Langlands.GroupScheme.Rational.DerivedCoverUnipotentLift
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # Proof that actual root groups lie in the simply connected image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRootReflectionData

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] (R : RelativeRootReflectionData i)

/-- The negated commutator cocharacter `-(α^∨ ≫ (σ - 1))`, where `σ` is the torus
automorphism induced by the reflection representative of `α`. -/
def derivedCocharacter (α : relativeRoots i) : cocharacterLattice T :=
  -(R.coroot α ≫ torusCommutatorEnd i (R.representative α))

/-- The commutator cocharacter lands in the actual derived subgroup. -/
theorem derivedCocharacter_mem (α : relativeRoots i) :
    R.derivedCocharacter α ∈ cocharactersLandingIn i (derivedSubgroup G) :=
  (cocharactersLandingIn i (derivedSubgroup G)).neg_mem
    (cocharacter_torusCommutatorEnd_mem i (derivedSubgroup_containsCommutators G) _ _)

/-- The commutator cocharacter pairs with `α` to `4`. -/
theorem latticePairing_derivedCocharacter (α : relativeRoots i) :
    latticePairing T α.val (R.derivedCocharacter α) = 4 := by
  set σ := normalizingAut i (R.representative α)
  have hinv : σ.inv ≫ α.val = -α.val := by
    rw [← weylAction_apply, R.action, R.pair_self]
    abel
  have hhom : σ.hom ≫ α.val = -α.val := by
    have h := congrArg (σ.hom ≫ ·) hinv
    simp only [Iso.hom_inv_id_assoc, Preadditive.comp_neg] at h
    exact (neg_eq_iff_eq_neg.mpr h).symm
  have hσ : latticePairing T α.val (R.coroot α ≫ σ.hom) =
      latticePairing T (σ.hom ≫ α.val) (R.coroot α) := by
    rw [latticePairing_apply, latticePairing_apply, Category.assoc]
  rw [derivedCocharacter, torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id, map_neg,
    map_sub, hσ, hhom, map_neg, LinearMap.neg_apply, R.pair_self]
  norm_num

end Langlands.GroupScheme.RelativeRootReflectionData

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace ZeroSubgroupDatum

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- Every rational point of every actual relative root group lifts through the
supplied simply connected derived cover. -/
theorem rootGroupLeSimplyConnectedImage : E.RootGroupLeSimplyConnectedImageStatement := by
  have hsc := E.isSimplyConnectedDerivedCover
  have hG := hsc.isConnectedReductive
  have := hG.isAffineHom
  have := E.isMaximalSplitTorus.isSplitSubtorus.mono
  obtain ⟨R, -⟩ := relativeRootReflectionExistence_of_rootRankOneFactorization
    rootRankOneFactorization F G hG S i E.isMaximalSplitTorus
  intro a ha g hg
  let α : relativeRoots i := ⟨a, ha⟩
  let hd := hsc.isDerivedSubgroup
  let χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ E.D :=
    hd.isRepresentedBy.factorHom
      (CommGroupScheme.groupHom (R.derivedCocharacter α) ≫ i) (by
        rintro U _ ⟨z, rfl⟩
        exact R.derivedCocharacter_mem α U z)
  have hχ : χ ≫ E.d = CommGroupScheme.groupHom (R.derivedCocharacter α) ≫ i :=
    hd.isRepresentedBy.factorHom_comp _ _
  have hpos : 0 < latticePairing S a (R.derivedCocharacter α) := by
    rw [show a = α.val from rfl, R.latticePairing_derivedCocharacter α]
    norm_num
  have hgU : g ∈ (Dynamic.unipotent (χ ≫ E.d)).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    exact RelativeRoot.subgroup_le_dynamicUnipotent i _ hpos _ hg
  exact mem_simplyConnectedImage.mpr
    (Dynamic.exists_derivedCover_lift_of_mem_unipotent hsc χ g hgU)

end ZeroSubgroupDatum

end Langlands.Geometry.Building
