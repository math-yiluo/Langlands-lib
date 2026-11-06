import Langlands.GroupScheme.Torus.RelativeSelfCentralizingLocus
import Langlands.GroupScheme.Torus.ExponentCharacters
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Locally constant actual geometric root profiles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- For an affine group locally of finite type over a field, actual roots are
exactly the nonzero characters whose actual weight spaces have nonzero dimension. -/
theorem mem_roots_iff_finrank_ne_zero {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (α : characterLattice T) :
    α ∈ roots i ↔ α ≠ 0 ∧ Module.finrank k (weightSpace i α) ≠ 0 := by
  exact and_congr Iff.rfl (not_congr
    (Submodule.finrank_eq_zero (R := k) (S := weightSpace i α)).symm)

namespace splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance rootProfile_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance rootProfile_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- Every actual character weight of the actual geometric identity component
has the corresponding relative exponent rank. -/
theorem finrank_weight_geometricIdentityComponentHom
    (s : Spec (CommRingCat.of r)) (m : I → ℤ) :
    Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
          (exponentCharacter _ I m)) =
      exponentWeightRank I G i m s := by
  calc
    _ = Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
        (weightSpace (T := commGroupScheme _ I) (geometricFiberHom I G i s)
          (exponentCharacter _ I m)) :=
      IdentityComponent.finrank_weightSpace _ _ _
    _ = geometricExponentWeightRankProfile I G i s m := by
      dsimp only [geometricExponentWeightRankProfile]
      rw [exponentCharacter_eq_characterLatticeEquiv_symm]
    _ = _ := geometricExponentWeightRankProfile_apply I G i s m

/-- The actual nonzero adjoint characters in each geometric identity component,
expressed by the common integral coordinate vectors of the standard torus. -/
def geometricExponentRoots (s : Spec (CommRingCat.of r)) : Set (I → ℤ) :=
  {m | exponentCharacter _ I m ∈
    roots (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)}

/-- Membership of the actual root support is exactly nonzero exponent and
nonzero rank of the actual relative summand. -/
theorem mem_geometricExponentRoots_iff (s : Spec (CommRingCat.of r)) (m : I → ℤ) :
    m ∈ geometricExponentRoots I G i s ↔
      m ≠ 0 ∧ exponentWeightRank I G i m s ≠ 0 := by
  change exponentCharacter _ I m ∈ roots
    (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s) ↔ _
  rw [mem_roots_iff_finrank_ne_zero,
    finrank_weight_geometricIdentityComponentHom I G i s m]
  have hzero : exponentCharacter
      (Spec (CommRingCat.of (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))))
      I m = 0 ↔ m = 0 := by
    rw [exponentCharacter_eq_characterLatticeEquiv_symm]
    exact AddEquiv.map_eq_zero_iff _
  exact and_congr (not_congr hzero) Iff.rfl

/-- All actual geometric root supports are determined by the full relative
weight-rank profiles. -/
theorem geometricExponentRoots_eq (s : Spec (CommRingCat.of r)) :
    geometricExponentRoots I G i s =
      {m | m ≠ 0 ∧ exponentWeightRank I G i m s ≠ 0} := by
  ext m
  exact mem_geometricExponentRoots_iff I G i s m

/-- The full actual geometric root support is locally constant, retaining
possibly disconnected ambient fibres. -/
theorem isLocallyConstant_geometricExponentRoots :
    IsLocallyConstant (geometricExponentRoots I G i) := by
  have heq : geometricExponentRoots I G i =
      fun s => {m | m ≠ 0 ∧ exponentWeightRankProfile I G i s m ≠ 0} := by
    funext s
    exact geometricExponentRoots_eq I G i s
  rw [heq]
  exact (isLocallyConstant_exponentWeightRankProfile I G i).comp
    (fun p : (I → ℤ) → ℕ => {m | m ≠ 0 ∧ p m ≠ 0})

/-- A single open neighbourhood preserves both the complete actual root
support and all actual weight dimensions in the geometric identity components. -/
theorem exists_open_geometricRootProfiles_eq (s : Spec (CommRingCat.of r)) :
    ∃ U : Set (Spec (CommRingCat.of r)), IsOpen U ∧ s ∈ U ∧
      ∀ t ∈ U, geometricExponentRoots I G i t = geometricExponentRoots I G i s ∧
        ∀ m : I → ℤ,
          Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField t))
              (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i t)
                (exponentCharacter _ I m)) =
            Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s))
              (weightSpace (T := commGroupScheme _ I) (geometricIdentityComponentHom I G i s)
                (exponentCharacter _ I m)) := by
  obtain ⟨U, hU, hs, hconst⟩ := exists_open_exponentWeightRanks_eq I G i s
  refine ⟨U, hU, hs, fun t ht => ⟨?_, ?_⟩⟩
  · ext m
    rw [mem_geometricExponentRoots_iff, mem_geometricExponentRoots_iff, hconst t ht m]
  · intro m
    rw [finrank_weight_geometricIdentityComponentHom,
      finrank_weight_geometricIdentityComponentHom, hconst t ht m]

end splitTorus

end Langlands.GroupScheme
