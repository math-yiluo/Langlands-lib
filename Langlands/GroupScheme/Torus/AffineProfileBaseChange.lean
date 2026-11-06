import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers

/-! # Actual geometric torus profiles under arbitrary affine base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {r A : Type u} [CommRing r] [CommRing A]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)
  (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of r))

local instance affineProfile_smooth_baseChange :
    Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b))

local instance affineProfile_affine_baseChange :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- Actual scalar extension of an exponent weight module along any specified
affine scheme morphism, with its induced scalar structure recorded explicitly. -/
def affineExponentWeightBaseChangeEquiv (m : I → ℤ) :
    letI : Algebra r A := (Spec.preimage b).hom.toAlgebra
    A ⊗[r] exponentWeightSpace I G i m ≃ₗ[A]
      exponentWeightSpace I ((baseChange b).obj G)
        (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) m := by
  letI : Algebra r A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap r A = b := Spec.map_preimage b
  let P (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of r)) :=
    A ⊗[r] exponentWeightSpace I G i m ≃ₗ[A]
      exponentWeightSpace I ((baseChange f).obj G)
        (RelativeCocharacterCentralizer.baseChangedTorusHom I G i f) m
  have E : P (algebraBaseMap r A) := exponentWeightBaseChangeEquiv (K := A) G I i m
  exact Eq.mp (congrArg P hb) E

/-- Relative actual weight ranks pull back along every specified affine
scheme morphism, including maps with nonreduced or nonnoetherian base. -/
theorem exponentWeightRank_affineBaseChange (m : I → ℤ) (t : Spec (CommRingCat.of A)) :
    exponentWeightRank I ((baseChange b).obj G)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) m t =
        exponentWeightRank I G i m (b t) := by
  let : Algebra r A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap r A = b := Spec.map_preimage b
  have he := congrFun (Module.rankAtStalk_eq_of_equiv
    (affineExponentWeightBaseChangeEquiv I G i b m).symm) t
  have hr := Module.rankAtStalk_baseChange
    (R := r) (M := exponentWeightSpace I G i m) t
  change Module.rankAtStalk (A ⊗[r] exponentWeightSpace I G i m) t =
    Module.rankAtStalk (exponentWeightSpace I G i m) ((algebraBaseMap r A) t) at hr
  rw [hb] at hr
  exact he.trans hr

local instance affineProfile_smooth_geometricFiber
    (s : Spec (CommRingCat.of r)) : Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance affineProfile_affine_geometricFiber
    (s : Spec (CommRingCat.of r)) : IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- Actual geometric identity-component weight dimensions are preserved at
points lying over one another, despite their different chosen algebraic closures. -/
theorem finrank_geometricIdentityWeight_affineBaseChange
    (m : I → ℤ) (t : Spec (CommRingCat.of A)) :
    Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField t))
      (weightSpace (T := commGroupScheme _ I)
        (geometricIdentityComponentHom I ((baseChange b).obj G)
          (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) t)
        (exponentCharacter _ I m)) =
    Module.finrank (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField (b t)))
      (weightSpace (T := commGroupScheme _ I)
        (geometricIdentityComponentHom I G i (b t)) (exponentCharacter _ I m)) := by
  rw [finrank_weight_geometricIdentityComponentHom,
    finrank_weight_geometricIdentityComponentHom,
    exponentWeightRank_affineBaseChange]

/-- The full integral-indexed actual geometric root support is unchanged
under arbitrary affine base change. -/
theorem geometricExponentRoots_affineBaseChange (t : Spec (CommRingCat.of A)) :
    geometricExponentRoots I ((baseChange b).obj G)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) t =
        geometricExponentRoots I G i (b t) := by
  ext m
  rw [mem_geometricExponentRoots_iff, mem_geometricExponentRoots_iff,
    exponentWeightRank_affineBaseChange]

omit [DecidableEq I] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The actual closed torus stays closed under the specified base change and
canonical split-coordinate identification. -/
theorem isClosedSubgroup_affineBaseChangedTorusHom (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) :=
  (IsClosedSubgroup.of_iso (baseChangeIso b I).symm).comp (hi.baseChange b)

/-- The actual geometric self-centralizing-torus locus is exactly the inverse
image of the original one under every affine base morphism. -/
theorem geometricSelfCentralizingTorusLocus_affineBaseChange (hi : IsClosedSubgroup i) :
    geometricSelfCentralizingTorusLocus I ((baseChange b).obj G)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) =
        b ⁻¹' geometricSelfCentralizingTorusLocus I G i := by
  ext t
  rw [mem_geometricSelfCentralizingTorusLocus_iff I _ _
      (isClosedSubgroup_affineBaseChangedTorusHom I G i b hi), Set.mem_preimage,
    mem_geometricSelfCentralizingTorusLocus_iff I G i hi,
    exponentWeightRank_affineBaseChange]

end Langlands.GroupScheme.splitTorus
