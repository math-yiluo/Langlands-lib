import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections

/-! # Original semidirect projections as dynamic limits -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.IsSemidirectDecomposition

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M U : Subgroup (rationalPoints G)}
  (d : IsSemidirectDecomposition P M U)

/-- The original projection of any realized triple is the dynamic limit. -/
theorem projection_eq_dynamicLimit
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : P = (Dynamic.parabolic χ).rationalPoints)
    (hM : M = (Dynamic.centralizer χ).rationalPoints)
    (hU : U = (Dynamic.unipotent χ).rationalPoints) (p : P) :
    (d.projection p : rationalPoints G) =
      Dynamic.limit χ ⟨p, hP ▸ p.property⟩ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let pd : (Dynamic.parabolic χ).rationalPoints := ⟨p, hP ▸ p.property⟩
  have hz : Dynamic.limit χ pd ∈ M := by
    rw [hM]
    exact Dynamic.limit_mem_centralizer χ pd
  apply congrArg Subtype.val ((d.projection_eq_iff p ⟨_, hz⟩).mpr ?_)
  rw [hU]
  have hl := Dynamic.centralizer_le_parabolic χ _
    (Dynamic.limit_mem_centralizer χ pd)
  have hu := Dynamic.conj_mem_unipotent χ (inv_mem hl)
    (Dynamic.mul_inv_limit_mem_unipotent χ pd)
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hu

/-- A represented closed subgroup stable under the realizing cocharacter
contains the original Levi projection of each of its parabolic points. -/
theorem projection_mem_of_closed_stable
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : P = (Dynamic.parabolic χ).rationalPoints)
    (hM : M = (Dynamic.centralizer χ).rationalPoints)
    (hU : U = (Dynamic.unipotent χ).rationalPoints)
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation χ).IsStable F)
    (p : P) (hp : (p : rationalPoints G) ∈ F.rationalPoints) :
    (d.projection p : rationalPoints G) ∈ F.rationalPoints := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let pd : (Dynamic.parabolic χ).rationalPoints := ⟨p, hP ▸ p.property⟩
  have hlim : Dynamic.HasLimit χ (p : rationalPoints G) (Dynamic.limit χ pd) :=
    Dynamic.hasLimit_limit χ pd
  have hmem : Dynamic.limit χ pd ∈ F.rationalPoints :=
    Dynamic.HasLimit.mem_of_isClosedSubgroup_of_isStable χ hj hjc hF
      (T := Over.mk (𝟙 (Spec (CommRingCat.of k))))
      (g := (p : rationalPoints G)) (l := Dynamic.limit χ pd) hp hlim
  rw [d.projection_eq_dynamicLimit χ hP hM hU p]
  exact hmem

section RestrictedProjection

variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (hP : P = (Dynamic.parabolic χ).rationalPoints)
  (hM : M = (Dynamic.centralizer χ).rationalPoints)
  (hU : U = (Dynamic.unipotent χ).rationalPoints)
  {H : GroupScheme (Spec (CommRingCat.of k))}
  {F : SubgroupFunctor G} {j : H ⟶ G}
  (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (hF : (AutomorphicAction.conjugation χ).IsStable F)

/-- Restrict the original projection to the points of a represented closed
stable subgroup, with values in its literal Levi intersection. -/
def closedStableProjection :
    F.rationalPoints.subgroupOf P →* F.rationalPoints.subgroupOf M where
  toFun a := ⟨d.projection a.val,
    d.projection_mem_of_closed_stable χ hP hM hU hj hjc hF a.val a.property⟩
  map_one' := Subtype.ext (map_one d.projection)
  map_mul' a b := Subtype.ext (map_mul d.projection a.val b.val)

@[simp]
theorem closedStableProjection_apply (a : F.rationalPoints.subgroupOf P) :
    (d.closedStableProjection χ hP hM hU hj hjc hF a : M) =
      d.projection a.val := rfl

end RestrictedProjection

/-- A second dynamic unipotent subgroup of the same torus is preserved
by the original projection of the first realized triple. -/
theorem projection_mem_commonTorusUnipotent
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (α β : cocharacterLattice T)
    (hP : P = (Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i)).rationalPoints)
    (hM : M = (Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i)).rationalPoints)
    (hU : U = (Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i)).rationalPoints)
    (p : P) (hp : (p : rationalPoints G) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i)).rationalPoints) :
    (d.projection p : rationalPoints G) ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom β ≫ i)).rationalPoints := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let ψ := CommGroupScheme.groupHom β ≫ i
  have hF := (Dynamic.unipotent_isStable_conjugation i
    (CommGroupScheme.groupHom β)).restrict (CommGroupScheme.groupHom α)
  rw [AutomorphicAction.restrict_conjugation] at hF
  exact d.projection_mem_of_closed_stable
    (CommGroupScheme.groupHom α ≫ i) hP hM hU
    (Dynamic.Affine.isRepresentedBy_unipotentHom ψ)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom ψ) hF p hp

end Langlands.Aubert.General.IsSemidirectDecomposition
