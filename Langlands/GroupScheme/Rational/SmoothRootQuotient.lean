import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.SmoothTangentWeights
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof

/-! # Smooth maps on intrinsic relative root groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section Restriction

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G H U V : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    {jU : U ⟶ G} {jV : V ⟶ H}
    (hU : (subgroup i a).IsRepresentedBy jU)
    (hV : (subgroup (i ≫ q) a).IsRepresentedBy jV)

/-- Restrict an actual homomorphism to representatives of the intrinsic root
functors for the same character and the composite torus map. -/
def rootMap : U ⟶ V :=
  hV.factorHom (jU ≫ q) (by
    intro X g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    change (x ≫ jU.hom.hom) ≫ q.hom.hom ∈ (subgroup (i ≫ q) a).carrier X
    exact comp_mem_subgroup i a q
      (hU.2 ▸ SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩))

/-- The restriction commutes with the original root inclusions. -/
theorem rootMap_comp : rootMap i a q hU hV ≫ jV = jU ≫ q :=
  hV.factorHom_comp _ _

end Restriction

section Field

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hq : Smooth q.hom.hom.left)

include hS ha hq

/-- The actual differential of a smooth homomorphism maps the full intrinsic
root tangent image onto the target root tangent image. -/
theorem map_tangentSubmodule_subgroup_eq_of_smooth :
    (tangentSubmodule (subgroup i a)).map (Lie.targetMapLinear q k) =
      tangentSubmodule (subgroup (i ≫ q) a) := by
  rw [tangentSubmodule_subgroup i a hS ha,
    tangentSubmodule_subgroup (i ≫ q) a hS ha]
  apply map_semigroupWeightSpan_eq_of_smooth
    (AutomorphicAction.conjugation i) (AutomorphicAction.conjugation (i ≫ q)) hS q
    (fun _ s x => ?_) hq
  simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

variable {U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
    {jU : U ⟶ G} {jV : V ⟶ H}
    (hU : (subgroup i a).IsRepresentedBy jU)
    (hV : (subgroup (i ≫ q) a).IsRepresentedBy jV)

/-- The induced map between actual root representatives has surjective
differential, without assuming connectedness of the ambient groups. -/
theorem rootMap_differential_surjective_of_smooth :
    Function.Surjective (Lie.targetMapLinear (rootMap i a q hU hV) k) := by
  let : Mono jU.hom.hom := hU.1
  let : Mono jV.hom.hom := hV.1
  have hUr : tangentSubmodule (subgroup i a) =
      LinearMap.range (Lie.targetMapLinear jU k) := by
    rw [← hU.2, tangentSubmodule_range]
  have hVr : tangentSubmodule (subgroup (i ≫ q) a) =
      LinearMap.range (Lie.targetMapLinear jV k) := by
    rw [← hV.2, tangentSubmodule_range]
  intro Y
  have hY : Lie.targetMapLinear jV k Y ∈
      (tangentSubmodule (subgroup i a)).map (Lie.targetMapLinear q k) := by
    rw [map_tangentSubmodule_subgroup_eq_of_smooth i a q hS ha hq, hVr]
    exact ⟨Y, rfl⟩
  obtain ⟨X, hX, hXY⟩ := hY
  rw [hUr] at hX
  obtain ⟨Z, rfl⟩ := hX
  refine ⟨Z, ?_⟩
  apply Lie.targetMapLinear_injective jV k
  have hc :
      Lie.targetMapLinear jV k (Lie.targetMapLinear (rootMap i a q hU hV) k Z) =
        Lie.targetMapLinear q k (Lie.targetMapLinear jU k Z) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [lieKernelTargetLinear_val, Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : U ⟶ H => Z.toMul.val ≫ f.hom.hom)
        (rootMap_comp i a q hU hV)
  exact hc.trans hXY

/-- A smooth ambient homomorphism restricts to a smooth surjection between
the intrinsic root representatives. -/
theorem rootMap_smooth_surjective :
    Smooth (rootMap i a q hU hV).hom.hom.left ∧
      Surjective (rootMap i a q hU hV).hom.hom.left := by
  have hUs : Smooth U.X.hom := smooth_of_isRepresentedBy_subgroup hS i a ha hU
  have hVs : Smooth V.X.hom := smooth_of_isRepresentedBy_subgroup hS (i ≫ q) a ha hV
  have hVc : ConnectedSpace V.X.left :=
    connected_of_isRepresentedBy_subgroup hS (i ≫ q) a ha dynamicConnected hV
  exact Lie.smoothSurjectiveOfSurjectiveDifferential k U V hUs hVs
    inferInstance inferInstance hVc (rootMap i a q hU hV)
    (rootMap_differential_surjective_of_smooth i a q hS ha hq hU hV)

/-- Over an algebraically closed field, every rational target root point
lifts through the same restricted homomorphism. -/
theorem rootMap_rationalPoints_surjective [IsAlgClosed k] :
    Function.Surjective
      (fun (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X) =>
        x ≫ (rootMap i a q hU hV).hom.hom) := by
  let : Smooth U.X.hom := smooth_of_isRepresentedBy_subgroup hS i a ha hU
  let : Smooth V.X.hom := smooth_of_isRepresentedBy_subgroup hS (i ≫ q) a ha hV
  have hsurj := (rootMap_smooth_surjective i a q hS ha hq hU hV).2
  intro y
  exact Lie.exists_rational_lift_of_mem_range (rootMap i a q hU hV) y
    (hsurj.surj _)

omit hU hV [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] in
/-- Over an algebraically closed field, every rational point of the intrinsic
target root functor has a source root lift under the original homomorphism. -/
theorem exists_root_point_lift_of_smooth [IsAlgClosed k]
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X)
    (hg : g ∈ (subgroup (i ≫ q) a).carrier _) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X,
      x ∈ (subgroup i a).carrier _ ∧ x ≫ q.hom.hom = g := by
  obtain ⟨U, jU, hU, hUc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hS i a ha
  obtain ⟨V, jV, hV, hVc, _, _⟩ :=
    subgroup_has_smooth_closed_representative hS (i ≫ q) a ha
  let : IsAffineHom U.X.hom := by
    let : IsClosedImmersion jU.hom.hom.left := hUc
    rw [← jU.hom.hom.w]
    infer_instance
  let : IsAffineHom V.X.hom := by
    let : IsClosedImmersion jV.hom.hom.left := hVc
    rw [← jV.hom.hom.w]
    infer_instance
  rw [← hV.2] at hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨z, hz⟩ := rootMap_rationalPoints_surjective i a q hS ha hq hU hV y
  change z ≫ (rootMap i a q hU hV).hom.hom = y at hz
  refine ⟨z ≫ jU.hom.hom, hU.2 ▸ SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩, ?_⟩
  have hc := congrArg (fun f : U ⟶ H => z ≫ f.hom.hom)
    (rootMap_comp i a q hU hV)
  calc
    (z ≫ jU.hom.hom) ≫ q.hom.hom =
        (z ≫ (rootMap i a q hU hV).hom.hom) ≫ jV.hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hc.symm
    _ = y ≫ jV.hom.hom := by rw [hz]

end Field

end Langlands.GroupScheme.RelativeRoot
