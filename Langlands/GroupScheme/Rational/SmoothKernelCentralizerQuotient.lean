import Langlands.GroupScheme.Rational.KernelCentralizerProportionalRoots
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.SmoothTangentWeights
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof

/-! # Smooth quotients of full character-kernel identity centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section Restriction

variable {B : Scheme.{u}} {S : CommGroupScheme B}
    {G H C E : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    {jC : C ⟶ G} {jE : E ⟶ H}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hE : (kernelCentralizer (i ≫ q) a).IsRepresentedBy jE)

/-- Restriction to representatives of the full character-kernel centralizers,
using commutation on every test scheme. -/
def kernelCentralizerMap : C ⟶ E :=
  hE.factorHom (jC ≫ q) (by
    intro X g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    change (x ≫ jC.hom.hom) ≫ q.hom.hom ∈
      (kernelCentralizer (i ≫ q) a).carrier X
    exact map_mem_kernelCentralizer q i a
      (hC.2 ▸ SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩))

@[reassoc]
theorem kernelCentralizerMap_comp :
    kernelCentralizerMap i a q hC hE ≫ jE = jC ≫ q :=
  hE.factorHom_comp _ _

end Restriction

section Identity

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H C E : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth E.X.hom] [IsAffineHom E.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    {jC : C ⟶ G} {jE : E ⟶ H}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hE : (kernelCentralizer (i ≫ q) a).IsRepresentedBy jE)

/-- The actual restricted homomorphism between identity components. -/
def kernelCentralizerIdentityMap : identityComponent C ⟶ identityComponent E :=
  IdentityComponent.factor E (identityComponentι C ≫ kernelCentralizerMap i a q hC hE)

@[reassoc]
theorem kernelCentralizerIdentityMap_comp :
    kernelCentralizerIdentityMap i a q hC hE ≫ identityComponentι E =
      identityComponentι C ≫ kernelCentralizerMap i a q hC hE :=
  IdentityComponent.factor_identityComponentι E _

@[reassoc]
theorem kernelCentralizerIdentityMap_comp_ambient :
    kernelCentralizerIdentityMap i a q hC hE ≫ (identityComponentι E ≫ jE) =
      (identityComponentι C ≫ jC) ≫ q := by
  rw [← Category.assoc, kernelCentralizerIdentityMap_comp, Category.assoc,
    kernelCentralizerMap_comp, Category.assoc]

/-- The same split torus commutes with restriction to identity components. -/
theorem kernelCentralizerIdentityMap_torus (hS : IsSplitTorus S.toGrp) :
    kernelCentralizerIdentityTorus i hS a jC hC ≫
        kernelCentralizerIdentityMap i a q hC hE =
      kernelCentralizerIdentityTorus (i ≫ q) hS a jE hE := by
  apply (cancel_mono (identityComponentι E)).mp
  apply hE.hom_ext
  calc
    (kernelCentralizerIdentityTorus i hS a jC hC ≫
        kernelCentralizerIdentityMap i a q hC hE ≫ identityComponentι E) ≫ jE =
        kernelCentralizerIdentityTorus i hS a jC hC ≫
          (kernelCentralizerIdentityMap i a q hC hE ≫
            (identityComponentι E ≫ jE)) := by simp only [Category.assoc]
    _ = i ≫ q := by
      rw [kernelCentralizerIdentityMap_comp_ambient, ← Category.assoc,
        kernelCentralizerIdentityTorus_comp_ambient]
    _ = (kernelCentralizerIdentityTorus (i ≫ q) hS a jE hE ≫
        identityComponentι E) ≫ jE := by
      rw [Category.assoc, kernelCentralizerIdentityTorus_comp_ambient]

end Identity

section Smooth

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S) (q : G ⟶ H)
    (hS : IsSplitTorus S.toGrp) (hq : Smooth q.hom.hom.left)

include hS hq in
/-- A smooth ambient map preserves the exact span of all integral character
weights, including zero. -/
theorem map_integralWeightSpan_eq_of_smooth :
    (integralWeightSpan i a).map (Lie.targetMapLinear q k) =
      integralWeightSpan (i ≫ q) a := by
  rw [← semigroupWeightSpan_zmultiples, ← semigroupWeightSpan_zmultiples]
  apply map_semigroupWeightSpan_eq_of_smooth
    (AutomorphicAction.conjugation i) (AutomorphicAction.conjugation (i ≫ q)) hS q
    (fun _ s x => ?_) hq
  simp only [AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

variable {C E : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    [Smooth E.X.hom] [IsAffineHom E.X.hom]
    {jC : C ⟶ G} {jE : E ⟶ H}
    (hC : (kernelCentralizer i a).IsRepresentedBy jC)
    (hE : (kernelCentralizer (i ≫ q) a).IsRepresentedBy jE)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (identityComponent C) A) :=
  lieKernelCommGroup (identityComponent C)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (identityComponent C) A)) :=
  lieKernelModule (identityComponent C)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    CommGroup (lieKernel (identityComponent E) A) :=
  lieKernelCommGroup (identityComponent E)

local instance (A : Type u) [CommRing A] [Algebra k A] :
    Module A (Additive (lieKernel (identityComponent E) A)) :=
  lieKernelModule (identityComponent E)

include hS hq

/-- The exact ambient Lie images imply surjectivity of the differential on the
actual identity-component restriction. -/
theorem kernelCentralizerIdentityMap_differential_surjective :
    Function.Surjective
      (Lie.targetMapLinear (kernelCentralizerIdentityMap i a q hC hE) k) := by
  let : Mono jC.hom.hom := hC.1
  let : Mono jE.hom.hom := hE.1
  let : Mono (identityComponentι C ≫ jC).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ jC.hom.hom)
    infer_instance
  let : Mono (identityComponentι E ≫ jE).hom.hom := by
    change Mono ((identityComponentι E).hom.hom ≫ jE.hom.hom)
    infer_instance
  have hCr : LinearMap.range (Lie.targetMapLinear (identityComponentι C ≫ jC) k) =
      integralWeightSpan i a := by
    simpa only [tangentSubmodule_range] using
      (hasLieImage_iff_tangentSubmodule_eq _ _).mp
        (kernelCentralizerIdentity_hasLieImage i hS a jC hC)
  have hEr : LinearMap.range (Lie.targetMapLinear (identityComponentι E ≫ jE) k) =
      integralWeightSpan (i ≫ q) a := by
    simpa only [tangentSubmodule_range] using
      (hasLieImage_iff_tangentSubmodule_eq _ _).mp
        (kernelCentralizerIdentity_hasLieImage (i ≫ q) hS a jE hE)
  intro Y
  have hY : Lie.targetMapLinear (identityComponentι E ≫ jE) k Y ∈
      (integralWeightSpan i a).map (Lie.targetMapLinear q k) := by
    rw [map_integralWeightSpan_eq_of_smooth i a q hS hq, ← hEr]
    exact ⟨Y, rfl⟩
  obtain ⟨X, hX, hXY⟩ := hY
  rw [← hCr] at hX
  obtain ⟨Z, rfl⟩ := hX
  refine ⟨Z, ?_⟩
  apply Lie.targetMapLinear_injective (identityComponentι E ≫ jE) k
  have hc := congrArg
    (fun f : identityComponent C ⟶ H => Lie.targetMapLinear f k Z)
    (kernelCentralizerIdentityMap_comp_ambient i a q hC hE)
  simpa only [Lie.targetMapLinear_comp, LinearMap.comp_apply] using hc.trans hXY

/-- A smooth homomorphism restricts to a smooth surjection between the identity
components of represented full character-kernel centralizers. -/
theorem kernelCentralizerIdentityMap_smooth_surjective :
    Smooth (kernelCentralizerIdentityMap i a q hC hE).hom.hom.left ∧
      Surjective (kernelCentralizerIdentityMap i a q hC hE).hom.hom.left :=
  Lie.smoothSurjectiveOfSurjectiveDifferential k (identityComponent C) (identityComponent E)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (kernelCentralizerIdentityMap i a q hC hE)
    (kernelCentralizerIdentityMap_differential_surjective i a q hS hq hC hE)

/-- Over an algebraically closed field, every rational point of the target
identity component lifts through the actual restricted homomorphism. -/
theorem kernelCentralizerIdentityMap_rationalPoints_surjective [IsAlgClosed k] :
    Function.Surjective
      (fun (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (identityComponent C).X) =>
        x ≫ (kernelCentralizerIdentityMap i a q hC hE).hom.hom) := by
  have hsurj := (kernelCentralizerIdentityMap_smooth_surjective i a q hS hq hC hE).2
  intro y
  exact Lie.exists_rational_lift_of_mem_range
    (kernelCentralizerIdentityMap i a q hC hE) y (hsurj.surj _)

end Smooth

end Langlands.GroupScheme.RelativeRoot
