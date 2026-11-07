import Langlands.GroupScheme.Rational.RootPointLieEquiv
import Langlands.GroupScheme.Rational.VectorPointLieNaturality

/-! # Independence of the representative in the actual root-point Lie comparison -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Representatives

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G U V : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {j' : V ⟶ G} (hj' : (subgroup i a).IsRepresentedBy j')

/-- The canonical group-scheme isomorphism between two representatives
of the same intrinsic root subgroup. -/
def rootSubgroupRepresentativeIso : U ≅ V :=
  hj.isoOfIsRepresentedBy hj'

/-- The canonical isomorphism between representatives intertwines the actual torus actions. -/
theorem subgroupAction_isoOfIsRepresentedBy
    (X : Over B) (s : X ⟶ S.X) (x : X ⟶ U.X) :
    (subgroupAction i a j hj).act s x ≫ (rootSubgroupRepresentativeIso i a hj hj').hom.hom.hom =
      (subgroupAction i a j' hj').act s
        (x ≫ (rootSubgroupRepresentativeIso i a hj hj').hom.hom.hom) := by
  let : Mono j'.hom.hom := hj'.1
  have hcomp :
      (rootSubgroupRepresentativeIso i a hj hj').hom.hom.hom ≫ j'.hom.hom = j.hom.hom :=
    congrArg (fun f : U ⟶ G => f.hom.hom) (hj.isoOfIsRepresentedBy_hom_comp hj')
  apply (cancel_mono j'.hom.hom).mp
  rw [Category.assoc, hcomp, subgroupAction_act_comp, subgroupAction_act_comp,
    Category.assoc, hcomp]

/-- The isomorphism of representatives presents exactly the same subgroup point. -/
theorem pointsEquiv_isoOfIsRepresentedBy (X : Over B) (x : X ⟶ U.X) :
    hj'.pointsEquiv X (x ≫ (rootSubgroupRepresentativeIso i a hj hj').hom.hom.hom) =
      hj.pointsEquiv X x := by
  apply Subtype.ext
  change (x ≫ (hj.isoOfIsRepresentedBy hj').hom.hom.hom) ≫ j'.hom.hom = x ≫ j.hom.hom
  rw [Category.assoc]
  exact congrArg (fun f : U ⟶ G => x ≫ f.hom.hom) (hj.isoOfIsRepresentedBy_hom_comp hj')

end Representatives

section RootPoints

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]

/-- The root-point comparison is independent of the chosen affine representative. -/
theorem representedRootPointLieEquiv_eq
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {j' : V ⟶ G} (hj' : (subgroup i a).IsRepresentedBy j') :
    representedRootPointLieEquiv hS i ha hhigh hj =
      representedRootPointLieEquiv hS i ha hhigh hj' := by
  let ψ := rootSubgroupRepresentativeIso i a hj hj'
  have hcomp : ψ.hom.hom.hom ≫ j'.hom.hom = j.hom.hom :=
    congrArg (fun f : U ⟶ G => f.hom.hom) (hj.isoOfIsRepresentedBy_hom_comp hj')
  let cU := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  let cV := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj'
  apply AddEquiv.ext
  intro v
  apply Subtype.ext
  let x := (hj.pointsEquiv _).symm v.toMul
  have hx : hj.pointsEquiv _ x = v.toMul := (hj.pointsEquiv _).apply_symm_apply _
  have hp : hj'.pointsEquiv _ (rationalPoints.map ψ.hom x) = hj.pointsEquiv _ x :=
    pointsEquiv_isoOfIsRepresentedBy i a hj hj' _ x
  have hnat := vectorPointLieEquiv_equivariantIso hS ha cU.2.property cV.2.property ψ
    (subgroupAction_isoOfIsRepresentedBy i a hj hj') (CommAlgCat.of k k)
    (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x))
  have haff : GaloisPointComparison.rationalCoeffEquiv k V (rationalPoints.map ψ.hom x) =
      GaloisPointComparison.rationalCoeffEquiv k U x ≫ ψ.hom.hom.hom :=
    GaloisPointComparison.rationalCoeffEquiv_map k ψ.hom x
  simp only [toMul_ofMul] at hnat
  change (representedRootPointLieEquiv hS i ha hhigh hj (Additive.ofMul v.toMul) :
      Additive (lieKernel G k)) =
    (representedRootPointLieEquiv hS i ha hhigh hj' (Additive.ofMul v.toMul) :
      Additive (lieKernel G k))
  rw [← hx]
  calc
    _ = Lie.targetMapLinear j k
        (vectorPointLieEquiv cU.2.val cU.2.property.1 (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x))) :=
      representedRootPointLieEquiv_apply hS i ha hhigh hj x
    _ = Lie.targetMapLinear j' k
        (vectorPointLieEquiv cV.2.val cV.2.property.1 (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k V
            (rationalPoints.map ψ.hom x)))) := by
      calc
        _ = Lie.targetMapLinear j' k
            (Lie.targetMapLinear ψ.hom k
              (vectorPointLieEquiv cU.2.val cU.2.property.1 (CommAlgCat.of k k)
                (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U x)))) := by
          apply Additive.toMul.injective
          apply Subtype.ext
          simp only [lieKernelTargetLinear_val, Category.assoc, hcomp]
        _ = _ := by
          simpa only [haff] using congrArg (Lie.targetMapLinear j' k) hnat
    _ = (representedRootPointLieEquiv hS i ha hhigh hj'
        (Additive.ofMul (hj'.pointsEquiv _ (rationalPoints.map ψ.hom x))) :
          Additive (lieKernel G k)) :=
      (representedRootPointLieEquiv_apply hS i ha hhigh hj' _).symm
    _ = _ := by rw [hp]

omit [IsAffineHom V.X.hom] in
/-- The intrinsic chosen comparison agrees with the comparison through every affine representative. -/
theorem rootPointLieEquiv_eq_represented
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) :
    rootPointLieEquiv hS i ha hhigh = representedRootPointLieEquiv hS i ha hhigh hj := by
  obtain ⟨V', hV', j', hj', h⟩ := rootPointLieEquiv_exists_representative hS i ha hhigh
  let : IsAffineHom V'.X.hom := hV'
  exact h.trans (representedRootPointLieEquiv_eq hS i ha hhigh hj' hj)

end RootPoints

end Langlands.GroupScheme.RelativeRoot
