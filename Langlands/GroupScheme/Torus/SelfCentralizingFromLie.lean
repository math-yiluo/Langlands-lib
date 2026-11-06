import Langlands.GroupScheme.Lie.SelfCentralizing
import Langlands.GroupScheme.Lie.DimensionInduction
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.CentralizerSmooth
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing

/-! # Detecting an actual self-centralizing torus from its zero Lie weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section GeneralRing

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
  {G C : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom T.toGrp.X.hom] [IsAffineHom C.X.hom]
  (i : T.toGrp ⟶ G) {j : C ⟶ G}
  (hrep : (torusCentralizer i).IsRepresentedBy j)

/-- Surjectivity onto the zero weight gives surjectivity onto the actual Lie
module of any representative of the whole-torus centralizer. -/
theorem surjective_torusCentralizerFactor_of_surjective_zeroWeightMap
    (hsurj : Function.Surjective (Lie.zeroWeightMap i)) :
    Function.Surjective (Lie.targetMapLinear (torusCentralizerFactor i hrep) R) := by
  let := hrep.1
  intro Y
  have hY : Lie.targetMapLinear j R Y ∈ weightSpace i 0 := by
    apply Lie.mem_weightSpace_zero_of_mem_torusCentralizer i (Lie.targetMap j R Y.toMul)
    rw [← hrep.2]
    exact ⟨Y.toMul.val, rfl⟩
  obtain ⟨X, hX⟩ := hsurj ⟨Lie.targetMapLinear j R Y, hY⟩
  refine ⟨X, Lie.targetMapLinear_injective j R ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  change (X.toMul.val ≫ (torusCentralizerFactor i hrep).hom.hom) ≫ j.hom.hom =
    Y.toMul.val ≫ j.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, torusCentralizerFactor_comp]
  exact congrArg (fun Z : weightSpace i 0 => Z.val.toMul.val) hX

end GeneralRing

section Field

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom T.toGrp.X.hom] [IsAffineHom C.X.hom]
  [Smooth T.toGrp.X.hom] [Smooth C.X.hom] [ConnectedSpace C.X.left]
  (i : T.toGrp ⟶ G) {j : C ⟶ G}
  (hrep : (torusCentralizer i).IsRepresentedBy j) (hj : IsClosedSubgroup j)
  (hi : IsClosedSubgroup i)

/-- A smooth connected centralizer is the given smooth closed commutative
subgroup when its zero-weight differential is surjective. The forward map
is the canonical factor of the specified inclusion. -/
def torusCentralizerFactorIsoOfZeroWeight
    (hsurj : Function.Surjective (Lie.zeroWeightMap i)) : T.toGrp ≅ C := by
  let f := torusCentralizerFactor i hrep
  have hf : IsClosedSubgroup f := isClosedSubgroup_torusCentralizerFactor i hrep hj hi
  have : IsIso f := Lie.isIso_of_surjective_targetMapLinear f hf
    (surjective_torusCentralizerFactor_of_surjective_zeroWeightMap i hrep hsurj)
  exact asIso f

@[simp] theorem torusCentralizerFactorIsoOfZeroWeight_hom
    (hsurj : Function.Surjective (Lie.zeroWeightMap i)) :
    (torusCentralizerFactorIsoOfZeroWeight i hrep hj hi hsurj).hom =
      torusCentralizerFactor i hrep := rfl

theorem torusCentralizerFactorIsoOfZeroWeight_hom_comp
    (hsurj : Function.Surjective (Lie.zeroWeightMap i)) :
    (torusCentralizerFactorIsoOfZeroWeight i hrep hj hi hsurj).hom ≫ j = i :=
  torusCentralizerFactor_comp i hrep

end Field

section SplitTorus

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [IsAffineHom T.toGrp.X.hom]
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)

include hT hi

/-- A closed split torus is its whole-group centralizer in a smooth connected
affine group if its differential fills the zero adjoint weight. -/
theorem torusCentralizer_eq_range_of_surjective_zeroWeightMap
    (hsurj : Function.Surjective (Lie.zeroWeightMap i)) :
    torusCentralizer i = SubgroupFunctor.range i := by
  let := hT.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨C, j, hj, hC, hrep⟩ :=
    torusCentralizer_hasSmoothClosedRepresentative i ⟨hT, hi⟩ inferInstance
  let := hC
  let := hj.isAffineHom
  let := hT.connectedSpace_centralizer i hrep
  let e := torusCentralizerFactorIsoOfZeroWeight i hrep hj hi hsurj
  calc
    torusCentralizer i = SubgroupFunctor.range j := hrep.2.symm
    _ = SubgroupFunctor.range (e.hom ≫ j) := (SubgroupFunctor.range_iso_comp e j).symm
    _ = SubgroupFunctor.range i := congrArg SubgroupFunctor.range
      (torusCentralizerFactorIsoOfZeroWeight_hom_comp i hrep hj hi hsurj)

/-- Equality of the two finite dimensions suffices; no reductivity assumption
is used in this field criterion. -/
theorem torusCentralizer_eq_range_of_finrank_zeroWeight
    (hdim : Module.finrank k (weightSpace i 0) =
      Module.finrank k (Additive (lieKernel T.toGrp k))) :
    torusCentralizer i = SubgroupFunctor.range i := by
  let := hT.smooth
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  apply torusCentralizer_eq_range_of_surjective_zeroWeightMap i hT hi
  exact (LinearEquiv.ofInjectiveOfFinrankEq (K := k) (Lie.zeroWeightMap i)
    (Lie.zeroWeightMap_injective i) hdim.symm).surjective

/-- The same Lie-dimension test proves geometric maximality of the actual
closed split torus. -/
theorem isMaximalTorus_of_finrank_zeroWeight
    (hdim : Module.finrank k (weightSpace i 0) =
      Module.finrank k (Additive (lieKernel T.toGrp k))) :
    IsMaximalTorus i :=
  isMaximalTorus_of_torusCentralizer_eq hT.isTorus hi
    (torusCentralizer_eq_range_of_finrank_zeroWeight i hT hi hdim)

end SplitTorus

end Langlands.GroupScheme
