import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget
import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections

/-! # Actual rational geometric stabilizer and radical projection maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

private theorem map_eq_of_surjective_restriction
    {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) (K : Subgroup B) (g : H →* K)
    (hg : ∀ h : H, (g h : B) = f h)
    (hsurj : Function.Surjective g) : H.map f = K := by
  ext b
  constructor
  · rintro ⟨a, ha, hab⟩
    have hf : f a ∈ K := (hg ⟨a, ha⟩) ▸ (g ⟨a, ha⟩).property
    exact hab ▸ hf
  · intro hb
    obtain ⟨a, ha⟩ := hsurj ⟨b, hb⟩
    exact ⟨a, a.property, (hg a).symm.trans (congrArg Subtype.val ha)⟩

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

private theorem projection_mem_of_closed_stable [IsSeparated G.X.hom]
    (I : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (α : cocharacterLattice T)
    (hP : standardParabolic i ν (rootSet i ν I) =
      Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i))
    (hM : standardLevi i ν (rootSet i ν I) =
      Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i))
    (hU : standardUnipotent i ν (rootSet i ν I) =
      Dynamic.unipotent (CommGroupScheme.groupHom α ≫ i))
    {H : GroupScheme (Spec (CommRingCat.of k))}
    {F : SubgroupFunctor G} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (hF : (AutomorphicAction.conjugation (CommGroupScheme.groupHom α ≫ i)).IsStable F)
    (p : parabolic i ν I) (hp : (p : RationalPoint k G.X) ∈ F.rationalPoints) :
    (d.projection p : RationalPoint k G.X) ∈ F.rationalPoints := by
  have hPp : parabolic i ν I =
      (Dynamic.parabolic (CommGroupScheme.groupHom α ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg SubgroupFunctor.rationalPoints hP
  have hMp := congrArg SubgroupFunctor.rationalPoints hM
  have hUp := congrArg SubgroupFunctor.rationalPoints hU
  let χ := CommGroupScheme.groupHom α ≫ i
  let pd : (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) :=
    ⟨p, hPp ▸ p.property⟩
  have heq : (d.projection p : RationalPoint k G.X) = Dynamic.limit χ pd :=
    projection_eq_dynamic_limit i ν I d χ hPp hMp hUp p
  have hl : Dynamic.HasLimit χ (p : RationalPoint k G.X) (Dynamic.limit χ pd) :=
    Dynamic.hasLimit_limit χ pd
  rw [heq]
  exact Dynamic.HasLimit.mem_of_isClosedSubgroup_of_isStable χ hj hjc hF hp hl

omit [IsAffineHom G.X.hom] in
private theorem unipotent_points_conjugate
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (g : GroupScheme.rationalPoints G) :
    (Dynamic.unipotent (χ ≫ (G.innerIso g).hom)).rationalPoints =
      (Dynamic.unipotent χ).rationalPoints.map (MulAut.conj g).toMonoidHom := by
  have h := Dynamic.unipotent_eq_comap_of_iso χ (G.innerIso g)
  have hc := congrArg
    (fun F : SubgroupFunctor G => F.comap (G.innerIso g).inv) h
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  rw [← hc, SubgroupFunctor.rationalPoints_comap_innerIso_inv]

/-- The actual Levi projection preserves the forward conjugate of any standard
parabolic, for every actual normalizer point and without a minimality premise. -/
theorem projection_mem_conjugate_parabolic
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (p : parabolic i ν I)
    (hp : (p : RationalPoint k G.X) ∈
      (parabolic i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom) :
    (d.projection p : RationalPoint k G.X) ∈
      (parabolic i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom := by
  have := hG.isSeparated
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨α, hα⟩, hcmpI⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hPI, hMI, hUI⟩ := hcmpI α hα
  obtain ⟨⟨β, hβ⟩, hcmpJ⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨hPJ, _, _⟩ := hcmpJ β hβ
  let ns := (normalizerEquiv i hN).symm n
  let βn := cocharacterAut (normalizingAut i ns) β
  have hconj : CommGroupScheme.groupHom βn ≫ i =
      (CommGroupScheme.groupHom β ≫ i) ≫
        (G.innerIso (n : GroupScheme.rationalPoints G)).hom :=
    groupHom_cocharacterAut_comp i ns β
  have hpoints : (Dynamic.parabolic (CommGroupScheme.groupHom βn ≫ i)).rationalPoints =
      (parabolic i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom := by
    rw [hconj, Dynamic.rationalPoints_parabolic_conjugate]
    rw [← hPJ]
  have hF := (Dynamic.parabolic_isStable_conjugation i
    (CommGroupScheme.groupHom βn)).restrict (CommGroupScheme.groupHom α)
  rw [AutomorphicAction.restrict_conjugation] at hF
  rw [← hpoints] at hp ⊢
  exact projection_mem_of_closed_stable i ν I d α hPI hMI hUI
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _) hF p hp

/-- The actual Levi projection also preserves the forward conjugate of a
standard radical. This supplies the containment part of the source image. -/
theorem projection_mem_conjugate_unipotent
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (p : parabolic i ν I)
    (hp : (p : RationalPoint k G.X) ∈
      (unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom) :
    (d.projection p : RationalPoint k G.X) ∈
      (unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom := by
  have := hG.isSeparated
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨⟨α, hα⟩, hcmpI⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨hPI, hMI, hUI⟩ := hcmpI α hα
  obtain ⟨⟨β, hβ⟩, hcmpJ⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨_, _, hUJ⟩ := hcmpJ β hβ
  let ns := (normalizerEquiv i hN).symm n
  let βn := cocharacterAut (normalizingAut i ns) β
  have hconj : CommGroupScheme.groupHom βn ≫ i =
      (CommGroupScheme.groupHom β ≫ i) ≫
        (G.innerIso (n : GroupScheme.rationalPoints G)).hom :=
    groupHom_cocharacterAut_comp i ns β
  have hpoints : (Dynamic.unipotent (CommGroupScheme.groupHom βn ≫ i)).rationalPoints =
      (unipotent i ν J).map (MulAut.conj (n : RationalPoint k G.X)).toMonoidHom := by
    rw [hconj, unipotent_points_conjugate]
    rw [← hUJ]
  have hF := (Dynamic.unipotent_isStable_conjugation i
    (CommGroupScheme.groupHom βn)).restrict (CommGroupScheme.groupHom α)
  rw [AutomorphicAction.restrict_conjugation] at hF
  rw [← hpoints] at hp ⊢
  exact projection_mem_of_closed_stable i ν I d α hPI hMI hUI
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _) hF p hp

section ProjectionMaps

variable
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)

/-- The actual target-side orbit stabilizer projects to the literal parabolic
intersection inside the target Levi. -/
def stabilizerProjection
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν I) →*
    (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (levi i ν I) where
  toFun p := ⟨d.projection p.val, (d.projection p.val).property,
    projection_mem_conjugate_parabolic i ν hStandard hG hi hν hN I J d n
      p.val p.property.2⟩
  map_one' := Subtype.ext (map_one d.projection)
  map_mul' p q := Subtype.ext (map_mul d.projection p.val q.val)

/-- On ambient points the restricted map is exactly the chosen Levi
projection; it introduces no conjugation or auxiliary coordinate map. -/
@[simp] theorem stabilizerProjection_apply
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (p : (geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν I)) :
    (stabilizerProjection i ν hStandard hG hi hν hN I J d n p : levi i ν I) =
      d.projection p.val := rfl

/-- Every point of the actual target intersection is its own lift through
the Levi section of the ambient decomposition. -/
theorem stabilizerProjection_surjective
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    Function.Surjective (stabilizerProjection i ν hStandard hG hi hν hN I J d n) := by
  intro m
  refine ⟨⟨⟨m.val, d.levi_le m.val.property⟩,
    d.levi_le m.val.property, m.property.2⟩, ?_⟩
  exact Subtype.ext (d.projection_levi m.val)

include hStandard hG hi hν hN in
/-- The image under the ambient Levi projection is the literal target
intersection subgroup, with its original `subgroupOf` restriction. -/
theorem map_stabilizer_eq
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    ((geometricTargetIntersection (parabolic i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν I)).map d.projection =
    (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (levi i ν I) := by
  exact map_eq_of_surjective_restriction d.projection _ _
    (stabilizerProjection i ν hStandard hG hi hν hN I J d n)
    (fun _ => rfl)
    (stabilizerProjection_surjective i ν hStandard hG hi hν hN I J d n)

/-- The inducing-side Levi projection on the actual inverse-conjugate target
radical has values in the literal radical intersection inside the source Levi. -/
def sourceRadicalProjection
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    (geometricSourceIntersection (unipotent i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν J) →*
    (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
      (n : RationalPoint k G.X)).subgroupOf (levi i ν J) where
  toFun p := ⟨d.projection p.val, (d.projection p.val).property,
    projection_mem_conjugate_unipotent i ν hStandard hG hi hν hN J I d n⁻¹
      p.val p.property.2⟩
  map_one' := Subtype.ext (map_one d.projection)
  map_mul' p q := Subtype.ext (map_mul d.projection p.val q.val)

/-- The source-radical map is the original inducing projection on every
ambient point. -/
@[simp] theorem sourceRadicalProjection_apply
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (p : (geometricSourceIntersection (unipotent i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν J)) :
    (sourceRadicalProjection i ν hStandard hG hi hν hN I J d n p : levi i ν J) =
      d.projection p.val := rfl

/-- The actual Levi section lifts each point of the source radical
intersection without changing its ambient rational point. -/
theorem sourceRadicalProjection_surjective
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    Function.Surjective (sourceRadicalProjection i ν hStandard hG hi hν hN I J d n) := by
  intro m
  refine ⟨⟨⟨m.val, d.levi_le m.val.property⟩,
    d.levi_le m.val.property, m.property.2⟩, ?_⟩
  exact Subtype.ext (d.projection_levi m.val)

include hStandard hG hi hν hN in
/-- The literal source-radical projection image, at every normalizer point
and for every decomposition of the original standard point subgroups. -/
theorem map_sourceRadical_eq
    (I J : Finset (SimpleRoot i ν))
    (d : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) :
    ((geometricSourceIntersection (unipotent i ν I) (parabolic i ν J)
      (n : RationalPoint k G.X)).subgroupOf (parabolic i ν J)).map d.projection =
    (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
      (n : RationalPoint k G.X)).subgroupOf (levi i ν J) := by
  exact map_eq_of_surjective_restriction d.projection _ _
    (sourceRadicalProjection i ν hStandard hG hi hν hN I J d n)
    (fun _ => rfl)
    (sourceRadicalProjection_surjective i ν hStandard hG hi hν hN I J d n)

end ProjectionMaps

end Langlands.Aubert.General.RationalPointFamily
