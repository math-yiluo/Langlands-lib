import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeStatement
import Langlands.GroupScheme.Rational.NormalSplitTorusCentrality
import Langlands.GroupScheme.Torus.CentralExtensionProof
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Central tori in the quotient by a largest central torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

/-- A normal closed torus in a smooth connected affine group is central. -/
theorem IsTorus.isCentral_of_isNormal
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    (hi : IsClosedSubgroup i) (hn : (SubgroupFunctor.range i).IsNormal) :
    IsCentral i := by
  obtain ⟨K, hK, aK, hs⟩ := hT
  let : Field K := hK
  let : Algebra k K := aK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Surjective b := (fieldExtension_fpqc k K).1
  let : Flat b := (fieldExtension_fpqc k K).2.1
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  let : IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left :=
    hi.baseChange b
  apply IsCentral.of_baseChange b
  apply isCentral_of_isNormal_of_isSplitTorus
    (T := (CommGroupScheme.baseChange b).obj T) _ hs
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hn.baseChange b

/-- No closed central torus survives in the quotient by a largest central subtorus. -/
theorem IsLargestCentralSubtorus.central_torus_quotient_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} {z : Z.toGrp ⟶ G}
    (hz : IsLargestCentralSubtorus z)
    {Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (a : T.toGrp ⟶ Q)
    (hT : IsTorus T.toGrp) (ha : IsClosedSubgroup a) (hac : IsCentral a) :
    a = 0 := by
  have hzq : z ≫ q = 0 := by
    apply (Grp.forget _).map_injective
    apply (mem_range_kernelι_iff q _).mp
    rw [hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  let E : GroupScheme (Spec (CommRingCat.of k)) := pullback a q
  let p : E ⟶ T.toGrp := pullback.fst a q
  let e : E ⟶ G := pullback.snd a q
  have hpb : IsPullback p.hom.hom e.hom.hom a.hom.hom q.hom.hom :=
    IsPullback.map (Grp.forget _) (IsPullback.of_hasPullback a q)
  have hpbS : IsPullback p.hom.hom.left e.hom.hom.left a.hom.hom.left q.hom.hom.left :=
    IsPullback.map (Over.forget _) hpb
  let zE : Z.toGrp ⟶ E := pullback.lift 0 z (by rw [zero_comp, hzq])
  have hzEp : zE ≫ p = 0 := pullback.lift_fst _ _ _
  have hzEe : zE ≫ e = z := pullback.lift_snd _ _ _
  have hzEp' : zE.hom.hom ≫ p.hom.hom = 1 :=
    congrArg (fun f => f.hom.hom) hzEp
  have hzEe' : zE.hom.hom ≫ e.hom.hom = z.hom.hom :=
    congrArg (fun f => f.hom.hom) hzEe
  have he : IsClosedSubgroup e := by
    change IsClosedImmersion e.hom.hom.left
    exact MorphismProperty.of_isPullback hpbS ha
  have hclosed : IsClosedSubgroup zE := by
    let : IsClosedImmersion e.hom.hom.left := he
    have : IsClosedImmersion (zE.hom.hom.left ≫ e.hom.hom.left) := by
      rw [← Over.comp_left, hzEe']
      exact hz.isClosedSubgroup
    exact IsClosedImmersion.of_comp _ e.hom.hom.left
  have hcentral : IsCentral zE := by
    intro U x V b y
    rw [← Category.assoc]
    refine hpb.hom_ext ?_ ?_
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hzEp',
        MonObj.comp_one, one_mul, mul_one]
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hzEe']
      exact (commute_of_mem_center (hz.isCentral V (b ≫ x)) (y ≫ e.hom.hom)).eq
  have hpq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zE) p := by
    refine ⟨MorphismProperty.of_isPullback hpbS.flip hq.1,
      MorphismProperty.of_isPullback hpbS.flip hq.2.1,
      MorphismProperty.of_isPullback hpbS.flip hq.2.2.1, ?_⟩
    ext U x
    rw [mem_range_kernelι_iff]
    constructor
    · intro hx
      have hxe : x ≫ e.hom.hom ∈ (SubgroupFunctor.range (kernelι q)).carrier U := by
        rw [mem_range_kernelι_iff, Category.assoc, ← hpb.w, ← Category.assoc, hx,
          MonObj.one_comp]
      rw [hq.2.2.2] at hxe
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxe
      refine SubgroupFunctor.mem_range.mpr ⟨y, hpb.hom_ext ?_ ?_⟩
      · rw [Category.assoc, hzEp', MonObj.comp_one, hx]
      · rw [Category.assoc, hzEe', hy]
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [Category.assoc, hzEp', MonObj.comp_one]
  have hpa : IsAffineHom p.hom.hom.left := by
    have : IsSeparated Q.X.hom := fieldSeparated k Q
    have : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w]
      infer_instance
    have : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp _ Q.X.hom
    exact MorphismProperty.of_isPullback hpbS.flip inferInstance
  have hE : IsTorus E :=
    centralTorusExtensionStatement k E Z zE hz.isTorus hclosed hcentral T p hT hpa hpq
  let Ec : CommGroupScheme (Spec (CommRingCat.of k)) := { E with comm := hE.isCommMonObj }
  have herange : SubgroupFunctor.range e = (SubgroupFunctor.range a).comap q := by
    ext U x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      change x ≫ q.hom.hom ∈ (SubgroupFunctor.range a).carrier U
      exact SubgroupFunctor.mem_range.mpr
        ⟨y ≫ p.hom.hom, by rw [Category.assoc, hpb.w, ← Category.assoc, hy]⟩
    · intro hx
      change x ≫ q.hom.hom ∈ (SubgroupFunctor.range a).carrier U at hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      exact SubgroupFunctor.mem_range.mpr ⟨hpb.lift y x hy, hpb.lift_snd _ _ _⟩
  have hen : (SubgroupFunctor.range e).IsNormal := by
    rw [herange]
    intro U g x _ hx
    change x ≫ q.hom.hom ∈ (SubgroupFunctor.range a).carrier U at hx
    change ((g * x * g⁻¹) ≫ q.hom.hom) ∈ (SubgroupFunctor.range a).carrier U
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← ht, ← (commute_of_mem_center (hac U t) (g ≫ q.hom.hom)).eq,
      mul_inv_cancel_right]
    exact SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩
  have hec : IsCentral e := hE.isCentral_of_isNormal (T := Ec) e he hen
  have hle : SubgroupFunctor.range e ≤ SubgroupFunctor.range z :=
    hz.greatest Ec e hE he hec
  have heq : e ≫ q = 0 := by
    apply (Grp.forget _).map_injective
    apply (mem_range_kernelι_iff q _).mp
    rw [hq.2.2.2]
    exact hle E.X (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
  have hpa0 : p ≫ a = p ≫ 0 := by
    rw [comp_zero, show p ≫ a = e ≫ q from pullback.condition, heq]
  let : Flat p.hom.hom.left := hpq.1
  let : Surjective p.hom.hom.left := hpq.2.1
  let : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi p.hom.hom.left).mp
  exact congrArg (fun f => f.hom.hom.left) hpa0

end Langlands.GroupScheme
