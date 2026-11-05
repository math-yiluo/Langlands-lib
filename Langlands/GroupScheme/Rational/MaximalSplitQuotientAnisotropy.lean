import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Torus.CentralExtensionSplit
import Langlands.GroupScheme.Torus.CocharacterAnisotropy
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers

/-! # Quotients by central maximal split tori have split rank zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

/-- A closed split torus in the quotient by a central maximal split torus is trivial. -/
theorem IsMaximalSplitTorus.split_torus_quotient_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {j : A.toGrp ⟶ G}
    (hj : IsMaximalSplitTorus j) (hjc : IsCentral j)
    {C : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ C)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (a : T.toGrp ⟶ C)
    (hT : IsSplitTorus T.toGrp) (ha : IsClosedSubgroup a) :
    a = 0 := by
  have hjq : j ≫ q = 0 := by
    apply (Grp.forget _).map_injective
    apply (mem_range_kernelι_iff q _).mp
    rw [hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  let E : GroupScheme (Spec (CommRingCat.of k)) := subgroupIntersection a q
  let p : E ⟶ T.toGrp := pullback.fst a q
  let e : E ⟶ G := pullback.snd a q
  have hpb : IsPullback p.hom.hom e.hom.hom a.hom.hom q.hom.hom :=
    IsPullback.map (Grp.forget _) (IsPullback.of_hasPullback a q)
  have hpbS : IsPullback p.hom.hom.left e.hom.hom.left a.hom.hom.left q.hom.hom.left :=
    IsPullback.map (Over.forget _) hpb
  let jE : A.toGrp ⟶ E := pullback.lift 0 j (by rw [zero_comp, hjq])
  have hjEp : jE ≫ p = 0 := pullback.lift_fst _ _ _
  have hjEe : jE ≫ e = j := pullback.lift_snd _ _ _
  have hjEp' : jE.hom.hom ≫ p.hom.hom = 1 :=
    congrArg (fun f => f.hom.hom) hjEp
  have hjEe' : jE.hom.hom ≫ e.hom.hom = j.hom.hom :=
    congrArg (fun f => f.hom.hom) hjEe
  have he : IsClosedSubgroup e := by
    change IsClosedImmersion e.hom.hom.left
    exact MorphismProperty.of_isPullback hpbS ha
  have hclosed : IsClosedSubgroup jE := by
    let : IsClosedImmersion e.hom.hom.left := he
    have : IsClosedImmersion (jE.hom.hom.left ≫ e.hom.hom.left) := by
      rw [← Over.comp_left, hjEe']
      exact hj.1.2
    exact IsClosedImmersion.of_comp _ e.hom.hom.left
  have hcentral : IsCentral jE := by
    intro U x V b y
    rw [← Category.assoc]
    refine hpb.hom_ext ?_ ?_
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hjEp',
        MonObj.comp_one, one_mul, mul_one]
    · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, hjEe']
      exact (commute_of_mem_center (hjc V (b ≫ x)) (y ≫ e.hom.hom)).eq
  have hpq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range jE) p := by
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
      · rw [Category.assoc, hjEp', MonObj.comp_one, hx]
      · rw [Category.assoc, hjEe', hy]
    · intro hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [Category.assoc, hjEp', MonObj.comp_one]
  let : IsClosedImmersion e.hom.hom.left := he
  let : IsAffine E.X.left := isAffine_of_isAffineHom e.hom.hom.left
  obtain ⟨I, hI, ⟨eT⟩⟩ := hT
  obtain ⟨J, hJ, ⟨eA⟩⟩ := hj.1.1
  have hE : IsSplitTorus E :=
    CentralExtensionHopfSpec.isSplitTorus_of_split eA eT jE hclosed hcentral p hpq
  let Ec : CommGroupScheme (Spec (CommRingCat.of k)) := { E with comm := hE.isCommMonObj }
  let : IsIso jE := hj.2 Ec e ⟨hE, he⟩ jE hjEe
  have heq : e ≫ q = 0 := by
    apply (cancel_epi jE).mp
    rw [← Category.assoc, hjEe, hjq, comp_zero]
  have hpa0 : p ≫ a = p ≫ 0 := by
    rw [comp_zero, show p ≫ a = e ≫ q from pullback.condition, heq]
  let : Flat p.hom.hom.left := hpq.1
  let : Surjective p.hom.hom.left := hpq.2.1
  let : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi p.hom.hom.left).mp
  exact congrArg (fun f => f.hom.hom.left) hpa0

/-- An affine group quotient by a central maximal split torus has split rank zero. -/
theorem IsMaximalSplitTorus.isAnisotropic_quotient
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {j : A.toGrp ⟶ G}
    (hj : IsMaximalSplitTorus j) (hjc : IsCentral j)
    {C : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ C)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q) :
    IsAnisotropic C := by
  apply isAnisotropic_iff.mpr
  intro I _ i hi
  have hi0 := hj.split_torus_quotient_eq_zero hjc q hq
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i
    (isSplitTorus_splitTorus I) hi
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  refine ⟨fun a => ?_⟩
  have hs : splitTorus.single (Spec (CommRingCat.of k)) I a = 0 := by
    apply CommGroupScheme.hom_ext_points
    intro U x
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, show i.hom.hom = 1 from congrArg (fun f => f.hom.hom) hi0]
    simp only [MonObj.comp_one]
  have hid : (𝟙 (Gm (Spec (CommRingCat.of k)))) = 0 := by
    have h := congrArg
      (fun f : cocharacterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) =>
        f ≫ splitTorus.proj (Spec (CommRingCat.of k)) I a) hs
    simpa [splitTorus.single_comp_proj] using h
  have h := congrArg (gmEndEquiv k) hid
  simp at h

end Langlands.GroupScheme
