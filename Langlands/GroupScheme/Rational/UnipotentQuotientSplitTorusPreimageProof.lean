import Langlands.GroupScheme.Rational.UnipotentQuotientSplitTorusPreimageStatement
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.FppfQuotientGeometry
import Langlands.GroupScheme.Rational.UnipotentPointsNilpotent

/-! # Proof: the preimage of a split subtorus under a unipotent quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace UnipotentQuotientSplitTorusPreimage

open RelativeRoot

variable {k : Type u} [Field k] {G U Q : GroupScheme (Spec (CommRingCat.of k))}
  {r : U ⟶ G} {q : G ⟶ Q} {B : CommGroupScheme (Spec (CommRingCat.of k))} {z : B.toGrp ⟶ Q}

/-- The points of the inverse image of a closed subgroup with commutative points, under a
quotient by a unipotent subgroup, form a solvable group on every test scheme. -/
theorem isSolvable_preimage_points [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom]
    (hU : IsUnipotent U) (hq : IsFppfQuotient (SubgroupFunctor.range r) q)
    (hz : IsClosedSubgroup z) (T : Over (Spec (CommRingCat.of k))) :
    Group.IsSolvable (T ⟶ (SubgroupPreimage.groupScheme q z).X) := by
  have : IsClosedImmersion (SubgroupPreimage.inclusion q z).hom.hom.left :=
    SubgroupPreimage.isClosedSubgroup q z hz
  let p := IsMonHom.monoidHom (SubgroupPreimage.projection q z).hom.hom T
  let incl := IsMonHom.monoidHom (SubgroupPreimage.inclusion q z).hom.hom T
  let ρ := IsMonHom.monoidHom r.hom.hom T
  have : Group.IsNilpotent (T ⟶ U.X) := isNilpotent_points_of_isUnipotent hU T
  have : Group.IsSolvable (T ⟶ U.X) := inferInstance
  have : Group.IsSolvable ρ.range := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have : Group.IsSolvable (T ⟶ B.toGrp.X) :=
    Group.isSolvable_of_comm fun a b => mul_comm (G := T ⟶ B.X) a b
  have hmem : ∀ x : p.ker, incl x ∈ ρ.range := by
    intro x
    have hx : (x : T ⟶ _) ≫ (SubgroupPreimage.projection q z).hom.hom = 1 := x.2
    have hk : incl x ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
      rw [mem_range_kernelι_iff]
      change ((x : T ⟶ _) ≫ (SubgroupPreimage.inclusion q z).hom.hom) ≫ q.hom.hom = 1
      rw [Category.assoc, (SubgroupPreimage.isPullback q z).w, ← Category.assoc, hx,
        MonObj.one_comp]
    rw [hq.2.2.2] at hk
    exact hk
  let ψ : p.ker →* ρ.range := (incl.comp p.ker.subtype).codRestrict ρ.range hmem
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact (cancel_mono (SubgroupPreimage.inclusion q z).hom.hom.left).1
      (congrArg CommaMorphism.left h)
  have : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective hψ
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p (by rw [Subgroup.range_subtype])

end UnipotentQuotientSplitTorusPreimage

open UnipotentQuotientSplitTorusPreimage RelativeRoot in
/-- The full inverse image of a split subtorus is the required solvable closed subgroup. -/
theorem unipotentQuotientSplitTorusPreimageStatement :
    UnipotentQuotientSplitTorusPreimageStatement.{u} := by
  intro k _ G _ _ _ U r hr hUs hUc hUu Q q hq B z hz
  have : IsClosedImmersion r.hom.hom.left := hr
  have : IsClosedImmersion z.hom.hom.left := hz.2
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Smooth U.X.hom := hUs
  have : ConnectedSpace U.X.left := hUc
  have : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : IsSeparated Q.X.hom := fieldSeparated k Q
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp q.hom.hom.left Q.X.hom
  have : Mono r.hom.hom := Over.mono_of_mono_left _
  have hrep : (SubgroupFunctor.range r).IsRepresentedBy r := ⟨inferInstance, rfl⟩
  have : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hrep hUs
  have : Smooth B.toGrp.X.hom := hz.1.smooth
  have : ConnectedSpace B.toGrp.X.left := hz.1.connectedSpace
  have : GeometricallyConnected U.X.hom := geometricallyConnected_of_connected U
  have : GeometricallyConnected (kernel q).X.hom := by
    let e := hq.kernelIso hrep
    let : IsIso e.inv.hom.hom := (Grp.forget _).map_isIso e.inv
    let : IsIso e.inv.hom.hom.left := (Over.forget _).map_isIso e.inv.hom.hom
    rw [← Over.w e.inv.hom.hom]
    set_option backward.isDefEq.respectTransparency.types false in
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) e.inv.hom.hom.left U.X.hom).mpr
      inferInstance
  have : IsClosedImmersion (SubgroupPreimage.inclusion q z).hom.hom.left :=
    SubgroupPreimage.isClosedSubgroup q z hz.2
  refine ⟨SubgroupPreimage.groupScheme q z, SubgroupPreimage.inclusion q z,
    SubgroupPreimage.isClosedSubgroup q z hz.2, SubgroupPreimage.smooth q z, ?_,
    SubgroupPreimage.isAffineHom q z hz.2,
    isSolvableGroupScheme_of_isSolvable_points (isSolvable_preimage_points hUu hq hz.2 _), ?_⟩
  · apply FppfQuotientGeometry.connectedSpace_of_isEmbedding
      (SubgroupPreimage.inclusion q z).hom.hom.left.isClosedEmbedding.isEmbedding
    have hrange : Set.range (SubgroupPreimage.inclusion q z).hom.hom.left =
        q.hom.hom.left ⁻¹' Set.range z.hom.hom.left := by
      have := Scheme.image_preimage_eq_of_isPullback
        (SubgroupPreimage.isPullback_scheme q z).flip Set.univ
      simpa only [Set.preimage_univ, Set.image_univ] using this
    rw [hrange]
    exact FppfQuotientGeometry.isConnected_preimage q
      (isConnected_range z.hom.hom.left.continuous)
      z.hom.hom.left.isClosedEmbedding.isClosed_range
  · intro K i g h
    exact ⟨pullback.lift i g h.symm, pullback.lift_fst _ _ _⟩

end Langlands.GroupScheme
