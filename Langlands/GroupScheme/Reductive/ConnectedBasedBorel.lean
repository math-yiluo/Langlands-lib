import Langlands.GroupScheme.RelativeLevi.ConnectedBorelCocharacter
import Langlands.GroupScheme.Reductive.SchemeCoordinateRootDatum
import Langlands.GroupScheme.Reductive.BasedBorelPullback
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning

/-! # Bases of coordinate root data presenting prescribed Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {I J : Type u} [Fintype I] [Fintype J]
    (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced]

omit [Fintype I] in
/-- A regular coordinate coweight selects a base with exactly its positive roots. -/
theorem exists_base_isPos_iff (n : I → ℤ) (hn : ∀ a, P.root' a n ≠ 0) :
    ∃ b : P.Base, ∀ a, b.IsPos a ↔ 0 < P.toLinearMap (P.root a) n := by
  obtain ⟨b, hb⟩ := Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P n hn
  refine ⟨b, ?_⟩
  intro a
  apply RootPairing.Base.isPos_iff_positive_functional P b (P.flip.toLinearMap n)
  intro c hc
  have hmem : c ∈ IsAddIndecomposable.baseOf P.root
      ((P.flip.toLinearMap n) : _ →+ ℤ) := by
    rw [← hb]
    exact hc
  exact hmem.1

/-- Over a field, any Borel through the coordinate maximal torus is the
canonical positive-coroot parabolic of a base of the supplied full datum. -/
theorem exists_base_of_fieldBorel
    (k : Type u) [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (t : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hmax : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : letI := hG.isAffineHom; IsRootDatumOf t (fieldRealization k P))
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ b : P.Base,
      SubgroupFunctor.range i = Dynamic.parabolic (BasedBorelTransport.cocharacter t P b) := by
  classical
  let := hG.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let hir : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let H := regularCocharacterBorel k G hG (splitTorus.commGroupScheme _ I) t
    (isSplitTorus_splitTorus I) hmax
  obtain ⟨ν, hν, hrep⟩ := H.2.2 B i (hir.liftOfLE t hti) hi (hir.liftOfLE_comp t hti)
  let n := splitTorus.cocharacterLatticeEquiv k I ν
  have hνeq : splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n = ν := by
    rw [splitTorus.exponentCocharacter_eq_cocharacterLatticeEquiv_symm]
    exact (splitTorus.cocharacterLatticeEquiv k I).symm_apply_apply ν
  have hpair (m n' : I → ℤ) :
      latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m)
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n') =
      P.toLinearMap m n' := by
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
    exact (pairing_of_isRootDatumOf k P t hP m n').symm
  have hn : ∀ a, P.root' a n ≠ 0 := by
    intro a
    have ha : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a) ∈ roots t :=
      (mem_rootRange_iff k P t hP _).mp ⟨a, rfl⟩
    have h := hν _ ha
    rw [← hνeq, hpair] at h
    exact h
  obtain ⟨b, hb⟩ := exists_base_isPos_iff P n hn
  let ρ := BasedBorelExponent.positiveCorootSum P b
  let νb := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I ρ
  have hνb : IsRegularCocharacter t νb := by
    intro α hα
    rw [← hP.2.1] at hα
    obtain ⟨a, rfl⟩ := hα
    rw [fieldRealization_root]
    change latticePairing _ _ (splitTorus.exponentCocharacter _ I ρ) ≠ 0
    rw [hpair]
    exact BasedBorelExponent.pairing_root_positiveCorootSum_ne_zero P b a
  have hpar :
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) =
        Dynamic.parabolic (CommGroupScheme.groupHom νb ≫ t) := by
    apply (H.2.1 ν νb hν hνb).mpr
    intro α hα
    rw [← hP.2.1] at hα
    obtain ⟨a, rfl⟩ := hα
    rw [fieldRealization_root, ← hνeq]
    change (0 < latticePairing _ _ (splitTorus.exponentCocharacter _ I n) ↔
      0 < latticePairing _ _ (splitTorus.exponentCocharacter _ I ρ))
    rw [hpair, hpair, BasedBorelExponent.pairing_root_positiveCorootSum]
    exact (hb a).symm.trans (by
      rw [RootPairing.Base.isPos_iff]
      omega)
  exact ⟨b, hrep.2.trans hpar⟩

end CoordinateRootDatum

namespace CoordinateRootDatum

variable {I J : Type u} [Fintype I] [Fintype J]
    (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced]

/-- Over a connected base, a base of any full global coordinate datum
presents the supplied Borel through the supplied split maximal torus. -/
theorem exists_base_of_connected
    {S : Scheme.{u}} [ConnectedSpace S] {G B : GroupScheme S}
    (hG : IsReductive G) (t : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : letI := hG.isAffineHom; IsGlobalCoordinateRootDatumOf I G t P)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    ∃ b : P.Base,
      SubgroupFunctor.range i = Dynamic.parabolic (BasedBorelTransport.cocharacter t P b) := by
  classical
  let := hG.smooth
  let := hG.isAffineHom
  let : GeometricallyConnected G.X.hom :=
    DynamicBaseSmoothConnected.geometricallyConnected_of_baseChange
      (fun k _ a => (hG.isConnectedReductive_baseChange a).connectedSpace)
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : GeometricallyConnected B.X.hom :=
    hi.isRelativeParabolicSubgroup.geometricallyConnected hG
  have hic : IsClosedSubgroup i := relativeParabolicClosed S G B i hG hi.isRelativeParabolicSubgroup
  let : IsClosedImmersion i.hom.hom.left := hic
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let s : S := Classical.choice inferInstance
  let a := S.fromSpecResidueField s
  let Gs := (baseChange a).obj G
  let ts := (splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t
  let is := (baseChange a).map i
  have hGs : IsConnectedReductive Gs := hG.isConnectedReductive_residueFiber s
  have hts : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) ts :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange a).obj (splitTorus.commGroupScheme S I))
      (T' := splitTorus.commGroupScheme _ I) (splitTorus.baseChangeIso a I).symm (hmax s)
  have htsis : SubgroupFunctor.range ts ≤ SubgroupFunctor.range is := by
    rw [show SubgroupFunctor.range ts = SubgroupFunctor.range ((baseChange a).map t) from
      SubgroupFunctor.range_iso_comp (splitTorus.baseChangeIso a I).symm _]
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    intro U x hx
    exact hti ((Over.map a).obj U) hx
  obtain ⟨b, hb⟩ := exists_base_of_fieldBorel P (S.residueField s) hGs ts hts
    (hP.2.2 _ a) is (hi.residueFiber s).isBorelSubgroup htsis
  let hir : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let l := hir.liftOfLE t hti
  let χ := CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter S I (BasedBorelExponent.positiveCorootSum P b)) ≫ l
  have hχ : χ ≫ i = BasedBorelTransport.cocharacter t P b := by
    rw [BasedBorelTransport.cocharacter, Category.assoc, hir.liftOfLE_comp]
  refine ⟨b, ?_⟩
  rw [← hχ]
  apply Dynamic.range_eq_parabolic_of_field_presentation i hic χ (S.residueField s) a
  rw [hχ, BasedBorelTransport.cocharacter_baseChange]
  exact hb

/-- A concrete base of the supplied full coordinate datum, with its actual
global Borel presentation. -/
def basedBorelOfConnected
    {S : Scheme.{u}} [ConnectedSpace S] {G B : GroupScheme S}
    (hG : IsReductive G) (t : splitTorus S I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : letI := hG.isAffineHom; IsGlobalCoordinateRootDatumOf I G t P)
    (i : B ⟶ G) (hi : IsRelativeBorelSubgroup i)
    (hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i) :
    {b : P.Base //
      SubgroupFunctor.range i = Dynamic.parabolic (BasedBorelTransport.cocharacter t P b)} :=
  ⟨(exists_base_of_connected P hG t hmax hP i hi hti).choose,
    (exists_base_of_connected P hG t hmax hP i hi hti).choose_spec⟩

end CoordinateRootDatum

end Langlands.GroupScheme
