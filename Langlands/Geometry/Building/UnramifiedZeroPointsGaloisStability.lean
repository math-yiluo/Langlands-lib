import Langlands.Geometry.Building.UnramifiedZeroGaloisStability
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.GroupScheme.SimplyConnected.BaseIsoTransport
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly

/-! # Galois stability of the unramified zero subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

/-- Pullback along a field-spectrum isomorphism and an ambient isomorphism
transports a supplied simply connected derived cover. -/
theorem baseChange_comp_iso_isSimplyConnectedDerivedCover
    {k K : Type u} [Field k] [Field K]
    {G D C : GroupScheme (Spec (CommRingCat.of k))}
    {G' : GroupScheme (Spec (CommRingCat.of K))}
    {d : D ⟶ G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π)
    (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso a]
    (e : (GroupScheme.baseChange a).obj G ≅ G') :
    IsSimplyConnectedDerivedCover
      ((GroupScheme.baseChange a).map d ≫ e.hom)
      ((GroupScheme.baseChange a).map π) := by
  let : IsAffineHom G.X.hom := h.isConnectedReductive.isAffineHom
  exact ⟨(h.isConnectedReductive.baseChange_of_isIso a).of_iso e.symm,
    (h.isDerivedSubgroup.baseChange_of_eq a
      (derivedSubgroup_baseChange_eq_of_field a G)).comp_iso e,
    h.isSimplyConnectedCover.baseChange_of_isIso a⟩

/-- Coefficient conjugation transports the rational-point image of a supplied
homomorphism to that of its conjugate homomorphism. -/
theorem rationalConjugate_mem_conjugate_range
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ baseChanged k K G) (σ : K ≃ₐ[k] K)
    {x : rationalPoints (baseChanged k K G)}
    (hx : x ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))) :
    rationalConjugate k K G σ x ∈
      (SubgroupFunctor.range
        ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i ≫
          (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
            (galoisBaseMap_over k K σ) G).hom)).carrier (Over.mk (𝟙 _)) := by
  have hx' := (rationalConjugate_mem_galoisTransport_iff k K G σ
    (SubgroupFunctor.range i) x).mpr hx
  change rationalConjugate k K G σ x ∈
    (SubgroupFunctor.descentTransport (algebraBaseMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G (SubgroupFunctor.range i)).carrier
        (Over.mk (𝟙 _)) at hx'
  rwa [SubgroupFunctor.descentTransport_range] at hx'

/-- The rational-point image of a transported derived-cover composite is the
simply connected image of the target group, computed with any supplied cover. -/
theorem baseChange_comp_range_eq_simplyConnectedImage
    {k K : Type u} [Field k] [Field K]
    {G D C : GroupScheme (Spec (CommRingCat.of k))}
    {G' D' C' : GroupScheme (Spec (CommRingCat.of K))}
    {d : D ⟶ G} {π : C ⟶ D} {d' : D' ⟶ G'} {π' : C' ⟶ D'}
    (h : IsSimplyConnectedDerivedCover d π)
    (h' : IsSimplyConnectedDerivedCover d' π')
    (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso a]
    (e : (GroupScheme.baseChange a).obj G ≅ G') :
    (SubgroupFunctor.range ((GroupScheme.baseChange a).map (π ≫ d) ≫ e.hom)).carrier
        (Over.mk (𝟙 _)) = simplyConnectedImage d' π' := by
  rw [Functor.map_comp, Category.assoc]
  exact simplyConnectedImage_eq (baseChange_comp_iso_isSimplyConnectedDerivedCover h a e) h'

/-- Coefficient conjugation preserves the simply connected image of a group
defined over the original field, for every choice of derived cover upstairs. -/
theorem rationalConjugate_mem_simplyConnectedImage
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    {D C : GroupScheme (Spec (CommRingCat.of K))}
    {d : D ⟶ baseChanged k K G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) (σ : K ≃ₐ[k] K)
    {x : rationalPoints (baseChanged k K G)} (hx : x ∈ simplyConnectedImage d π) :
    rationalConjugate k K G σ x ∈ simplyConnectedImage d π := by
  let a := galoisBaseMap k K σ
  let : IsIso a := isIso_SpecMap_iff.mpr σ.bijective
  have hx' := rationalConjugate_mem_conjugate_range k K G (π ≫ d) σ hx
  rwa [baseChange_comp_range_eq_simplyConnectedImage h h a
    (descentBaseChangeIso (algebraBaseMap k K) a (galoisBaseMap_over k K σ) G)] at hx'

/-- Coefficient conjugation preserves the zero subgroup for every supplied
upstairs datum. This is clause 2 of `UnramifiedZeroDescentStatement`. -/
theorem UnramifiedZeroDatum.rationalConjugate_mem_zeroPoints
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)
    {x : rationalPoints (baseChanged F (UnramifiedClosure F) G)}
    (hx : x ∈ E.zeroPoints) :
    rationalConjugate F (UnramifiedClosure F) G σ x ∈ E.zeroPoints := by
  have hle : E.zeroPoints ≤
      E.zeroPoints.comap (rationalConjugate F (UnramifiedClosure F) G σ).toMonoidHom := by
    apply sup_le
    · intro y hy
      exact E.simplyConnectedImage_le_zeroPoints
        (rationalConjugate_mem_simplyConnectedImage F (UnramifiedClosure F) G
          E.isSimplyConnectedDerivedCover σ hy)
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
      exact E.rationalConjugate_torusIwahori_mem_zeroPoints F G σ ht
  exact hle hx

/-- Galois stability of every supplied unramified zero subgroup. -/
def UnramifiedZeroPointsGaloisStabilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F)
    (x : rationalPoints (baseChanged F (UnramifiedClosure F) G)),
      x ∈ E.zeroPoints → rationalConjugate F (UnramifiedClosure F) G σ x ∈ E.zeroPoints

end Langlands.Geometry.Building
