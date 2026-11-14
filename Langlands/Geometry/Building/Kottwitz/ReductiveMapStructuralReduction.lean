import Langlands.Geometry.Building.Kottwitz.ReductiveMapExistenceReduction
import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorStatement
import Langlands.GroupScheme.SimplyConnected.CommutativeDerivedCoverConstruction
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Derived.Functoriality

/-! # Structural inputs to the reductive Kottwitz construction -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- A commutative reductive group has the actual trivial group as its simply
connected derived subgroup. -/
theorem hasSimplyConnectedDerivedGroup_of_commutative
    {k : Type u} [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsConnectedReductive T.toGrp) :
    HasSimplyConnectedDerivedGroup T.toGrp :=
  ⟨Grp.trivial (Over (Spec (CommRingCat.of k))), kernelUnit T.toGrp,
    (commutativeDerivedCoverData T.toGrp hT).property.isDerivedSubgroup,
    isSimplyConnected_trivial⟩

/-- The representative law for fundamental-group maps forces the trivial
group-scheme morphism to induce the zero linear map. -/
theorem fundamentalGroupMap_zero_of_mapStatement
    (hmap : AlgebraicFundamentalGroupMapStatement.{u})
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) :
    fundamentalGroupMap k E H G hH hG 0 = 0 := by
  let a := chosenChoice k H hH
  let b := chosenChoice k G hG
  have hs := (hmap k E H G hH hG a b 0).2.1
  have hf : a.IsTorusFactorization E b 0 0 := by
    unfold Choice.IsTorusFactorization
    simp
    apply GroupScheme.hom_ext_points
    intro U x
    change x ≫ (1 : _ ⟶ _) =
      (x ≫ (CommGroupScheme.groupHom
        (0 : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
          (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)).hom.hom) ≫
        ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion).hom.hom
    have hx := comp_groupHom_zero
      (G := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus)
      (H := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus) x
    exact (MonObj.comp_one x).trans
      (((congrArg
        (fun y => y ≫ ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion).hom.hom)
        hx).trans (MonObj.one_comp _)).symm)
  change a.mapTo E b 0 = 0
  apply LinearMap.ext
  intro x
  obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
  have h := hs.2 b 0 hf ν
  simpa only [Limits.comp_zero, map_zero, LinearMap.zero_apply] using h

/-- The actual inertia map also sends the trivial group-scheme morphism to zero. -/
theorem fundamentalInertiaMap_zero_of_statements
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K] [Normal k E]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) :
    fundamentalInertiaMap k K E G hG H hH 0 = 0 := by
  have hs := ((hmap k K E).1 H G hH hG 0).2.1
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective
    ((fundamentalGroupGalois k H E hH).comp (relativeInertia k K E).subtype) x
  have h := hs y
  rw [fundamentalGroupMap_zero_of_mapStatement hfund, LinearMap.zero_apply, map_zero] at h
  exact h

/-- The central-torus inclusion followed by its z-extension projection is the
trivial morphism on all schemes. -/
theorem zExtension_inclusion_projection
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : ZExtension G) :
    z.i ≫ z.p = 0 := by
  apply Grp.hom_ext
  apply yoneda.map_injective
  ext T t
  change (t ≫ z.i.hom.hom) ≫ z.p.hom.hom = t ≫ (0 : z.Z.toGrp ⟶ G).hom.hom
  change (t ≫ z.i.hom.hom) ≫ z.p.hom.hom = t ≫ 1
  rw [MonObj.comp_one]
  apply (mem_range_kernelι_iff z.p _).mp
  rw [z.isZExtension.quotient.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- Upstairs naturality and the zero-morphism law remove the point-kernel
obstruction to descent. -/
theorem zExtensionKottwitzComposite_kills_kernel
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hnat : ∀ (H J : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hJ : IsConnectedReductive J)
      (hscH : HasSimplyConnectedDerivedGroup H) (hscJ : HasSimplyConnectedDerivedGroup J)
      (f : H ⟶ J),
      SimplyConnectedDerivedKottwitzNaturalAt F k H J hH hJ hscH hscJ f)
    (z : ZExtension G) :
    (zExtensionPointMap F k G z).ker ≤
      (zExtensionKottwitzComposite F k G hG z).ker := by
  apply (zExtensionKottwitzComposite_kernel_iff F k G hG z).mpr
  intro t
  have hZT : IsTorus z.Z.toGrp := by
    obtain ⟨E, hE, aE, _, _, hs, _⟩ := z.isZExtension.induced
    exact ⟨E, hE, aE, hs⟩
  let hZ := hZT.isConnectedReductive_of_fieldSplitting
  let hscZ := hasSimplyConnectedDerivedGroup_of_commutative z.Z hZ
  apply Multiplicative.toAdd.injective
  change fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
      G hG z.H z.isZExtension.source_reductive z.p
        (simplyConnectedDerivedKottwitz F k z.H z.isZExtension.source_reductive
          z.isZExtension.derived_simplyConnected
          (affinePointsTarget z.Z.toGrp z.i (CommAlgCat.of k (UnramifiedClosure F)) t)).toAdd = 0
  rw [hnat z.Z.toGrp z.H hZ z.isZExtension.source_reductive hscZ
    z.isZExtension.derived_simplyConnected z.i]
  have hc := congrArg
    (fun m => m (simplyConnectedDerivedKottwitz F k z.Z.toGrp hZ hscZ t).toAdd)
    ((hmap k (UnramifiedClosure F) (SeparableClosure F)).2.2
      z.Z.toGrp z.H G hZ z.isZExtension.source_reductive hG z.i z.p)
  rw [zExtension_inclusion_projection z,
    fundamentalInertiaMap_zero_of_statements hfund hmap,
    LinearMap.zero_apply] at hc
  exact hc

/-- The fixed-group construction with kernel vanishing derived from naturality. -/
theorem reductiveKottwitzExistenceAt_of_naturality
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hnat : ∀ (H J : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hJ : IsConnectedReductive J)
      (hscH : HasSimplyConnectedDerivedGroup H) (hscJ : HasSimplyConnectedDerivedGroup J)
      (f : H ⟶ J),
      SimplyConnectedDerivedKottwitzNaturalAt F k H J hH hJ hscH hscJ f)
    (hz : Nonempty (ZExtension G))
    (hp : ∀ z : ZExtension G, Function.Surjective (zExtensionPointMap F k G z))
    (ht : ∀ z : ZExtension G, Function.Surjective
      (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
        G hG z.H z.isZExtension.source_reductive z.p))
    (hrefine : ∀ z z' : ZExtension G, ∃ w : ZExtension G,
      ∃ r : w.H ⟶ z.H, ∃ r' : w.H ⟶ z'.H,
        r ≫ z.p = w.p ∧ r' ≫ z'.p = w.p) :
    Nonempty (ZExtension G) ∧
    (∃! κ, IsReductiveKottwitzHom F k G hG κ) ∧
    IsReductiveKottwitzHom F k G hG (reductiveKottwitz F k G hG) ∧
    Function.Surjective (reductiveKottwitz F k G hG) ∧
    (∀ hscG : HasSimplyConnectedDerivedGroup G,
      reductiveKottwitz F k G hG = simplyConnectedDerivedKottwitz F k G hG hscG) ∧
    ∀ z : ZExtension G,
      Function.Surjective (zExtensionPointMap F k G z) ∧
      Function.Surjective
        (fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H z.isZExtension.source_reductive z.p) ∧
      ∀ κ, ZExtensionKottwitzLawAt F k G hG z κ ↔ κ = reductiveKottwitz F k G hG :=
  reductiveKottwitzExistenceAt_of_structural_inputs F k G hG hsc hmap hnat hz hp ht
    (zExtensionKottwitzComposite_kills_kernel F k G hG hfund hmap hnat) hrefine

end Langlands.Geometry.Building.Kottwitz
