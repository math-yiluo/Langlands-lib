import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedNaturalityReduction
import Langlands.Geometry.Building.Kottwitz.TorusFundamentalComparisonProof
import Langlands.GroupScheme.Derived.CommutativeTriviality
import Langlands.GroupScheme.SimplyConnected.CommutativeDerivedCoverConstruction
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Reducing reductive Kottwitz functoriality to its named inputs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

namespace Cocenter

variable {k : Type u} [Field k]

/-- The identity of an actual torus is an fppf quotient by its derived subgroup. -/
theorem isFppfQuotient_id_of_isTorus (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) :
    RelativeRoot.IsFppfQuotient (derivedSubgroup T.toGrp) (𝟙 T.toGrp) := by
  have : IsAffineHom T.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  have : IsSeparated T.toGrp.X.hom := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (𝟙 T.X.left)
    infer_instance
  · change Surjective (𝟙 T.X.left)
    infer_instance
  · change LocallyOfFinitePresentation (𝟙 T.X.left)
    infer_instance
  · rw [derivedSubgroup_eq_bot_of_isCommMonObj T.toGrp]
    apply SubgroupFunctor.ext
    intro U
    ext x
    rw [mem_range_kernelι_iff]
    simp only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    change x ≫ 𝟙 _ = 1 ↔ x = 1
    rw [Category.comp_id]

/-- An actual torus is its own cocenter, with the identity quotient. -/
def ofTorus (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp) :
    Cocenter k T.toGrp where
  torus := T
  quotient := 𝟙 T.toGrp
  isTorus := hT
  isQuotient := isFppfQuotient_id_of_isTorus T hT

end Cocenter

section NaturalAt

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [Normal k (UnramifiedClosure F)]

/-- The reductive Kottwitz square for one actual morphism of connected reductive groups. -/
def ReductiveKottwitzNaturalAt (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G) : Prop :=
  ∀ x : reductiveKPoints F k H,
    (reductiveKottwitz F k G hG
      (H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
    fundamentalInertiaMap k (UnramifiedClosure F) (SeparableClosure F) G hG H hH f
      (reductiveKottwitz F k H hH x).toAdd

end NaturalAt

section Fixed

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]

/-- On a torus, the reductive map followed by the inertia comparison is the torus map. -/
theorem reductiveKottwitz_torus_of_inputs
    (hmap : FundamentalInertiaMapStatement.{u})
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hexist : ReductiveKottwitzExistenceStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (x : reductiveKPoints F k T.toGrp) :
    torusInertiaComparison k (UnramifiedClosure F) (SeparableClosure F) T hT
        (reductiveKottwitz F k T.toGrp hT.isConnectedReductive_of_fieldSplitting x).toAdd =
      (torusKottwitz F k T hT x).toAdd := by
  have hred := hT.isConnectedReductive_of_fieldSplitting
  have hscT : HasSimplyConnectedDerivedGroup T.toGrp :=
    ⟨Grp.trivial (Over (Spec (CommRingCat.of k))), kernelUnit T.toGrp,
      (commutativeDerivedCoverData T.toGrp hred).property.isDerivedSubgroup,
      isSimplyConnected_trivial⟩
  rw [(hexist F k T.toGrp hred).2.2.2.2.1 hscT]
  have hlaw := (hsc F k T.toGrp hred hscT).2.1 (Cocenter.ofTorus T hT) x
  dsimp only [cocenterTargetMap, Cocenter.ofTorus, LinearMap.comp_apply] at hlaw
  rw [(hmap k (UnramifiedClosure F) (SeparableClosure F)).2.1 T.toGrp hred,
    LinearMap.id_apply] at hlaw
  have hx : affinePointsTarget T.toGrp (𝟙 T.toGrp) (CommAlgCat.of k (UnramifiedClosure F)) x =
      x := by
    rw [affinePointsTarget_apply]
    exact Category.comp_id x
  rw [hx] at hlaw
  exact hlaw

/-- Torus naturality, z-extension domination and the existence statements imply the
reductive Kottwitz square for every actual morphism of connected reductive groups. -/
theorem reductiveKottwitzNaturalAt_of_inputs
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hexist : ReductiveKottwitzExistenceStatement.{u})
    (hdom : ∀ (G H : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → IsConnectedReductive H →
      ∀ (z : ZExtension G) (t : ZExtension H) (f : G ⟶ H),
        ∃ (w : ZExtension G) (r : w.H ⟶ z.H) (s : w.H ⟶ t.H),
          r ≫ z.p = w.p ∧ s ≫ t.p = w.p ≫ f)
    (htnat : ∀ (S T : CommGroupScheme (Spec (CommRingCat.of k)))
      (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T) (x : torusKPoints F k S),
      (torusKottwitz F k T hT
        (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
        torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
          (torusKottwitz F k S hS x).toAdd)
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G) :
    ReductiveKottwitzNaturalAt F k H G hH hG f := by
  intro x
  obtain ⟨t⟩ := (hexist F k G hG).1
  obtain ⟨z⟩ := (hexist F k H hH).1
  obtain ⟨w, -, s, -, hs⟩ := hdom H G hH hG z t f
  obtain ⟨y, rfl⟩ := ((hexist F k H hH).2.2.2.2.2 w).1 x
  have hwH := w.isZExtension.source_reductive
  have htH := t.isZExtension.source_reductive
  obtain ⟨cw⟩ := nonempty_cocenter k w.H hwH
  obtain ⟨ct⟩ := nonempty_cocenter k t.H htH
  have hpt :
      H.affinePointsTarget f (CommAlgCat.of k (UnramifiedClosure F))
          (w.H.affinePointsTarget w.p (CommAlgCat.of k (UnramifiedClosure F)) y) =
        t.H.affinePointsTarget t.p (CommAlgCat.of k (UnramifiedClosure F))
          (w.H.affinePointsTarget s (CommAlgCat.of k (UnramifiedClosure F)) y) := by
    change (y ≫ w.p.hom.hom) ≫ f.hom.hom = (y ≫ s.hom.hom) ≫ t.p.hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hs]
  rw [hpt, (hexist F k G hG).2.2.1.2 t, (hexist F k H hH).2.2.1.2 w,
    simplyConnectedDerivedKottwitz_natural_of_torus_naturality hcmp hfund
      torusFundamentalComparison_proof hmap hinertia F k w.H t.H hwH htH cw ct s hsc
      w.isZExtension.derived_simplyConnected t.isZExtension.derived_simplyConnected
      (htnat cw.torus ct.torus cw.isTorus ct.isTorus (cw.map ct hwH s))]
  have hcomp := (hmap k (UnramifiedClosure F) (SeparableClosure F)).2.2
  have h1 := LinearMap.congr_fun (hcomp w.H t.H G hwH htH hG s t.p)
    (simplyConnectedDerivedKottwitz F k w.H hwH w.isZExtension.derived_simplyConnected y).toAdd
  have h2 := LinearMap.congr_fun (hcomp w.H H G hwH hH hG w.p f)
    (simplyConnectedDerivedKottwitz F k w.H hwH w.isZExtension.derived_simplyConnected y).toAdd
  rw [LinearMap.comp_apply] at h1 h2
  rw [h1, h2, hs]

end Fixed

/-- KP Lemma 11.5.1 functoriality and torus compatibility, from the named existence,
fundamental-group and torus statements, z-extension domination and torus naturality. -/
theorem reductiveKottwitzFunctoriality_of_inputs
    (hcmp : AlgebraicFundamentalGroupComparisonStatement.{u})
    (hfund : AlgebraicFundamentalGroupMapStatement.{u})
    (hmap : FundamentalInertiaMapStatement.{u})
    (hinertia : TorusInertiaComparisonStatement.{u})
    (hsc : SimplyConnectedDerivedKottwitzStatement.{u})
    (hexist : ReductiveKottwitzExistenceStatement.{u})
    (hdom : ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
      IsConnectedReductive G → IsConnectedReductive H →
      ∀ (z : ZExtension G) (t : ZExtension H) (f : G ⟶ H),
        ∃ (w : ZExtension G) (r : w.H ⟶ z.H) (s : w.H ⟶ t.H),
          r ≫ z.p = w.p ∧ s ≫ t.p = w.p ≫ f)
    (htnat : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
      [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
      [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
      (S T : CommGroupScheme (Spec (CommRingCat.of k)))
      (hS : IsTorus S.toGrp) (hT : IsTorus T.toGrp) (f : S ⟶ T) (x : torusKPoints F k S),
      (torusKottwitz F k T hT
        (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
          (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
        torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
          (torusKottwitz F k S hS x).toAdd) :
    ReductiveKottwitzFunctorialityStatement.{u} := by
  intro F _ _ _ _ k _ _ _ _ _ _
  exact ⟨fun H G hH hG f =>
      reductiveKottwitzNaturalAt_of_inputs F k hcmp hfund hmap hinertia hsc hexist
        (hdom k) (htnat F k) H G hH hG f,
    fun T hT x => reductiveKottwitz_torus_of_inputs F k hmap hsc hexist T hT x⟩

end Langlands.Geometry.Building.Kottwitz
