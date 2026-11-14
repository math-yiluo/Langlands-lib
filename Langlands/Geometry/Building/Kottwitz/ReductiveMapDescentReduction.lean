import Langlands.Geometry.Building.Kottwitz.ReductiveMapDescentReductionStatement

/-! # Formal reduction of reductive Kottwitz descent -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

section EquivarianceTransfer

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (k : Type u) [Field k]
  [Algebra k (UnramifiedClosure F)] [Algebra k (SeparableClosure F)]
  [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
  [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
  (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)

/-- The two residual-equivariant factors of the cocenter target comparison
give residual equivariance of their composite. -/
theorem cocenterTargetMap_equivariant
    (hI : FundamentalInertiaMapStatement.{u})
    (hT : TorusInertiaComparisonStatement.{u})
    (c : Cocenter k G) (σ : UnramifiedClosure F ≃ₐ[k] UnramifiedClosure F)
    (a : ReductiveTarget F k G hG) :
    cocenterTargetMap F k G hG c
        (fundamentalGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F)
          G hG σ a) =
      torusGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F) c.torus σ
        (cocenterTargetMap F k G hG c a) := by
  unfold cocenterTargetMap
  simp only [LinearMap.comp_apply]
  rw [((hI k (UnramifiedClosure F) (SeparableClosure F)).1 G c.torus.toGrp hG
    c.isTorus.isConnectedReductive_of_fieldSplitting c.quotient).2.2 σ a]
  exact (hT k (UnramifiedClosure F) (SeparableClosure F) c.torus c.isTorus).2.2.2 σ _

/-- The cocenter square transfers torus equivariance to a group with simply
connected derived group through its injective target comparison. -/
theorem simplyConnectedDerivedKottwitz_equivariant_of_inputs
    (hscInput : SimplyConnectedDerivedKottwitzStatement.{u})
    (hI : FundamentalInertiaMapStatement.{u})
    (hT : TorusInertiaComparisonStatement.{u})
    (hTor : GeneralTorusKottwitzEquivarianceStatement.{u})
    (hsc : HasSimplyConnectedDerivedGroup G)
    (σ : UnramifiedClosure F ≃ₐ[k] UnramifiedClosure F)
    (x : reductiveKPoints F k G) :
    (simplyConnectedDerivedKottwitz F k G hG hsc
      (GaloisPoint.conjugate k (UnramifiedClosure F) G σ x)).toAdd =
    fundamentalGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F) G hG σ
      (simplyConnectedDerivedKottwitz F k G hG hsc x).toAdd := by
  classical
  let c := Classical.choice (nonempty_cocenter k G hG)
  have hs := hscInput F k G hG hsc
  apply (hs.2.2.2 c).1.1
  rw [hs.2.1 c, cocenterTargetMap_equivariant F k G hG hI hT c, hs.2.1 c]
  have hn := DFunLike.congr_fun
    (G.affinePointsTarget_naturality c.quotient
      (CommAlgCat.ofHom σ.toAlgHom)) x
  change GaloisPoint.conjugate k (UnramifiedClosure F) c.torus.toGrp σ
      (G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F)) x) =
    G.affinePointsTarget c.quotient (CommAlgCat.of k (UnramifiedClosure F))
      (GaloisPoint.conjugate k (UnramifiedClosure F) G σ x) at hn
  rw [← hn]
  exact hTor F k c.torus c.isTorus σ _

/-- Surjectivity on points in a z-extension transfers residual equivariance
from its simply-connected-derived source to the reductive map. -/
theorem reductiveKottwitz_equivariant_of_inputs
    (hscInput : SimplyConnectedDerivedKottwitzStatement.{u})
    (hredInput : ReductiveKottwitzExistenceStatement.{u})
    (hI : FundamentalInertiaMapStatement.{u})
    (hT : TorusInertiaComparisonStatement.{u})
    (hTor : GeneralTorusKottwitzEquivarianceStatement.{u})
    (σ : UnramifiedClosure F ≃ₐ[k] UnramifiedClosure F)
    (x : reductiveKPoints F k G) :
    (reductiveKottwitz F k G hG
      (GaloisPoint.conjugate k (UnramifiedClosure F) G σ x)).toAdd =
    fundamentalGammaRepresentation k (UnramifiedClosure F) (SeparableClosure F) G hG σ
      (reductiveKottwitz F k G hG x).toAdd := by
  classical
  have hr := hredInput F k G hG
  let z := Classical.choice hr.1
  obtain ⟨y, rfl⟩ := (hr.2.2.2.2.2 z).1 x
  have hz := hr.2.2.1.2 z
  have hn := DFunLike.congr_fun
    (z.H.affinePointsTarget_naturality z.p
      (CommAlgCat.ofHom σ.toAlgHom)) y
  change GaloisPoint.conjugate k (UnramifiedClosure F) G σ
      (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F)) y) =
    z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F))
      (GaloisPoint.conjugate k (UnramifiedClosure F) z.H σ y) at hn
  rw [hn, hz, hz]
  rw [simplyConnectedDerivedKottwitz_equivariant_of_inputs F k z.H
    z.isZExtension.source_reductive hscInput hI hT hTor
    z.isZExtension.derived_simplyConnected]
  exact ((hI k (UnramifiedClosure F) (SeparableClosure F)).1 z.H G
    z.isZExtension.source_reductive hG z.p).2.2 σ _

end EquivarianceTransfer

section RationalRestriction

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- Residual equivariance gives the unique invariant-valued restriction and its
selected-map specification. -/
theorem reductiveKottwitzRestriction_of_equivariant
    (hκ : ReductiveKottwitzEquivariant F G hG) :
    (∃! κ, IsReductiveKottwitzRestriction F G hG κ) ∧
    IsReductiveKottwitzRestriction F G hG (reductiveKottwitzRational F G hG) := by
  let κK : rationalPoints G →* Multiplicative (ReductiveTarget F F G hG) :=
    (reductiveKottwitz F F G hG).comp
      ((GaloisPoint.extend F (UnramifiedClosure F) G).comp
        (rationalCoeffEquiv F G).toMonoidHom)
  have hfixed (x : rationalPoints G) :
      (κK x).toAdd ∈ ReductiveInvariantTarget F G hG := by
    intro σ
    simpa only [κK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      GaloisPoint.conjugate_extend] using
      (hκ σ (GaloisPoint.extend F (UnramifiedClosure F) G
        (rationalCoeffEquiv F G x))).symm
  let κ : rationalPoints G →* Multiplicative (ReductiveInvariantTarget F G hG) :=
    { toFun := fun x => Multiplicative.ofAdd ⟨(κK x).toAdd, hfixed x⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd κK.map_one
      map_mul' := fun x y => by
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (κK.map_mul x y) }
  have hspec : IsReductiveKottwitzRestriction F G hG κ := fun _ => rfl
  refine ⟨⟨κ, hspec, ?_⟩, ?_⟩
  · intro ψ hψ
    ext x
    exact congrArg Multiplicative.toAdd ((hψ x).trans (hspec x).symm)
  · exact Classical.epsilon_spec ⟨κ, hspec⟩

end RationalRestriction

/-- The unique invariant-valued rational restriction follows from residual
equivariance at the full published local-field scope. -/
theorem reductiveKottwitzRationalRestriction :
    ReductiveKottwitzRationalRestrictionStatement.{u} := by
  intro F _ _ _ _ G hG hκ
  exact reductiveKottwitzRestriction_of_equivariant F G hG hκ

/-- The cocenter and z-extension transfers, followed by restriction to rational
points, prove the five-input reduction without changing the descent target. -/
theorem reductiveKottwitzDescent_of_inputs :
    ReductiveKottwitzDescentReductionStatement.{u} := by
  intro hsc hred hI hT hTor
  constructor
  · intro F _ _ _ _ k _ _ _ _ _ _ G hG σ x
    exact reductiveKottwitz_equivariant_of_inputs F k G hG hsc hred hI hT hTor σ x
  · intro F _ _ _ _ G hG
    have hκ : ReductiveKottwitzEquivariant F G hG :=
      reductiveKottwitz_equivariant_of_inputs F F G hG hsc hred hI hT hTor
    exact ⟨hκ, reductiveKottwitzRestriction_of_equivariant F G hG hκ⟩

end Langlands.Geometry.Building.Kottwitz
