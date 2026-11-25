/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackAugmentedTransfer
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCanonicalCoefficientTransfer

/-! # Pullback maps of the augmented additive Čech complexes
Source: Stacks Project, Tags 01FD, 01FB and 03P2.
(blueprint: lem-pbc-etale-additive-cech-pullback-chain-transfer) -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback and refinement give augmentation-preserving global and total cochain maps.
Source: Stacks Project, Tag 01FD, proof of Lemma 20.15.1 (double-complex maps),
Tag 01FB, resolution comparison, and Tag 03P2, structural-function coordinates.
(blueprint: lem-pbc-etale-additive-cech-pullback-chain-transfer)

Proof: Obtain α:I -> g_*J, its coefficient augmentation equation, and its total
map t from exists_additiveCech_pullback_augmented_transfer. Take f to be the explicit
globalResolutionSectionTransfer of α. Its terminal restrictions and the tuplewise
restriction components of t give the alpha square and the beta equation supplied
by that theorem. Apply resolutionSection_canonical_coefficient_transfer to α and
the structural coefficient morphism. The canonical comparisons identify the
homology map of f with inverse-image pullback followed by the adjoint coefficient
map. This proves the final formula for every global class. No global cycle is
chosen with a prescribed class, and no equality of total classes is assumed.
Empty families give zero total maps; degree zero,
empty intersections and empty schemes need no extra assumptions. -/
theorem exists_additiveCech_pullback_chain_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (cI : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (cJ : Etale.ResolutionSectionCanonicalComparison Y.etaleAdditiveSheaf J)
    (n : ℕ) :
    ∃ f : additiveCechGlobal I ⟶ additiveCechGlobal J,
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal V J,
      (additiveCechAlpha U I n ≫ t.f n = f.f n ≫ additiveCechAlpha V J n) ∧
      (∀ (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n)
        (x' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).X n),
        (∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                x' =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    x))) → t.f n (additiveCechBeta U I n x) = additiveCechBeta V J n x') ∧
      (∀ x, cJ.globalEquiv n (HomologicalComplex.homologyMap f n x) =
        Sheaf.H.map
          (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
            (Scheme.etaleAdditiveSheafToLowerStar g)) n
          (Etale.cohomologyMap g X.etaleAdditiveSheaf n (cI.globalEquiv n x))) := by
  obtain ⟨α, hα, t, htα, htβ⟩ :=
    exists_additiveCech_pullback_augmented_transfer g U V hinter I J n
  refine ⟨Etale.globalResolutionSectionTransfer g I.cocomplex J.cocomplex α,
    t, htα, htβ, ?_⟩
  intro x
  exact Etale.resolutionSection_canonical_coefficient_transfer g X.etaleAdditiveSheaf
    I Y.etaleAdditiveSheaf J (Scheme.etaleAdditiveSheafToLowerStar g) α hα cI cJ n x

end AlgebraicGeometry.Scheme.Modules
