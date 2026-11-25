/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationPrescribedClass

/-! # Transport of equal additive Čech augmentation classes
Source: Stacks Project, Tag 01FD, Lemma 20.15.1. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A matched pair of coefficient cycles transports a supplied augmentation
class equality. This concerns resolution cycles, with no normalized edge equivalence.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, the augmented resolution pentagon;
Tag 03P2 identifies coefficient sections on the small étale sites.
(blueprint: lem-pbc-etale-additive-cech-augmentation-transfer)

Proof: Resolve the exact inverse image of X.etaleAdditiveSheaf. Lift the adjunction
unit to the direct image of this resolution, preserving the degree-zero
augmentation, and lift the adjoint of etaleAdditiveSheafToLowerStar to the given
resolution J of Y.etaleAdditiveSheaf. Their composite on global sections is a
chain map T from the global section complex of I to that of J. The canonical
transfer theorem identifies the first lift on homology with cohomologyMap(g);
the global_cocycle formulas and naturality of extMk identify the coefficient
lift with Sheaf.H.map of the adjoint. Thus s' := cyclesMap(T)(s) has the stated
cohomology class. On each tuple of opens, use the adjunction unit followed by
the target restrictions along hinter to define the refined section transfer.
Naturality makes it commute with cofaces and with resolution differentials.
The augmentation equation identifies its coefficient face with structural
pullback followed by restriction, so hcoords gives exactly the beta image of
z'. The alpha face is global-section transfer. Equivalently use the auxiliary
direct-image resolution and invert its quasi-isomorphisms as in the pentagon
of 01FD. The supplied source equality consequently gives equality of the target
alpha and beta classes. Both augmentation images are cycles since their
augmentations are chain maps; choose tα' and tβ' with the displayed inclusions.
No inverse image of an injective is assumed injective: it is resolved separately,
and its resolution comparisons are augmentation-preserving. No flatness,
affineness, acyclicity on opens or covering hypothesis is needed to transport
an already supplied equality. Degree zero is the same restriction square;
empty schemes, intersections and index sets give zero maps and groups. -/
theorem etaleAdditiveCech_augmentation_transfer
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (cX : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (cY : Etale.ResolutionSectionCanonicalComparison Y.etaleAdditiveSheaf J)
    (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
    (z' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).cycles n)
    (hcoords : ∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    ((cechOver X.toSpecΓ U
                      (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))))
    (s : (additiveCechGlobal I).cycles n)
    (tα tβ : (additiveCechTotal U I).cycles n)
    (hα : (additiveCechTotal U I).iCycles n tα =
      additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s))
    (hβ : (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
      ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))
    (heq : (additiveCechTotal U I).homologyπ n tα =
      (additiveCechTotal U I).homologyπ n tβ) :
    ∃ (s' : (additiveCechGlobal J).cycles n)
      (tα' tβ' : (additiveCechTotal V J).cycles n),
      (additiveCechTotal V J).iCycles n tα' =
        additiveCechAlpha V J n ((additiveCechGlobal J).iCycles n s') ∧
      (additiveCechTotal V J).iCycles n tβ' = additiveCechBeta V J n
        ((cechOver Y.toSpecΓ V
          (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') ∧
      (additiveCechTotal V J).homologyπ n tα' =
        (additiveCechTotal V J).homologyπ n tβ' ∧
      cY.globalEquiv n ((additiveCechGlobal J).homologyπ n s') =
        Sheaf.H.map
          (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
            (Scheme.etaleAdditiveSheafToLowerStar g)) n
          (Etale.cohomologyMap g X.etaleAdditiveSheaf n
            (cX.globalEquiv n ((additiveCechGlobal I).homologyπ n s))) := by
  let x := Sheaf.H.map
    (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
      (Scheme.etaleAdditiveSheafToLowerStar g)) n
    (Etale.cohomologyMap g X.etaleAdditiveSheaf n
      (cX.globalEquiv n ((additiveCechGlobal I).homologyπ n s)))
  obtain ⟨s', hs'⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((additiveCechGlobal J).homologyπ n)).mp
      inferInstance ((cY.globalEquiv n).symm x)
  have hclass : cY.globalEquiv n ((additiveCechGlobal J).homologyπ n s') = x := by
    rw [hs']
    exact (cY.globalEquiv n).apply_symm_apply x
  obtain ⟨tα', tβ', hα', hβ', heq'⟩ :=
    etaleAdditiveCech_augmentation_prescribed_class g U V hinter I J cX cY n z z'
      hcoords s tα tβ hα hβ heq s' hclass
  exact ⟨s', tα', tβ', hα', hβ', heq', hclass⟩

end AlgebraicGeometry.Scheme.Modules
