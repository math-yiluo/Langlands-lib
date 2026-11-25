/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaMap
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechPullbackChainTransfer

/-! # Čech augmentation compatibility for a prescribed target class
Source: Stacks Project, Tag 01FD, Lemma 20.15.1.
(blueprint: lem-pbc-etale-additive-cech-augmentation-prescribed-class) -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A target global cycle of the prescribed pullback class has matching total augmentations.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, the augmented double-complex
construction; Tag 01FB, resolution comparison; Tag 03P2, coefficient sections.
(blueprint: lem-pbc-etale-additive-cech-augmentation-prescribed-class)

Proof: Apply the exact inverse image to I. Its augmented complex is still exact,
although its terms need not be injective. Extend the adjoint coefficient morphism
into J degree by degree using injectivity of the terms of J: first extend across
the degree-zero augmentation, then factor through each differential's image and
extend across its inclusion into the next term. Adjunction gives a complex map
from I into the direct image of J preserving the coefficient augmentation.
Evaluate this map at the terminal object and restrict to the terminal pullback
to obtain the global section map T. On each tuple intersection, evaluate the same
map and restrict along hinter. Naturality with respect to deleting entries of a
tuple gives the horizontal complex equation; the resolution-map equation gives
the vertical one. Hence these components define a map of the double complexes
and of their totals, R. For alpha, the restriction square gives
R(alpha(s)) = alpha(T(s)). For beta, the degree-zero augmentation equation and
the identification of coefficient sections in Tag 03P2 give exactly structural
pullback followed by restriction. The coordinate hypothesis therefore gives
R(beta(z)) = beta(z'). Applying homologyMap(R) to heq equates the target alpha
class of T(s) and the target beta class. The canonical global-cocycle comparison,
resolutionSection_canonical_transfer for inverse image, and naturality of extMk
for the adjoint coefficient morphism identify the class of T(s) with the right
side of hclass. Thus hclass and injectivity of cY.globalEquiv show that s' and
T(s) differ by a global boundary. Alpha is a complex map (its horizontal
component is zero by the alternating restriction identity), so their alpha
images differ by a total boundary. Beta also takes cycles to cycles: its
horizontal differential is the coefficient Cech differential, and its vertical
differential vanishes by the resolution augmentation equation. Take the unique
cycle lifts of alpha(s') and beta(z') through iCycles; the preceding boundary
calculation gives equality of their total homology classes. No augmentation is
inverted, and no cover or acyclicity on opens is needed. For degree zero the
boundary argument is equality of cycles. Empty index sets give zero total
complexes; empty schemes and empty intersections likewise introduce no extra
hypothesis. -/
theorem etaleAdditiveCech_augmentation_prescribed_class
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
      (additiveCechTotal U I).homologyπ n tβ)
    (s' : (additiveCechGlobal J).cycles n)
    (hclass : cY.globalEquiv n ((additiveCechGlobal J).homologyπ n s') =
        Sheaf.H.map
          (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
            (Scheme.etaleAdditiveSheafToLowerStar g)) n
          (Etale.cohomologyMap g X.etaleAdditiveSheaf n
            (cX.globalEquiv n ((additiveCechGlobal I).homologyπ n s)))) :
    ∃ (tα' tβ' : (additiveCechTotal V J).cycles n),
      (additiveCechTotal V J).iCycles n tα' =
        additiveCechAlpha V J n ((additiveCechGlobal J).iCycles n s') ∧
      (additiveCechTotal V J).iCycles n tβ' = additiveCechBeta V J n
        ((cechOver Y.toSpecΓ V
          (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') ∧
      (additiveCechTotal V J).homologyπ n tα' =
        (additiveCechTotal V J).homologyπ n tβ' := by
  obtain ⟨f, t, hf, htβ, hc⟩ :=
    exists_additiveCech_pullback_chain_transfer g U V hinter I J cX cY n
  obtain ⟨a, ha⟩ := exists_additiveCech_alpha_map V J
  let fs := HomologicalComplex.cyclesMap f n s
  let ta := HomologicalComplex.cyclesMap t n tα
  let tb := HomologicalComplex.cyclesMap t n tβ
  let as' := HomologicalComplex.cyclesMap a n s'
  have hiα : (additiveCechTotal V J).iCycles n ta =
      additiveCechAlpha V J n ((additiveCechGlobal J).iCycles n fs) := by
    change (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal V J).iCycles n) tα = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hα]
    rw [← ConcreteCategory.comp_apply, hf, ConcreteCategory.comp_apply]
    congr 1
    change _ = (HomologicalComplex.cyclesMap f n ≫ (additiveCechGlobal J).iCycles n) s
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
  have hiβ : (additiveCechTotal V J).iCycles n tb = additiveCechBeta V J n
      ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') := by
    change (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal V J).iCycles n) tβ = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hβ]
    exact htβ _ _ hcoords
  have ht : (additiveCechTotal V J).homologyπ n ta =
      (additiveCechTotal V J).homologyπ n tb := by
    change (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal V J).homologyπ n) tα =
      (HomologicalComplex.cyclesMap t n ≫ (additiveCechTotal V J).homologyπ n) tβ
    rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  have hs : (additiveCechGlobal J).homologyπ n s' =
      (additiveCechGlobal J).homologyπ n fs := by
    apply (cY.globalEquiv n).injective
    change _ = cY.globalEquiv n
      ((HomologicalComplex.cyclesMap f n ≫ (additiveCechGlobal J).homologyπ n) s)
    rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply, hc]
    exact hclass
  have hia : (additiveCechTotal V J).iCycles n as' =
      additiveCechAlpha V J n ((additiveCechGlobal J).iCycles n s') := by
    change (HomologicalComplex.cyclesMap a n ≫ (additiveCechTotal V J).iCycles n) s' = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, ha]
  have hta : HomologicalComplex.cyclesMap a n fs = ta := by
    apply (AddCommGrpCat.mono_iff_injective ((additiveCechTotal V J).iCycles n)).mp
      inferInstance
    change (HomologicalComplex.cyclesMap a n ≫ (additiveCechTotal V J).iCycles n) fs = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, ha, hiα]
  refine ⟨as', tb, hia, hiβ, ?_⟩
  change (HomologicalComplex.cyclesMap a n ≫ (additiveCechTotal V J).homologyπ n) s' = _
  rw [← HomologicalComplex.homologyπ_naturality, ConcreteCategory.comp_apply, hs]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hta, ht]

end AlgebraicGeometry.Scheme.Modules
