/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechScalarChainAction
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechGlobalMapNaturality

/-! # Scalar transport of augmentation representatives

Source: Stacks Project, Tags 03P2 and 01FD. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Multiplication transports a common augmentation representative to another one.
Source: Stacks Project, Tag 01EQ, functoriality in coefficients, and Tag 01FD,
the commuting augmented double-complex diagram used in Tag 03P2.
(blueprint: new-w2-additive-cech-scalar-transport)

Proof: Lift μ(r) to an endomorphism of I preserving its augmentation, by the
injective-resolution comparison theorem. Apply its global section cochain map
to s and its induced total-complex map to tα and tβ. On coefficient cochains
use multiplication by r in the module complex cechOver. The section formula hμ
and naturality of restrictFunctorΓ imply that beta commutes with these maps:
the pullback of r on the intersection is its restriction as a structural
section, and GammaSpecIso.inv_hom_id identifies the base scalar with r.
Alpha commutes by naturality of restrictions. These chain maps preserve cycles
and equality of homology classes, giving s', z', tα', tβ' and the first three
equations. The canonical comparison's extMk formula and functoriality of Ext
identify the class of s' with H(μ(r)) of the class of s. Finally the homology
projection in ModuleCat is linear, so the class of z' is r times [z]. This
argument does not assume a normalized edge or the affine-cover hypotheses.
For r=0 and r=1 the same chain-map identities apply; in degree zero there
are no boundaries, and empty intersections give zero coordinates. -/
theorem additiveCech_scalar_transport
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (μ : Γ(X, ⊤) → (X.etaleAdditiveSheaf ⟶ X.etaleAdditiveSheaf))
    (hμ : ∀ r (W : X.Etaleᵒᵖ) (x : X.etaleAdditiveSheaf.obj.obj W),
      (μ r).hom.app W x =
        ULift.up ((show Γ(W.unop.left, ⊤) from x.down) *
          (show Γ(W.unop.left, ⊤) from W.unop.hom.appTop r)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (c : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (n : ℕ) (r : Γ(X, ⊤))
    (s : (additiveCechGlobal I).cycles n)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
    (tα tβ : (additiveCechTotal U I).cycles n)
    (hα : (additiveCechTotal U I).iCycles n tα =
      additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s))
    (hβ : (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
      ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z))
    (ht : (additiveCechTotal U I).homologyπ n tα =
      (additiveCechTotal U I).homologyπ n tβ) :
    ∃ (s' : (additiveCechGlobal I).cycles n)
      (z' : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
      (tα' tβ' : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tα' =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s') ∧
      (additiveCechTotal U I).iCycles n tβ' = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z') ∧
      (additiveCechTotal U I).homologyπ n tα' =
        (additiveCechTotal U I).homologyπ n tβ' ∧
      c.globalEquiv n ((additiveCechGlobal I).homologyπ n s') =
        Sheaf.H.map (μ r) n (c.globalEquiv n ((additiveCechGlobal I).homologyπ n s)) ∧
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z' =
        r • (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z
    := by
  let G := additiveCechGlobalMap I (μ r)
  let F := additiveCechTotalMap U I (μ r)
  have hA := fun x ↦ ConcreteCategory.congr_hom
    (additiveCech_alpha_natural X U I (μ r) n) x
  change ∀ x : (additiveCechGlobal I).X n,
    F.f n (additiveCechAlpha U I n x) = additiveCechAlpha U I n (G.f n x) at hA
  have hB := additiveCech_scalar_chain_action X U μ hμ I n r
  let s' := HomologicalComplex.cyclesMap G n s
  let z' := r • z
  let tα' := HomologicalComplex.cyclesMap F n tα
  let tβ' := HomologicalComplex.cyclesMap F n tβ
  refine ⟨s', z', tα', tβ', ?_, ?_, ?_, ?_, ?_⟩
  · have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i F n) tα
    change (additiveCechTotal U I).iCycles n tα' =
      F.f n ((additiveCechTotal U I).iCycles n tα) at hi
    rw [hi, hα, hA]
    have hg := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i G n) s
    change (additiveCechGlobal I).iCycles n s' =
      G.f n ((additiveCechGlobal I).iCycles n s) at hg
    exact congrArg (additiveCechAlpha U I n) hg.symm
  · have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i F n) tβ
    change (additiveCechTotal U I).iCycles n tβ' =
      F.f n ((additiveCechTotal U I).iCycles n tβ) at hi
    rw [hi, hβ, hB]
    congr 1
    exact ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n).hom.map_smul
      r z |>.symm
  · have ha := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality F n) tα
    have hb := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality F n) tβ
    change HomologicalComplex.homologyMap F n ((additiveCechTotal U I).homologyπ n tα) =
      (additiveCechTotal U I).homologyπ n tα' at ha
    change HomologicalComplex.homologyMap F n ((additiveCechTotal U I).homologyπ n tβ) =
      (additiveCechTotal U I).homologyπ n tβ' at hb
    rw [← ha, ← hb, ht]
  · exact additiveCech_global_map_naturality X I c (μ r) n s
  · exact ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n).hom.map_smul
      r z

end AlgebraicGeometry.Scheme.Modules
