/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections

import WeilConjectures.AlgebraicGeometry.PicardOrdinaryScalarCoordinates
import WeilConjectures.AlgebraicGeometry.Picard.PicardConnectiveModelComparison

/-! # Scalar cycles as derived test sections

## References

* Stacks Project, Tag 0BF2, the degree-zero cycle calculation
* Stacks Project, Tag 0BF2, degree-zero cycle calculation
* Tags 08C4 and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The scalar-cycle calculation for an arbitrary derived object with a fixed connective
strictly perfect model. No direct image or family of line bundles occurs in this lemma. -/
theorem picard_scalar_derived_cycles
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
    ∃ c : picardDerivedModelSections E (W.fromSpecResidueField w) ≃+ W.residueField w,
      ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U) (a : Γ(W, V)),
        (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
        ∃ ξ : picardDerivedModelSections E V.ι,
          picardDerivedModelRestriction E (picardResidueLift W w V hwV) V.ι
              (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV) ξ =
            c.symm (W.evaluation V w hwV a) := by
  classical
  obtain ⟨q, hq⟩ := picard_connective_model_comparison W E U K hK hneg hE
  obtain ⟨b, hb, hlift⟩ :=
    picard_ordinary_scalar_coordinates W w U hwU hU m d K hK e0 e1 hd hdw
  let p := picardResidueLift W w U hwU
  let qκ := q (W.fromSpecResidueField w) p (picardResidueLift_comp W w U hwU)
  let bκ : picardOrdinaryModelCycles W U K (W.fromSpecResidueField w) p ≃+
      W.residueField w :=
    { toFun := fun x ↦ b x.val
      invFun := fun a ↦ ⟨b.symm a, hb _⟩
      left_inv := fun x ↦ Subtype.ext (b.symm_apply_apply x.val)
      right_inv := fun a ↦ b.apply_symm_apply a
      map_add' := fun x y ↦ b.map_add x.val y.val }
  refine ⟨qκ.trans bκ, ?_⟩
  intro V hwV hVU a ha
  have hVUι : W.homOfLE hVU ≫ U.ι = V.ι := by simp
  have hp : picardResidueLift W w V hwV ≫ W.homOfLE hVU = p := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, hVUι, picardResidueLift_comp, picardResidueLift_comp]
  obtain ⟨x, hx⟩ := hlift V hwV hVU hp a ha
  let qV := q V.ι (W.homOfLE hVU) hVUι
  refine ⟨qV.symm x, ?_⟩
  apply (qκ.trans bκ).injective
  rw [AddEquiv.apply_symm_apply]
  change b (qκ (picardDerivedModelRestriction E (picardResidueLift W w V hwV)
    V.ι (W.fromSpecResidueField w) (picardResidueLift_comp W w V hwV)
      (qV.symm x))).val = _
  rw [hq (picardResidueLift W w V hwV) V.ι (W.fromSpecResidueField w)
    (W.homOfLE hVU) p (picardResidueLift_comp W w V hwV) hp hVUι
    (picardResidueLift_comp W w U hwU)]
  simpa only [qV, AddEquiv.apply_symm_apply] using hx

end AlgebraicGeometry.Scheme
