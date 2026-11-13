import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleDiscrepancy
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # The based root action of the coordinate discrepancy -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G} {n : ℕ} {e : d.Vertex ≃ Fin n}

/-- The contravariant full root-datum equivalence of the coordinate pinned presentation. -/
def Presentation.coordinateRootEquiv (p : Presentation d e) :
    RootPairing.Equiv p.stage.toSplitPinning.rootDatum p.coordinatePinning.rootDatum :=
  rootDatumEquivOfTorusCompatibleIso
    p.coordinatePinning.isConnectedReductive p.stage.toSplitPinning.isConnectedReductive
    p.coordinatePinning.isSplitTorus p.stage.toSplitPinning.isSplitTorus
    p.coordinatePinning.isMaximalTorus p.stage.toSplitPinning.isMaximalTorus
    p.coordinate.pinningIso.groupIso p.coordinate.pinningIso.torusIso
    p.coordinate.pinningIso.square p.coordinatePinning.isRootDatum
    p.stage.toSplitPinning.isRootDatum

theorem Presentation.coordinateRootEquiv_weightMap (p : Presentation d e)
    (χ : characterLattice p.stage.toSplitPinning.torus) :
    p.coordinateRootEquiv.weightMap χ = p.coordinate.pinningIso.torusIso.hom ≫ χ :=
  rootDatumEquivOfTorusCompatibleIso_weightMap _ _ _ _ _ _ _ _ _ _ _ χ

theorem Presentation.coordinateRootEquiv_symm_weightEquiv (p : Presentation d e)
    (χ : characterLattice p.coordinatePinning.torus) :
    p.coordinateRootEquiv.weightEquiv.symm χ = p.coordinate.pinningIso.torusIso.inv ≫ χ := by
  apply p.coordinateRootEquiv.weightEquiv.injective
  change p.coordinateRootEquiv.weightEquiv
      (p.coordinateRootEquiv.weightEquiv.symm χ) =
    p.coordinateRootEquiv.weightMap (p.coordinate.pinningIso.torusIso.inv ≫ χ)
  rw [LinearEquiv.apply_symm_apply, p.coordinateRootEquiv_weightMap]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The full equivalence has precisely the inverse index map of the pinned isomorphism. -/
theorem Presentation.coordinateRootEquiv_indexEquiv (p : Presentation d e)
    (a : p.stage.rootIndex) :
    p.coordinateRootEquiv.indexEquiv a = p.coordinate.pinningIso.indexEquiv.symm a := by
  obtain ⟨b, rfl⟩ := p.coordinate.pinningIso.indexEquiv.surjective a
  rw [Equiv.symm_apply_apply]
  apply p.coordinatePinning.rootDatum.root.injective
  rw [← RootPairing.Hom.root_weightMap_apply, p.coordinateRootEquiv_weightMap]
  have h := congrArg (fun χ => p.coordinate.pinningIso.torusIso.hom ≫ χ)
    (p.coordinate.pinningIso.root_eq b)
  simpa only [Presentation.coordinatePinning, characterLattice.congr_apply,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h.symm

/-- The contravariant full equivalence preserves the chosen simple bases. -/
theorem Presentation.coordinateRootEquiv_base_iff (p : Presentation d e)
    (a : p.stage.rootIndex) :
    a ∈ p.stage.toSplitPinning.base.support ↔
      p.coordinateRootEquiv.indexEquiv a ∈ p.coordinatePinning.base.support := by
  rw [p.coordinateRootEquiv_indexEquiv]
  simpa only [Presentation.coordinatePinning, Equiv.apply_symm_apply] using
    (p.coordinate.pinningIso.simple_iff (p.coordinate.pinningIso.indexEquiv.symm a)).symm

/-- The full root action induced by the actual coordinate discrepancy. -/
def Presentation.discrepancyRootAut (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    p.coordinatePinning.rootDatum.Aut :=
  rootDatumEquivOfTorusCompatibleIso
    p.coordinatePinning.isConnectedReductive p.coordinatePinning.isConnectedReductive
    p.coordinatePinning.isSplitTorus p.coordinatePinning.isSplitTorus
    p.coordinatePinning.isMaximalTorus p.coordinatePinning.isMaximalTorus
    (p.discrepancyIso σ) (p.discrepancyTorusIso σ) (p.discrepancy_square σ)
    p.coordinatePinning.isRootDatum p.coordinatePinning.isRootDatum

/-- Its canonical based representative modulo the full integral Weyl group. -/
def Presentation.discrepancyBasedAction (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    p.coordinatePinning.basedRootDatumAut :=
  p.coordinatePinning.basedRootDatumProjection (p.discrepancyRootAut σ)

/-- The full discrepancy action is the transported ordinary action of the inverse
Galois element. -/
theorem Presentation.discrepancyRootAut_eq_conjAut (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) :
    p.discrepancyRootAut σ =
      StarActionIndependence.conjAut p.coordinateRootEquiv (p.stage.galoisAction σ⁻¹) := by
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro χ
  rw [StarActionIndependence.conjAut_weightMap,
    p.coordinateRootEquiv_symm_weightEquiv]
  change (p.discrepancyRootAut σ).weightMap χ =
    p.coordinateRootEquiv.weightMap
      ((p.stage.galoisAction σ⁻¹).weightMap (p.coordinate.pinningIso.torusIso.inv ≫ χ))
  rw [p.coordinateRootEquiv_weightMap, StarActionIndependence.galoisAction_weightMap_apply]
  exact (rootDatumEquivOfTorusCompatibleIso_weightMap _ _ _ _ _ _ _ _ _ _ _ χ).trans
    (p.discrepancyTorusIso_character σ χ)

/-- Taking based representatives intertwines the inverse stage star action and
the coordinate discrepancy action. -/
theorem Presentation.discrepancyBasedAction_intertwine (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) :
    p.coordinateRootEquiv.comp (p.stage.starAction σ⁻¹).val =
      (p.discrepancyBasedAction σ).val.comp p.coordinateRootEquiv := by
  apply StarActionIndependence.comp_basedRootDatumProjection
    p.stage.toSplitPinning p.coordinatePinning p.coordinateRootEquiv
    p.coordinateRootEquiv_base_iff (p.stage.galoisAction σ⁻¹) (p.discrepancyRootAut σ)
  rw [p.discrepancyRootAut_eq_conjAut, mul_inv_cancel]
  exact one_mem _

/-- On coordinate simple roots the discrepancy is the inverse stage star action. -/
theorem Presentation.discrepancyBasedAction_index (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (a : p.coordinatePinning.base.support) :
    p.coordinate.pinningIso.indexEquiv ((p.discrepancyBasedAction σ).val.indexEquiv a.val) =
      (p.stage.starAction σ⁻¹).val.indexEquiv (p.coordinate.pinningIso.indexEquiv a.val) := by
  have h := congrArg
    (fun f => f.indexEquiv (p.coordinate.pinningIso.indexEquiv a.val))
    (p.discrepancyBasedAction_intertwine σ)
  change p.coordinateRootEquiv.indexEquiv
      ((p.stage.starAction σ⁻¹).val.indexEquiv (p.coordinate.pinningIso.indexEquiv a.val)) =
    (p.discrepancyBasedAction σ).val.indexEquiv
      (p.coordinateRootEquiv.indexEquiv (p.coordinate.pinningIso.indexEquiv a.val)) at h
  simp only [p.coordinateRootEquiv_indexEquiv, Equiv.symm_apply_apply] at h
  exact p.coordinate.pinningIso.indexEquiv.eq_symm_apply.mp h.symm

/-- Fixedness of all coordinate simple roots is fixedness for the inverse stage action. -/
theorem Presentation.discrepancyBasedAction_fixes_iff_stage_inverse (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) :
    (∀ a : p.coordinatePinning.base.support,
      (p.discrepancyBasedAction σ).val.indexEquiv a.val = a.val) ↔
    (∀ a : p.stage.base.support, (p.stage.starAction σ⁻¹).val.indexEquiv a.val = a.val) := by
  constructor
  · intro h a
    let b : p.coordinatePinning.base.support :=
      ⟨p.coordinate.pinningIso.indexEquiv.symm a.val,
        (p.coordinate.pinningIso.simple_iff _).mpr (by
          simpa only [Equiv.apply_symm_apply, GaloisPinningData.toSplitPinning]
            using a.property)⟩
    have hb := p.discrepancyBasedAction_index σ b
    rw [h b] at hb
    simpa only [b, Equiv.apply_symm_apply] using hb.symm
  · intro h a
    apply p.coordinate.pinningIso.indexEquiv.injective
    rw [p.discrepancyBasedAction_index]
    exact h ⟨p.coordinate.pinningIso.indexEquiv a.val,
      (p.coordinate.pinningIso.simple_iff _).mp a.property⟩

/-- An action element and its inverse fix precisely the same simple vertices. -/
theorem Presentation.stage_inverse_fixes_iff (p : Presentation d e) (σ : p.L ≃ₐ[K] p.L) :
    (∀ a : p.stage.base.support, (p.stage.starAction σ⁻¹).val.indexEquiv a.val = a.val) ↔
    (∀ a : p.stage.base.support, (p.stage.starAction σ).val.indexEquiv a.val = a.val) := by
  constructor
  · intro h a
    have ha := h a
    rw [map_inv] at ha
    change (p.stage.starAction σ).val.indexEquiv.symm a.val = a.val at ha
    exact ((p.stage.starAction σ).val.indexEquiv.symm_apply_eq.mp ha).symm
  · intro h a
    rw [map_inv]
    change (p.stage.starAction σ).val.indexEquiv.symm a.val = a.val
    exact (p.stage.starAction σ).val.indexEquiv.symm_apply_eq.mpr (h a).symm

/-- The retained stage-to-absolute comparison identifies fixedness of every simple vertex. -/
theorem Presentation.stage_fixes_iff_star (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hστ : ∀ y, τ (p.embedding y) = p.embedding (σ y)) :
    (∀ a : p.stage.base.support, (p.stage.starAction σ).val.indexEquiv a.val = a.val) ↔
    (∀ v, d.star τ v = v) := by
  let q := p.rootEquiv.indexEquiv.subtypeEquiv p.base_iff
  constructor
  · intro h v
    obtain ⟨a, rfl⟩ := q.surjective v
    apply Subtype.ext
    have ha := p.star_vertex σ τ hστ a
    rw [h a] at ha
    exact ha.symm
  · intro h a
    apply p.rootEquiv.indexEquiv.injective
    rw [p.star_vertex σ τ hστ a, h]

/-- The discrepancy has trivial based vertex action exactly when the supplied
absolute star action fixes every vertex. -/
theorem Presentation.discrepancyBasedAction_fixes_iff_star (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hστ : ∀ y, τ (p.embedding y) = p.embedding (σ y)) :
    (∀ a : p.coordinatePinning.base.support,
      (p.discrepancyBasedAction σ).val.indexEquiv a.val = a.val) ↔
    (∀ v, d.star τ v = v) :=
  (p.discrepancyBasedAction_fixes_iff_stage_inverse σ).trans
    ((p.stage_inverse_fixes_iff σ).trans (p.stage_fixes_iff_star σ τ hστ))

/-- Movement of some coordinate simple root is exactly movement of some original
Tits vertex by the supplied absolute star action. -/
theorem Presentation.discrepancyBasedAction_moves_iff_star (p : Presentation d e)
    (σ : p.L ≃ₐ[K] p.L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (hστ : ∀ y, τ (p.embedding y) = p.embedding (σ y)) :
    (∃ a : p.coordinatePinning.base.support,
      (p.discrepancyBasedAction σ).val.indexEquiv a.val ≠ a.val) ↔
    (∃ v, d.star τ v ≠ v) := by
  classical
  simpa only [not_forall] using
    not_congr (p.discrepancyBasedAction_fixes_iff_star σ τ hστ)

end Langlands.GroupScheme.SpecialLinearTitsCocycle
