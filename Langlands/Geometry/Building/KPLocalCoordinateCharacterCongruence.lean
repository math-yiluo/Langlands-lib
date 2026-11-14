import Langlands.Geometry.Building.KPLocalCoordinateValuationComparison
import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.GroupScheme.GaloisPointTowerBaseChange

/-! # Coordinate characters tested by geometric character congruence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPointComparison

private theorem map_iso_inv_hom {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} (e : G ≅ H)
    (x : rationalPoints G) :
    rationalPoints.map e.inv (rationalPoints.map e.hom x) = x := by
  change (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x
  simp only [Category.assoc, ← Grp.comp_hom_hom,
    Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

private theorem eval_extend_restrict_of_map_eq
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (f : H ⟶ baseChanged k L G) (χ : rationalCharacters G)
    (x : rationalPoints G) (y : rationalPoints H)
    (h : rationalPoints.map f y = rationalExtend k L G x) :
    rationalCharacterEval
        (characterRestrict f (rationalCharacters.baseChange (baseMap k L) χ)) y =
      Units.map (algebraMap k L).toMonoidHom (rationalCharacterEval χ x) := by
  rw [rationalCharacterEval_characterRestrict, h]
  exact rationalCharacterEval_extend k L G χ x

private def characterLiftWithEvaluation
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of L))}
    {P : Type u} (x : P → rationalPoints G) (y : P → rationalPoints H)
    (f : H ⟶ baseChanged k L G) (χ : rationalCharacters G)
    (h : ∀ z, rationalPoints.map f (y z) = rationalExtend k L G (x z)) :
    {ψ : rationalCharacters H // ∀ z, rationalCharacterEval ψ (y z) =
      Units.map (algebraMap k L).toMonoidHom (rationalCharacterEval χ (x z))} :=
  ⟨characterRestrict f (rationalCharacters.baseChange (baseMap k L) χ),
    fun z => eval_extend_restrict_of_map_eq f χ (x z) (y z) (h z)⟩

private theorem unitFiltration_of_comparison
    {E Ω : Type u} [Field E] [Field Ω]
    (v : AddValuation E (WithTop ℝ)) (w : AddValuation Ω (WithTop ℝ))
    (f : E →+* Ω) (hv : ∀ z, v z = w (f z))
    (r : ℝ≥0) (z : Eˣ)
    (hz : Units.map f.toMonoidHom z ∈ LocalField.addValuationUnitFiltration w r) :
    z ∈ LocalField.addValuationUnitFiltration v r := by
  change w (f z) = 0 ∧ ((r : ℝ) : WithTop ℝ) ≤ w (f z - 1) at hz
  change v z = 0 ∧ ((r : ℝ) : WithTop ℝ) ≤ v ((z : E) - 1)
  simpa only [hv, map_sub, map_one] using hz

variable (k E Ω : Type u) [Field k] [Field E] [Field Ω]
  [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Successive extension of a rational point agrees with direct extension. -/
theorem towerBaseChangeIso_rationalExtend (z : rationalPoints G) :
    rationalPoints.map (towerBaseChangeIso k E Ω G).hom
      (rationalExtend E Ω (baseChanged k E G) (rationalExtend k E G z)) =
        rationalExtend k Ω G z := by
  apply (baseChangeCoeffEquiv k Ω G).injective
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_towerBaseChangeIso, coefficientBaseChangeEquiv_left,
    baseChangeCoeffEquiv_left]
  change ((rationalExtend E Ω (baseChanged k E G) (rationalExtend k E G z)).left ≫
      CategoryTheory.Limits.pullback.fst (baseChanged k E G).X.hom (baseMap E Ω)) ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (baseMap k E) = _
  rw [rationalExtend_fst, Category.assoc, rationalExtend_fst,
    ← Category.assoc, baseMap_tower]
  exact (rationalExtend_fst k Ω G z).symm

/-- The inverse tower comparison recovers the successive extension. -/
theorem towerBaseChangeIso_inv_rationalExtend (z : rationalPoints G) :
    rationalPoints.map (towerBaseChangeIso k E Ω G).inv (rationalExtend k Ω G z) =
      rationalExtend E Ω (baseChanged k E G) (rationalExtend k E G z) :=
  (congrArg (rationalPoints.map (towerBaseChangeIso k E Ω G).inv)
    (towerBaseChangeIso_rationalExtend k E Ω G z).symm).trans
      (map_iso_inv_hom (towerBaseChangeIso k E Ω G) _)

/-- A geometric character with its coordinate evaluation certificate. -/
def coordinateCharacterBaseChange
    (χ : rationalCharacters (baseChanged k E G)) :
    {ψ : rationalCharacters (baseChanged k Ω G) // ∀ z : rationalPoints G,
      rationalCharacterEval ψ (rationalExtend k Ω G z) =
        Units.map (algebraMap E Ω).toMonoidHom
          (rationalCharacterEval χ (rationalExtend k E G z))} :=
  characterLiftWithEvaluation (rationalExtend k E G) (rationalExtend k Ω G)
    (towerBaseChangeIso k E Ω G).inv χ (towerBaseChangeIso_inv_rationalExtend k E Ω G)

/-- The geometric character has exactly the embedded coordinate-character value. -/
theorem rationalCharacterEval_coordinateCharacterBaseChange
    (χ : rationalCharacters (baseChanged k E G)) (z : rationalPoints G) :
    rationalCharacterEval (coordinateCharacterBaseChange k E Ω G χ).val
        (rationalExtend k Ω G z) =
      Units.map (algebraMap E Ω).toMonoidHom
        (rationalCharacterEval χ (rationalExtend k E G z)) :=
  (coordinateCharacterBaseChange k E Ω G χ).property z

/-- All-character congruence transfers through an exact valuation comparison. -/
theorem coordinateCharacter_mem_unitFiltration_of_comparison
    (v : AddValuation E (WithTop ℝ)) (w : AddValuation Ω (WithTop ℝ))
    (hv : ∀ z, v z = w (algebraMap E Ω z))
    (r : ℝ≥0) (t : rationalPoints G)
    (ht : ∀ ψ : rationalCharacters (baseChanged k Ω G),
      rationalCharacterEval ψ (rationalExtend k Ω G t) ∈
        LocalField.addValuationUnitFiltration w r)
    (χ : rationalCharacters (baseChanged k E G)) :
    rationalCharacterEval χ (rationalExtend k E G t) ∈
      LocalField.addValuationUnitFiltration v r := by
  apply unitFiltration_of_comparison v w (algebraMap E Ω) hv r
  have hχ := ht (coordinateCharacterBaseChange k E Ω G χ).val
  rwa [rationalCharacterEval_coordinateCharacterBaseChange] at hχ

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type u} [Field E] [Algebra (UnramifiedClosure F) E]
  [FiniteDimensional (UnramifiedClosure F) E] [Algebra.IsSeparable (UnramifiedClosure F) E]
  (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))

/-- A geometric congruence condition controls every coordinate-field character. -/
theorem coordinateCharacter_mem_unitFiltration
    (hH : HenselianLocalRing (MaximalUnramified.valuation F).valuationSubring)
    {r : ℝ≥0} {t : rationalPoints T.toGrp}
    (ht : t ∈ localGeometricCharacterCongruence F T r)
    (χ : rationalCharacters (baseChanged (UnramifiedClosure F) E T.toGrp)) :
    rationalCharacterEval χ (rationalExtend (UnramifiedClosure F) E T.toGrp t) ∈
      LocalField.addValuationUnitFiltration
        (FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F) hH E) r := by
  let f : E →ₐ[UnramifiedClosure F] SeparableClosure F := IsSepClosed.lift
  let : Algebra E (SeparableClosure F) := f.toRingHom.toAlgebra
  let : IsScalarTower (UnramifiedClosure F) E (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  exact coordinateCharacter_mem_unitFiltration_of_comparison
    (UnramifiedClosure F) E (SeparableClosure F) T.toGrp
    (FieldTheory.henselianSeparableAddValuation (MaximalUnramified.valuation F) hH E)
    (LocalField.algebraicExtensionAddValuation F (SeparableClosure F))
    (fun z => MaximalUnramified.henselianSeparableAddValuation_eq_geometric F hH f z)
    r t ((mem_characterCongruence _ _ r _).mp ht) χ

end Langlands.Geometry.Building
