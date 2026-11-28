import Langlands.GroupScheme.Rational.QuadraticRealCover
import Langlands.GroupScheme.Rational.QuadraticRegularCochain
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.Global.InfinitePlaceGroupManifold
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldWeilRestrictionTopology

/-! # Toral centralizers and coboundaries at inert real places -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField Topology
open CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology Langlands.Global.AdelicFunctoriality
open scoped NumberField.LiesOver InfiniteExtension CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1400
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 30000

private theorem HasToralCentralizer.comp_iso {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} {z : rationalPoints G}
    (hz : HasToralCentralizer z) (e : G ≅ H) : HasToralCentralizer (z ≫ e.hom.hom.hom) := by
  obtain ⟨T, j, hj, hc⟩ := hz
  refine ⟨T, j ≫ e.hom, hj.comp_iso e, ?_⟩
  ext Z x
  rw [MaximalTorusParameterExistence.mem_range_comp_iso_iff, hc, mem_pointCentralizer,
    mem_pointCentralizer, ← Category.assoc (toUnit _) z]
  let y := toUnit Z ≫ z
  have hy : (y ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = y := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  constructor
  · intro h
    apply (cancel_mono e.inv.hom.hom).mp
    change (x * (y ≫ e.hom.hom.hom)) ≫ e.inv.hom.hom =
      ((y ≫ e.hom.hom.hom) * x) ≫ e.inv.hom.hom
    simpa only [MonObj.mul_comp, hy] using h
  · intro h
    have hh := congrArg (fun t : Z ⟶ H.X => t ≫ e.inv.hom.hom) h
    change (x * (y ≫ e.hom.hom.hom)) ≫ e.inv.hom.hom =
      ((y ≫ e.hom.hom.hom) * x) ≫ e.inv.hom.hom at hh
    simpa only [MonObj.mul_comp, hy] using hh

private theorem baseChangeSectionHom_eq {S S' : Scheme.{u}} (b : S' ⟶ S)
    (G : GroupScheme S) (z : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom b G z = (baseChangeBasePointsEquiv b G).symm (toUnit (Over.mk b) ≫ z) := by
  let r : Over.mk b ⟶ Over.mk (𝟙 S) := Over.homMk b (by simp)
  change (baseChangeBasePointsEquiv b G).symm (r ≫ z) = _
  rw [toUnit_unique r (toUnit _)]

private theorem toralCentralizer_of_iso_points {k : Type u} [Field k]
    {G₁ G₂ H : GroupScheme (Spec (CommRingCat.of k))} (e₁ : G₁ ≅ H) (e₂ : G₂ ≅ H)
    (x₁ : rationalPoints G₁) (x₂ : rationalPoints G₂)
    (he : rationalPoints.map e₁.hom x₁ = rationalPoints.map e₂.hom x₂)
    (h : HasToralCentralizer x₁) : HasToralCentralizer x₂ := by
  have h' := h.comp_iso (e₁ ≪≫ e₂.symm)
  change x₁ ≫ e₁.hom.hom.hom = x₂ ≫ e₂.hom.hom.hom at he
  change HasToralCentralizer (x₁ ≫ (e₁.hom ≫ e₂.inv).hom.hom) at h'
  rw [Grp.comp_hom_hom, ← Category.assoc, he, Category.assoc, ← Grp.comp_hom_hom,
    Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] at h'
  exact h'

private theorem toralCentralizer_of_geometricPoint {k E : Type u} [Field k] [Field E] [Algebra k E]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated H.X.hom]
    (z : rationalPoints H) (h : HasToralCentralizer (geometricRationalPointHom (K := E) H z)) :
    HasToralCentralizer z := by
  change HasToralCentralizer (baseChangeSectionHom (algebraBaseMap k E) H z) at h
  rw [baseChangeSectionHom_eq] at h
  obtain ⟨T, j, hj, hc⟩ := h
  exact exists_maximalTorus_pointCentralizer_of_extension z j hj hc

section Towers

open GaloisPointComparison

variable {F K M : Type u} [Field F] [Field K] [Field M] [Algebra F K]
  [Algebra F M] [Algebra K M] [IsScalarTower F K M]
  (G : GroupScheme (Spec (CommRingCat.of F)))

private theorem tower_point (y : (baseChanged F K G).affinePoints (CommAlgCat.of K M)) :
    rationalPoints.map (towerBaseChangeIso F K M G).hom
        ((baseChangeCoeffEquiv K M (baseChanged F K G)).symm y) =
      (baseChangeCoeffEquiv F M G).symm (coefficientBaseChangeEquiv F K M G y) := by
  apply (baseChangeCoeffEquiv F M G).injective
  rw [baseChangeCoeffEquiv_towerBaseChangeIso, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem extend_tower_coeff (y : G.affinePoints (CommAlgCat.of F K)) :
    let H := baseChanged F K G
    let z := (baseChangeCoeffEquiv F K G).symm y
    coefficientBaseChangeEquiv F K M G (baseChangeCoeffEquiv K M H
      (geometricRationalPointHom (K := M) H z)) =
      ringTestMap F (IsScalarTower.toAlgHom F K M) ≫ y := by
  let H := baseChanged F K G
  let e := baseChangeCoeffEquiv F K G
  let z := e.symm y
  have hz : z.left ≫ pullback.fst G.X.hom (baseMap F K) = y.left :=
    (baseChangeCoeffEquiv_left F K G z).symm.trans (congrArg Over.Hom.left (e.apply_symm_apply y))
  apply Over.OverMorphism.ext
  rw [coefficientBaseChangeEquiv_left, baseChangeCoeffEquiv_left]
  change ((baseChangeSectionHom (baseMap K M) H z).left ≫ pullback.fst H.X.hom (baseMap K M)) ≫
    pullback.fst G.X.hom (baseMap F K) = _
  rw [baseChangeSectionHom_fst, Category.assoc, hz]
  rfl

private theorem extension_tower_point (y : G.affinePoints (CommAlgCat.of F K)) :
    rationalPoints.map (towerBaseChangeIso F K M G).hom
        (geometricRationalPointHom (K := M) (baseChanged F K G) ((baseChangeCoeffEquiv F K G).symm y)) =
      (baseChangeCoeffEquiv F M G).symm (ringTestMap F (IsScalarTower.toAlgHom F K M) ≫ y) := by
  apply (baseChangeCoeffEquiv F M G).injective
  rw [baseChangeCoeffEquiv_towerBaseChangeIso, MulEquiv.apply_symm_apply]
  exact extend_tower_coeff G y

private theorem tower_point_eq {L : Type u} [Field L] [Algebra F L] [Algebra L M]
    [IsScalarTower F L M] (s : (baseChanged F K G).affinePoints (CommAlgCat.of K M))
    (t : G.affinePoints (CommAlgCat.of F L))
    (hval : coefficientBaseChangeEquiv F K M G s = ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ t) :
    rationalPoints.map (towerBaseChangeIso F K M G).hom
        ((baseChangeCoeffEquiv K M (baseChanged F K G)).symm s) =
      rationalPoints.map (towerBaseChangeIso F L M G).hom
        (geometricRationalPointHom (K := M) (baseChanged F L G) ((baseChangeCoeffEquiv F L G).symm t)) :=
  (tower_point G s).trans ((congrArg (baseChangeCoeffEquiv F M G).symm hval).trans
    (extension_tower_point G t).symm)

private theorem toralCentralizer_of_tower {L : Type u} [Field L] [Algebra F L] [Algebra L M]
    [IsScalarTower F L M] [IsSeparated (baseChanged F L G).X.hom]
    (s : (baseChanged F K G).affinePoints (CommAlgCat.of K M))
    (t : G.affinePoints (CommAlgCat.of F L))
    (hval : coefficientBaseChangeEquiv F K M G s = ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ t)
    (h : HasToralCentralizer ((baseChangeCoeffEquiv K M (baseChanged F K G)).symm s)) :
    HasToralCentralizer ((baseChangeCoeffEquiv F L G).symm t) := by
  apply toralCentralizer_of_geometricPoint (E := M)
  exact toralCentralizer_of_iso_points (towerBaseChangeIso F K M G) (towerBaseChangeIso F L M G) _ _
    (tower_point_eq G s t hval) h

end Towers

section Inert

attribute [local instance] upperCompletion_isScalarTower

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  {w : InfinitePlace F} (v : InfinitePlacesAbove L w)
  (hdeg : Module.finrank F L = 2) (hw : w.IsReal) (hv : v.1.IsComplex)
  (σ : L ≃ₐ[F] L) (hσ : σ ≠ 1)
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "K" => w.Completion
local notation "M" => (upperCompletion v)
local notation "G₁" => (Functor.obj (baseChange (algebraBaseMap F K)) G)
local notation "G₂" => (Functor.obj (baseChange (algebraBaseMap F L)) G)
local notation "τ" => (inertConjugation v hdeg hw hv σ)

/-- The local strongly regular centralizer descends to the coefficient field
of the original cocycle. -/
theorem toralCentralizer_of_inertRestriction (ξ : Cocycle G (ringTest F L))
    (h : HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap K M) G₁).symm
        (GaloisCocycle.value (inertRestriction v ξ) τ))) :
    HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm
      (GaloisCocycle.value ξ σ)) := by
  let : IsSeparated (G₂).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd G.X.hom (algebraBaseMap F L)))
  exact toralCentralizer_of_tower G _ _ (inertRestriction_value v ξ hdeg hw hv σ) h

omit [IsAffineHom G.X.hom] in
/-- Over an inert completion the restriction of a twist has the ordinary
local twisted value for the scalar-extended cochain. -/
theorem inertRestriction_twist_value (ξ : Cocycle G (ringTest F L))
    (f : G.affinePoints (CommAlgCat.of F L)) :
    let f₁ := affinePointsBaseChangeMulEquiv F K M G
      (ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ f)
    GaloisCocycle.value (inertRestriction v (ξ.twist f)) τ =
      GaloisCocycle.value ((inertRestriction v ξ).twist f₁) τ := by
  let r := ringTestMap F (IsScalarTower.toAlgHom F L M)
  let e := affinePointsBaseChangeMulEquiv F K M G
  let f₁ := e (r ≫ f)
  have hr : r ≫ ringTestMap F σ.toAlgHom =
      ringTestMap F ((τ).toAlgHom.restrictScalars F) ≫ r := by
    rw [← ringTestMap_comp, ← ringTestMap_comp]
    congr 1
    exact AlgHom.ext (fun x => (inertConjugation_algebraMap v hdeg hw hv σ x).symm)
  have hn : GaloisPoint.conjugate K M G₁ τ f₁ = e (r ≫ GaloisPoint.conjugate F L G σ f) := by
    rw [show GaloisPoint.conjugate K M G₁ τ f₁ =
      (G₁).affinePointMap (CommAlgCat.ofHom (τ).toAlgHom) f₁ from rfl,
      affinePointsBaseChangeMulEquiv_naturality]
    congr 1
    change ringTestMap F ((τ).toAlgHom.restrictScalars F) ≫ r ≫ f =
      r ≫ ringTestMap F σ.toAlgHom ≫ f
    rw [← Category.assoc, ← Category.assoc, hr]
  change _ = GaloisCocycle.value ((inertRestriction v ξ).twist f₁) τ
  apply e.symm.injective
  rw [inertRestriction_value, value_twist, value_twist, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply, inertRestriction_value, hn, MulEquiv.symm_apply_apply]
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  rfl

/-- The inert local value has a square root inverted by the coefficient automorphism. -/
def HasInertSquare (ξ : Cocycle G (ringTest F L)) : Prop :=
  ∃ s : (G₁).affinePoints (CommAlgCat.of K M),
    s * s = GaloisCocycle.value (inertRestriction v ξ) τ ∧
      GaloisPoint.conjugate K M G₁ τ s = s⁻¹

include hσ in
/-- A nonempty open at the upper complex completion gives strongly regular
quadratic values with norm-one square roots over that completion. -/
theorem exists_inert_cochainOpen (hG : IsConnectedReductive G) (ξ : Cocycle G (ringTest F L))
    (hξ : (ξ.baseChangePullback (algebraBaseMap F K)).IsTrivial) :
    letI : IsAffine (G₂).X.left := isAffine_of_isAffineHom (G₂).X.hom
    ∃ U : Set (RingPoint L (G₂).X M), IsOpen U ∧ U.Nonempty ∧
      ∀ f : G.affinePoints (CommAlgCat.of F L),
        RingPoint.changeRing (Algebra.ofId L M) (affinePointsBaseChangeMulEquiv F L L G f) ∈ U →
        HasToralCentralizer ((baseChangeBasePointsEquiv (algebraBaseMap F L) G).symm
          (GaloisCocycle.value (ξ.twist f) σ)) ∧
        HasInertSquare v hdeg hw hv σ (ξ.twist f) := by
  let : NontriviallyNormedField K := infiniteCompletionNontriviallyNormedField w
  let : RCLike M := Langlands.Global.InfinitePlaceGroupPoints.completionRCLike L v.1
  let : IsModuleTopology K M := isModuleTopologyOfFiniteDimensional
  let : IsGalois K M := inert_isGalois v hw hv
  have hτ := inertConjugation_ne v hdeg hw hv σ hσ
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 :=
    (IsGalois.card_aut_eq_finrank K M).trans (completion_finrank_of_complex v hw hv)
  have hτ₂ : τ * τ = 1 := by simpa only [hcard, pow_two] using (pow_card_eq_one' (x := τ))
  let hG₁ := connectedReductiveFieldExtensionStatement F K G hG
  let : IsAffine (G₁).X.left := isAffine_of_isAffineHom (G₁).X.hom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth (G₁).X.hom := hG₁.smooth
  let : TopologicalSpace ((G₁).affinePoints (CommAlgCat.of K M)) := (G₁).affinePointsTopologicalSpace _
  let : TopologicalSpace ((G₂).affinePoints (CommAlgCat.of L M)) := (G₂).affinePointsTopologicalSpace _
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of F M)) := G.affinePointsTopologicalSpace _
  obtain ⟨V, hV, hVn, hVgood⟩ := exists_regular_squareCochainOpen hG₁ (inertRestriction v ξ)
    ((isTrivial_inertRestriction_iff v ξ hdeg hw hv).mpr hξ) τ hτ hτ₂
  let e := (((G₂).affinePointsRingPointHomeomorph (CommAlgCat.of L M)).symm.trans
    (affinePointsBaseChangeContinuousMulEquiv F L M G).symm.toHomeomorph).trans
    (affinePointsBaseChangeContinuousMulEquiv F K M G).toHomeomorph
  refine ⟨e ⁻¹' V, hV.preimage e.continuous, hVn.preimage e.surjective, fun f hf => ?_⟩
  let f₂ := RingPoint.changeRing (Algebra.ofId L M) (affinePointsBaseChangeMulEquiv F L L G f)
  let f₁ := affinePointsBaseChangeMulEquiv F K M G
    (ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ f)
  have hfcomp : e f₂ = f₁ := by
    change affinePointsBaseChangeMulEquiv F K M G
      ((affinePointsBaseChangeMulEquiv F L M G).symm
        (((G₂).affinePointsRingPointHomeomorph _).symm f₂)) = _
    rw [affinePointsRingPointHomeomorph_symm_apply]
    have hn : f₂ = affinePointsBaseChangeMulEquiv F L M G
        (ringTestMap F (IsScalarTower.toAlgHom F L M) ≫ f) :=
      affinePointsBaseChangeMulEquiv_naturality F L L M G (Algebra.ofId L M) f
    rw [hn, MulEquiv.symm_apply_apply]
  have hval := inertRestriction_twist_value v hdeg hw hv σ ξ f
  have hgood := hVgood (e f₂) hf
  rw [hfcomp, ← hval] at hgood
  exact ⟨toralCentralizer_of_inertRestriction v hdeg hw hv σ (ξ.twist f) hgood.1, hgood.2⟩

end Inert

end Langlands.GroupScheme.QuadraticToralReduction
