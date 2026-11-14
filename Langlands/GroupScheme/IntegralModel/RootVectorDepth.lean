import Langlands.GroupScheme.IntegralModel.NaturalVectorDepth

/-! # Depth models on actual root representatives without higher roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

variable {K : Type u} [Field K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G U : GroupScheme (Spec (CommRingCat.of K))}
  {i : S.toGrp ⟶ G} {a : characterLattice S} {j : U ⟶ G}
  (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)
  {n : ℕ}
  (c : ∀ X : Over (Spec (CommRingCat.of K)),
    (X ⟶ U.X) ≃* Multiplicative (Fin n → Γ(X.left, ⊤)))

/-- Rational coordinates induced by the original all-test section coordinates. -/
def rootRationalVectorCoordinates :
    rationalPoints U ≃* Multiplicative (Fin n → K) :=
  (c (Over.mk (𝟙 _))).trans (rootVectorRationalCoeffEquiv n)

variable (hc : RelativeRoot.IsWeightVectorCoordinates
  (RelativeRoot.subgroupAction i a j hj) a c)

/-- Positive weight coordinates on a supplied actual representative induce
the corresponding coordinates on the actual ambient rational root subgroup. -/
def weightedRootVectorCoordinatesOfRepresentation (hn : 0 < n) :
    WeightedRootVectorCoordinates i a where
  dimension := n
  dimension_pos := hn
  equiv := (rootRationalVectorCoordinates c).symm.trans (hj.pointsEquiv (Over.mk (𝟙 _)))
  conjugation := by
    intro s x
    let R := rootRationalVectorCoordinates c
    let d := RelativeRoot.subgroupAction i a j hj
    have hR (h : rationalPoints U) :
        R (d.act s h) = Multiplicative.ofAdd
          ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : K)
            • (R h).toAdd) := by
      apply Multiplicative.toAdd.injective
      funext l
      change (Scheme.ΓSpecIso (CommRingCat.of K)).hom
        ((c (Over.mk (𝟙 _)) (d.act s h)).toAdd l) = _
      rw [hc.2]
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.map_mul _ _
    have hd : d.act s (R.symm (Multiplicative.ofAdd x)) =
        R.symm (Multiplicative.ofAdd
          ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : K)
            • x)) := by
      apply R.injective
      rw [hR, R.apply_symm_apply, R.apply_symm_apply]
      rfl
    change (s ≫ i.hom.hom) * (R.symm (Multiplicative.ofAdd x) ≫ j.hom.hom) *
        (s ≫ i.hom.hom)⁻¹ =
      R.symm (Multiplicative.ofAdd
        ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s : K)
          • x)) ≫ j.hom.hom
    rw [← hd]
    exact (RelativeRoot.subgroupAction_act_comp i a j hj s _).symm

/-- The ambient root value evaluated on the representing inclusion is
exactly the minimum of the original rational vector coordinates. -/
theorem weightedRootVectorValue_representation
    (hn : 0 < n) (omega : AddValuation K (WithTop ℝ)) (g : rationalPoints U) :
    weightedRootVectorValue omega (weightedRootVectorCoordinatesOfRepresentation hj c hc hn)
        (rationalPoints.map j g) =
      finiteVectorValue omega (rootRationalVectorCoordinates c g).toAdd := by
  change weightedRootVectorValue omega (weightedRootVectorCoordinatesOfRepresentation hj c hc hn)
    (hj.pointsEquiv (Over.mk (𝟙 _)) g) = _
  rw [weightedRootVectorValue_of_mem]
  change finiteVectorValue omega
    (((rootRationalVectorCoordinates c).symm.trans
      (hj.pointsEquiv (Over.mk (𝟙 _)))).symm
        (hj.pointsEquiv (Over.mk (𝟙 _)) g)).toAdd = _
  simp only [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_symm]

section NoHigherRoots

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
  {a : characterLattice S} (ha : a ∈ relativeRoots i)
  (hhigh : RelativeRoot.HasNoHigherRoots i a)
  {U : GroupScheme (Spec (CommRingCat.of K))} {j : U ⟶ G}
  (hj : (RelativeRoot.subgroup i a).IsRepresentedBy j)

/-- The existing all-test weight coordinates on this very representative. -/
def noHigherRootVectorCoordinates :=
  RelativeRoot.weightVectorCoordinatesOfNoHigherRoots hS i ha.1 hhigh hj

/-- These coordinates have positive dimension because an actual root without
higher roots has a nonidentity rational point. -/
theorem noHigherRootVectorCoordinates_dimension_pos :
    0 < (noHigherRootVectorCoordinates hS i ha hhigh hj).1 := by
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  by_contra hn
  change ¬ 0 < d.1 at hn
  have hn0 : d.1 = 0 := by omega
  obtain ⟨g, hg, hg1⟩ := RelativeRoot.exists_rootPoint_of_noHigherRoots hS i ha hhigh
  let T : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  have hv : (hj.pointsEquiv T).symm ⟨g, hg⟩ = 1 := by
    apply (d.2.1 T).injective
    apply Multiplicative.toAdd.injective
    funext l
    exact Fin.elim0 (hn0 ▸ l)
  have hv' := congrArg (fun v => ((hj.pointsEquiv T v :
    (RelativeRoot.subgroup i a).carrier T) : T ⟶ G.X)) hv
  apply hg1
  simpa only [MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one] using hv'

/-- The rational weight coordinates induced by the same actual all-test choice. -/
def noHigherRootWeightedVectorCoordinates : WeightedRootVectorCoordinates i a :=
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  weightedRootVectorCoordinatesOfRepresentation hj d.2.1 d.2.2
    (noHigherRootVectorCoordinates_dimension_pos hS i ha hhigh hj)

variable (v : Valuation K (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
  (R : ValuationSubring K) (hvR : v.valuationSubring = R)

/-- An actual smooth depth model for every supplied representative of a root
without higher positive integral multiples. -/
def noHigherRootVectorDepthModel (r : ℝ) : IntegralModel R K U :=
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  naturalVectorDepthModel v hv R d.2.1 d.2.2.1 r

theorem noHigherRootVectorDepthModel_isSmooth (r : ℝ) :
    (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r).IsSmooth := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of R)
    (noHigherRootVectorCoordinates hS i ha hhigh hj).1).X.hom
  exact VectorGroup.smooth _ _

theorem noHigherRootVectorDepthModel_hasGeometricallyConnectedFibres (r : ℝ) :
    (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r).HasGeometricallyConnectedFibres := by
  change GeometricallyConnected (VectorGroup.groupScheme (CommRingCat.of R)
    (noHigherRootVectorCoordinates hS i ha hhigh hj).1).X.hom
  exact VectorGroup.geometricallyConnected _ _

include hvR in
/-- The actual model-point image is precisely the filtration of the induced
coordinate-minimum root value. No supplied-apartment comparison is assumed. -/
theorem noHigherRootVectorDepthModel_integralPoints_map
    (hH : HenselianLocalRing v.valuationSubring) (r : ℝ) :
    (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r).integralPoints.map
        (rationalPoints.map j) =
      weightedRootVectorFiltration (FieldTheory.henselianIntegerAddValuation v hH K)
        (noHigherRootWeightedVectorCoordinates hS i ha hhigh hj) r := by
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  let w := noHigherRootWeightedVectorCoordinates hS i ha hhigh hj
  have hmem (g : rationalPoints U) :
      g ∈ (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r).integralPoints ↔
        (r : WithTop ℝ) ≤
          weightedRootVectorValue (FieldTheory.henselianIntegerAddValuation v hH K) w
            (rationalPoints.map j g) := by
    dsimp only [w, noHigherRootWeightedVectorCoordinates]
    rw [weightedRootVectorValue_representation]
    change g ∈ (naturalVectorDepthModel v hv R d.2.1 d.2.2.1 r).integralPoints ↔ _
    rw [naturalVectorDepthModel_mem_integralPoints v hv R hvR,
      real_le_finiteVectorValue_iff]
    rfl
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hj.pointsEquiv (Over.mk (𝟙 _)) z).property, (hmem z).mp hz⟩
  · rintro ⟨hg, hv⟩
    let z := (hj.pointsEquiv (Over.mk (𝟙 _))).symm ⟨g, hg⟩
    have hz : rationalPoints.map j z = g :=
      hj.pointsEquiv_symm_comp ⟨g, hg⟩
    refine ⟨z, (hmem z).mpr ?_, hz⟩
    rwa [hz]

/-- The explicit deeper-to-shallower map extends the actual generic identity. -/
def noHigherRootVectorDepthTransition {r s : ℝ} (h : r ≤ s) :
    (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R s).Hom
      (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r) (𝟙 _) :=
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  vectorIsoDepthTransition v hv R hvR (RelativeRoot.vectorGroupIso d.2.1 d.2.2.1) h

include hvR in
/-- Every compatible identity extension between these actual root models has
a smooth, connected and unipotent scheme-theoretic special-fibre kernel. -/
theorem noHigherRootVectorDepthModel_kernel_properties {r s : ℝ} (h : r ≤ s)
    (φ : (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R s).Hom
      (noHigherRootVectorDepthModel hS i ha hhigh hj v hv R r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  let d := noHigherRootVectorCoordinates hS i ha hhigh hj
  exact vectorIsoDepthModel_kernel_properties v hv R hvR
    (RelativeRoot.vectorGroupIso d.2.1 d.2.2.1) h φ

end NoHigherRoots

end Langlands.GroupScheme.IntegralModel
