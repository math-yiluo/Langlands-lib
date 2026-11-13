import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExtensionDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceMorphismPointMap

/-!
# Descent of a dominating-extension valuative lift for separated morphisms

Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.41.4 (Tag 0ARH): for a separated
morphism `f : X ⟶ Y` of algebraic spaces, a lift of a valuative square after a dominating
extension `A → B` of valuation rings gives a lift over `A` itself.

Write `Z = X ×_Y Spec A`. The supplied section over `B` gives a morphism `Spec B ⟶ Z`. The
image `ζ'` of the closed point of `Spec B` lies over the closed point of `Spec A` (the map
`A → B` is local) and specializes from the point `ζ` of `Z` given by `x` (the generic point of
`Spec B` maps to `ζ`, and the point map is continuous). This is the situation produced by
universal closedness in `ValuativeExistence.exists_lift`; the remaining argument of that proof
(an étale chart through `ζ'` and `ValuativeExistence.exists_lift_of_chart`) only uses
separatedness.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ValuativeExtensionDescent

open ValuativeExistence

variable {S : Scheme.{u}} {A : Type u} [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S)
variable {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Y.sections (Over.mk s))

/-- The point map of the morphism `h_T ⟶ X ×_Y Spec A` given by a section over `T` is
continuous for the point topology of the base change. -/
theorem continuous_chartPointMap_zOf {T : Over S} (χ : X.sections T) (t : T ⟶ Over.mk s)
    (h : mapSections f T χ = Y.pullback t y) :
    Continuous[_, pointTopology (ValuativeExistence.baseChange s f y)]
      (chartPointMap (zOf s f y χ t h)) := by
  obtain ⟨U₀, a₀, -, ha₀, hs₀⟩ := X.exists_atlas
  let g : (schemeYoneda S).obj (Over.mk s) ⟶ Y.presheaf := uliftYonedaEquiv.{u + 1}.symm y
  have hcont := Points.continuous_map_of_atlas (zOf s f y χ t h)
    (SchemePullbackChart.atlas f a₀ g) (SchemePullbackChart.atlas_isEtale f a₀ g ha₀)
    (SchemePullbackChart.atlas_isSurjective f a₀ g hs₀)
  let := pointTopology ((schemeYoneda S).obj T)
  let := pointTopology (ValuativeExistence.baseChange s f y)
  exact hcont.comp (continuous_schemePoint T)

/-- The image in `|Spec A|` of a point of `h_T ⟶ X ×_Y Spec A` is its image under `t`. -/
theorem map_snd_chartPointMap_zOf {T : Over S} (χ : X.sections T) (t : T ⟶ Over.mk s)
    (h : mapSections f T χ = Y.pullback t y) (w : T.left) :
    Points.map (pullback.snd _ _ : ValuativeExistence.baseChange s f y ⟶ _)
        (chartPointMap (zOf s f y χ t h) w) =
      schemePoint (Over.mk s) (t.left w) := by
  change Points.map _ (Points.map _ (schemePoint _ w)) = _
  rw [← Points.map_comp, zOf_snd]
  exact schemePoint_naturality _ _

/-- **Lift from a specialization.** Let `ζ` be the point of `X ×_Y Spec A` given by `x`. A point
`ζ'` in the closure of `ζ` lying over the closed point of `Spec A` gives a lift of `x` over
`Spec A` lying over `y`. This is the part of `ValuativeExistence.exists_lift` after the use of
universal closedness. -/
theorem exists_lift_of_mem_closure [IsDomain A] [ValuationRing A] {K : Type u} [Field K]
    [Algebra A K] [IsFractionRing A K] (hf : IsSeparatedMorphism f)
    (x : X.sections (algTest s K)) (hx : mapSections f _ x = Y.pullback (algTestBase s K) y)
    (ζ' : Points (ValuativeExistence.baseChange s f y))
    (hζ'C : ζ' ∈ @closure _ (pointTopology (ValuativeExistence.baseChange s f y))
      {chartPointMap (zOf s f y x (algTestBase s K) hx) (IsLocalRing.closedPoint K)})
    (hζ'm : Points.map (pullback.snd _ _ : ValuativeExistence.baseChange s f y ⟶ _) ζ' =
      schemePoint (Over.mk s) (IsLocalRing.closedPoint A)) :
    ∃ a : X.sections (Over.mk s),
      X.pullback (algTestBase s K) a = x ∧ mapSections f _ a = y := by
  let := pointTopology (ValuativeExistence.baseChange s f y)
  obtain ⟨P, _, _, ξ, hξ, u', hb, hu'⟩ := exists_algTest_chart s f y ζ'
  have hu'm : (algTestBase s P).left u' = IsLocalRing.closedPoint A := by
    have h := congrArg (schemePointsTo (Over.mk s))
      ((map_snd_chartPointMap s f y ξ hξ u').symm.trans
        ((congrArg (Points.map (pullback.snd _ _ : ValuativeExistence.baseChange s f y ⟶ _))
          hu').trans hζ'm))
    exact (schemePointsTo_schemePoint _ _).symm.trans (h.trans (schemePointsTo_schemePoint _ _))
  let v : Ideal P := (show PrimeSpectrum P from u').asIdeal
  have : v.IsPrime := (show PrimeSpectrum P from u').isPrime
  have hv : (IsLocalRing.maximalIdeal A).map (algebraMap A P) ≤ v := by
    rw [Ideal.map_le_iff_le_comap]
    exact (congrArg PrimeSpectrum.asIdeal hu'm).ge
  refine exists_lift_of_chart s f y hf hx hξ hb v hv fun p hp => ?_
  -- The basic open `D(p) ∋ v` has open image containing `ζ'`, hence `ζ`.
  let O : Set (algTest s P).left := (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum P))
  have hO := isOpen_image_chartPointMap (zOf s f y ξ (algTestBase s P) hξ) hb
    (O := O) (PrimeSpectrum.basicOpen p).isOpen
  obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp hζ'C _ hO ⟨u', hp, hu'⟩
  rw [Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨w, hwO, hwζ⟩ := hzO
  obtain ⟨T, g, h, τ, he, hg, -⟩ := (chartPointMap_eq_iff_sameImage₂ _ _ w _).mp hwζ
  have hsec : X.pullback g ξ = X.pullback h x := by
    have h1 := congrArg (fun k => k ≫ pullback.fst _ _) he
    simp only [Category.assoc, zOf_fst, map_comp_symm] at h1
    exact uliftYonedaEquiv.{u + 1}.symm.injective h1
  have hbase : g ≫ algTestBase s P = h ≫ algTestBase s K := by
    have h2 := congrArg (fun k => k ≫ pullback.snd _ _) he
    simp only [Category.assoc, zOf_snd, ← Functor.map_comp] at h2
    exact (schemeYoneda S).map_injective h2
  obtain ⟨R, _, _, φ, ψ, e, hφ, hψ, hne⟩ := exists_residueField_algHom s g h hbase τ
  refine ⟨R, inferInstance, inferInstance, ψ, φ, ?_, hne p ?_⟩
  · rw [← hφ, ← hψ, pullback_comp, pullback_comp, hsec]
  · rw [hg]
    exact hwO

/-- **Descent from a lift over a scheme.** Let `b` be a section over `T` with `f(b) = y|_T`
through `t : T ⟶ Spec A`, and let `e_L : T_L ⟶ T`, `e_K : T_L ⟶ Spec K` be morphisms over
`Spec A` along which `b` and `x` restrict to the same section. If some point of `T_L` maps
under `e_L` to a point `m` of `T` that specializes to a point over the closed point of
`Spec A`, then `x` extends over `Spec A`. -/
theorem exists_lift_of_specializes [IsDomain A] [ValuationRing A] {K : Type u} [Field K]
    [Algebra A K] [IsFractionRing A K] (hf : IsSeparatedMorphism f)
    (x : X.sections (algTest s K)) (hx : mapSections f _ x = Y.pullback (algTestBase s K) y)
    {T TL : Over S} (b : X.sections T) (t : T ⟶ Over.mk s)
    (hbY : mapSections f T b = Y.pullback t y) (eL : TL ⟶ T) (eK : TL ⟶ algTest s K)
    (hbase : eL ≫ t = eK ≫ algTestBase s K) (hbL : X.pullback eL b = X.pullback eK x)
    (w : TL.left) (m : T.left) (hw : eL.left w ⤳ m)
    (hm : t.left m = IsLocalRing.closedPoint A) :
    ∃ a : X.sections (Over.mk s),
      X.pullback (algTestBase s K) a = x ∧ mapSections f _ a = y := by
  let := pointTopology (ValuativeExistence.baseChange s f y)
  have hz : (schemeYoneda S).map eL ≫ zOf s f y b t hbY =
      (schemeYoneda S).map eK ≫ zOf s f y x (algTestBase s K) hx := by
    apply pullback.hom_ext
    · simp only [Category.assoc, zOf_fst, map_comp_symm]
      exact congrArg _ hbL
    · simp only [Category.assoc, zOf_snd, ← Functor.map_comp, hbase]
  refine exists_lift_of_mem_closure s f y hf x hx (chartPointMap (zOf s f y b t hbY) m) ?_ ?_
  · have h2 := hw.map (continuous_chartPointMap_zOf s f y b t hbY)
    rw [specializes_iff_mem_closure] at h2
    convert h2 using 3
    rw [← chartPointMap_comp eL, hz, chartPointMap_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  · rw [map_snd_chartPointMap_zOf, hm]

end ValuativeExtensionDescent

open ValuativeExtensionDescent in
/-- **Stacks 67.41.4.** For a separated morphism of algebraic spaces, a valuative lift after a
dominating extension of valuation rings descends to a lift over the original valuation ring. -/
theorem spaceValuativeExtensionDescent : SpaceValuativeExtensionDescentStatement.{u} := by
  intro S X Y f hf A _ _ _ K _ _ _ s x y hx hlift
  obtain ⟨B, _, _, _, L, _, _, _, i, hi, j, hij, b, hbL, hbY⟩ := hlift
  refine exists_lift_of_specializes s f y hf x hx b _ hbY _ _ ?_ hbL
    (IsLocalRing.closedPoint L) (IsLocalRing.closedPoint B)
    (IsLocalRing.specializes_closedPoint _) (IsLocalRing.comap_closedPoint i)
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hij]

end Langlands.AlgebraicGeometry.AlgebraicSpace
