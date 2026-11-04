import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinates
import Langlands.HarmonicAnalysis.TriangularHaarModulus
import Langlands.Global.AdelicScalarHaarChar

/-!
# The modulus of the positive torus on the standard unipotent subgroup

`positiveTorusUnipotentModulus_of_coordinates` derives the Library proposition
`PositiveTorusUnipotentModulusStatement` from `PositiveTorusTriangularCoordinatesStatement`.
The paired Markdown records the argument.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]

/-- If global functions `t` identify the coordinate ring with a polynomial ring, then every
`c : Fin d → A` is the coordinate vector of an `A`-point. -/
theorem exists_affinePoint_evaluation {d : ℕ} {t : Fin d → AffineCoordinateRing F U.X}
    (ht : Function.Bijective
      (MvPolynomial.aeval t : MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F U.X))
    (A : Type u) [CommRing A] [Algebra F A] (c : Fin d → A) :
    ∃ x : U.affinePoints (CommAlgCat.of F A),
      ∀ k, U.affinePointEvaluation (CommAlgCat.of F A) x (t k) = c k := by
  let e := AlgEquiv.ofBijective _ ht
  let φ : AffineCoordinateRing F U.X →ₐ[F] A := (MvPolynomial.aeval c).comp e.symm.toAlgHom
  refine ⟨(affineSchemePointEquiv F U.X A).symm (AlgPoint.ofAlgHom φ), fun k => ?_⟩
  have h := U.affineSchemePointEquiv_evaluation (CommAlgCat.of F A)
    ((affineSchemePointEquiv F U.X A).symm (AlgPoint.ofAlgHom φ)) (t k)
  rw [Equiv.apply_symm_apply, AlgPoint.ofAlgHom_apply] at h
  rw [← h]
  have he : e.symm (t k) = MvPolynomial.X k :=
    e.symm_apply_eq.mpr (MvPolynomial.aeval_X t k).symm
  simp [φ, he]

end Langlands.GroupScheme

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine U.X.left]

/-- **Polynomial coordinates on adelic points.** If global functions `t` identify the
coordinate ring of `U` with a polynomial ring, evaluation at `t` is a homeomorphism
`U(𝔸_F) ≃ₜ 𝔸_F^d`. -/
def coordinateHomeomorph {d : ℕ} {t : Fin d → AffineCoordinateRing F U.X}
    (ht : Function.Bijective
      (MvPolynomial.aeval t : MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F U.X)) :
    AdelicGroupPoints F U ≃ₜ (Fin d → Adeles F) :=
  (U.isEmbedding_affinePointFiniteEvaluation (CommAlgCat.of F (Adeles F)) d t (by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr ht.2)).toHomeomorphOfSurjective fun c => by
    obtain ⟨x, hx⟩ := U.exists_affinePoint_evaluation ht (Adeles F) c
    exact ⟨x, funext hx⟩

@[simp]
theorem coordinateHomeomorph_apply {d : ℕ} {t : Fin d → AffineCoordinateRing F U.X}
    (ht : Function.Bijective
      (MvPolynomial.aeval t : MvPolynomial (Fin d) F →ₐ[F] AffineCoordinateRing F U.X))
    (x : AdelicGroupPoints F U) (k : Fin d) :
    coordinateHomeomorph U ht x k =
      U.affinePointEvaluation (CommAlgCat.of F (Adeles F)) x (t k) :=
  rfl

end Langlands.Global.AdelicGroupPoints

namespace Langlands.HaarModulus

/-- **Normalizer modulus in triangular coordinates.** The closed-subgroup normalizer
character is computed by `mulEquivHaarChar_eq_prod_of_triangular`. -/
theorem closedNormalizerCharacter_eq_prod_of_triangular {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : Subgroup G)
    (hU : IsClosed (U : Set G)) (g : Subgroup.normalizer (U : Set G))
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (ν : Measure A) [IsAddHaarMeasure ν] {d : ℕ} (Φ : U ≃ₜ (Fin d → A))
    (htri : ∀ h : U, HarmonicAnalysis.IsTriangularShear fun v => Φ (h * Φ.symm v))
    (s : Fin d → A → A) (hs : ∀ k, Measurable (s k)) (r : Fin d → ℝ≥0)
    (hr : ∀ k, r k • ν.map (s k) = ν)
    (hψ : ∀ h k, Φ (normalizerConj U g h) k = s k (Φ h k)) :
    (closedNormalizerCharacter U hU g : ℝ≥0) = ∏ k, r k := by
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have := hU.locallyCompactSpace
  exact HarmonicAnalysis.mulEquivHaarChar_eq_prod_of_triangular ν Φ htri _ s hs r hr hψ

end Langlands.HaarModulus

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints NumberField IsDedekindDomain
open scoped RestrictedProduct

/-- **The positive-torus modulus from weighted triangular coordinates.**
`PositiveTorusTriangularCoordinatesStatement` implies `PositiveTorusUnipotentModulusStatement`. -/
theorem positiveTorusUnipotentModulus_of_coordinates
    (hcoord : PositiveTorusTriangularCoordinatesStatement.{u}) :
    PositiveTorusUnipotentModulusStatement.{u} := by
  classical
  intro F _ _ G _ _ hG T i ν T₀ j hsetup
  obtain ⟨hTmax, hgen, -⟩ := id hsetup
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x
  have hcl := Standard.isClosedSubgroup_unipotentHom i ν ∅
  have : IsAffineHom (Standard.unipotentScheme i ν ∅).X.hom := hcl.isAffineHom
  have : IsAffine (Standard.unipotentScheme i ν ∅).X.left :=
    isAffine_of_isAffineHom (Standard.unipotentScheme i ν ∅).X.hom
  obtain ⟨d, t, P, w, ht, hP, hmul, hconj, hpos, hcard⟩ := hcoord F G hG T i ν hTmax hgen
  -- topology and measure on the adeles
  have := adeles_locallyCompactSpace F
  have := adeles_secondCountableTopology F
  let _ : MeasurableSpace (Adeles F) := borel _
  have : BorelSpace (Adeles F) := ⟨rfl⟩
  -- coordinates on `N(𝔸_F)`
  let Φ₀ := coordinateHomeomorph (Standard.unipotentScheme i ν ∅) ht
  let ev : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅) → (Fin d → Adeles F) := Φ₀
  have hev_mul : ∀ u u' k, ev (u * u') k =
      ev u k + ev u' k + MvPolynomial.aeval (Sum.elim (ev u) (ev u')) (P k) :=
    fun u u' k => hmul (CommAlgCat.of F (Adeles F)) u u' k
  have hev_symm : ∀ v, ev (Φ₀.symm v) = v := fun v => Φ₀.apply_symm_apply v
  -- the closed image `N(𝔸_F) ⊆ G(𝔸_F)` and its coordinates
  let f := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅)
  have hf : IsClosedEmbedding f := isClosedEmbedding_map_of_isClosedSubgroup F _ hcl
  have hrange : ∀ g : standardUnipotentImage F G T i ν, ∃ u, f u = g := fun g =>
    MonoidHom.mem_range.mp g.2
  have hmemH : ∀ u, f u ∈ standardUnipotentImage F G T i ν := fun u =>
    MonoidHom.mem_range.mpr ⟨u, rfl⟩
  let Ψ : (Fin d → Adeles F) → standardUnipotentImage F G T i ν :=
    fun v => ⟨f (Φ₀.symm v), hmemH _⟩
  have hΨ : IsEmbedding Ψ := by
    refine ⟨IsInducing.subtypeVal.of_comp_iff.mp ?_, fun v w hvw => ?_⟩
    · exact hf.isInducing.comp Φ₀.symm.isInducing
    · exact Φ₀.symm.injective (hf.injective (congrArg Subtype.val hvw))
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨u, hu⟩ := hrange g
    refine ⟨Φ₀ u, Subtype.ext ?_⟩
    change f (Φ₀.symm (Φ₀ u)) = g
    rw [Φ₀.symm_apply_apply, hu]
  let Φ : standardUnipotentImage F G T i ν ≃ₜ (Fin d → Adeles F) :=
    (hΨ.toHomeomorphOfSurjective hΨs).symm
  have hΦ : ∀ (h : standardUnipotentImage F G T i ν) u, f u = h → Φ h = ev u := by
    intro h u hu
    have h1 : Ψ (ev u) = h := Subtype.ext (by
      change f (Φ₀.symm (Φ₀ u)) = h
      rw [Φ₀.symm_apply_apply, hu])
    rw [← h1]
    exact (hΨ.toHomeomorphOfSurjective hΨs).symm_apply_apply (ev u)
  have hΦs : ∀ v, ((Φ.symm v : standardUnipotentImage F G T i ν) :
      AdelicGroupPoints F G) = f (Φ₀.symm v) := fun v => rfl
  -- left translations are triangular shears
  have htri : ∀ g : standardUnipotentImage F G T i ν,
      HarmonicAnalysis.IsTriangularShear fun v => Φ (g * Φ.symm v) := by
    intro g k v w hvw
    obtain ⟨ug, hug⟩ := hrange g
    have key : ∀ v, Φ (g * Φ.symm v) k - v k =
        ev ug k + MvPolynomial.aeval (Sum.elim (ev ug) v) (P k) := by
      intro v
      rw [hΦ (g * Φ.symm v) (ug * Φ₀.symm v) (by
        rw [map_mul, hug, Subgroup.coe_mul, hΦs]), hev_mul, hev_symm]
      ring
    rw [key v, key w]
    congr 1
    apply aeval_eq_of_forall_mem_vars
    intro l hl
    rcases l with l | l
    · rfl
    · exact hvw l (hP k _ hl)
  -- the positive torus element and its characters
  let s : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F (Adeles F)) :=
    x.1 ≫ (CommGroupScheme.groupHom j).hom.hom
  have ha : positiveMap F G T i T₀ j x =
      GroupScheme.affinePointsTarget T.toGrp i (CommAlgCat.of F (Adeles F)) s := by
    change x.1 ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom =
      (x.1 ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom
    rw [Category.assoc]
    rfl
  have hσ : ∀ k, ∃ σ : ℝ≥0ˣ, PositiveRealIdeles.full F σ = Lie.characterValue (w k) s := by
    intro k
    obtain ⟨σ, hσ⟩ := (PositiveRealTorus.mem_intrinsicSubgroup_iff F T₀ x.1).mp x.2 (j ≫ w k)
    exact ⟨σ, hσ.trans (Lie.characterValue_comp j (w k) x.1)⟩
  choose σ hσ using hσ
  -- conjugation acts diagonally in the coordinates
  have hψ : ∀ (h : standardUnipotentImage F G T i ν) k,
      Φ (HaarModulus.normalizerConj (standardUnipotentImage F G T i ν)
          ⟨positiveMap F G T i T₀ j x, positiveMap_mem_normalizer F G T i ν T₀ j x⟩ h) k =
        (PositiveRealIdeles.full F (σ k) : Adeles F) * Φ h k := by
    intro h k
    obtain ⟨u, hu⟩ := hrange h
    obtain ⟨y, hy⟩ := hrange (HaarModulus.normalizerConj (standardUnipotentImage F G T i ν)
      ⟨positiveMap F G T i T₀ j x, positiveMap_mem_normalizer F G T i ν T₀ j x⟩ h)
    rw [hΦ _ y hy, hΦ h u hu, hσ k]
    refine hconj (CommAlgCat.of F (Adeles F)) s u y ?_ k
    have hy' := hy
    rw [HaarModulus.normalizerConj_apply, ← hu] at hy'
    rw [← ha]
    exact hy'
  -- the Haar measure on the adeles and the coordinate scalings
  let μA : Measure (Adeles F) := addHaar
  have : Regular μA := by
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Adeles F)) := inferInstance
    exact regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  have hr : ∀ k, ((σ k : ℝ≥0) ^ Module.finrank ℚ F) •
      μA.map (fun z => (PositiveRealIdeles.full F (σ k) : Adeles F) * z) = μA := by
    intro k
    have h1 := addEquivAddHaarChar_smul_map μA
      (ContinuousAddEquiv.mulLeft (PositiveRealIdeles.full F (σ k)))
    rw [PositiveRealIdeles.addEquivAddHaarChar_mulLeft_full] at h1
    exact h1
  refine (HaarModulus.closedNormalizerCharacter_eq_prod_of_triangular _
    (isClosed_standardUnipotentImage F G T i ν) _ μA Φ htri _
    (fun k => (continuous_const.mul continuous_id).measurable) _ hr hψ).trans ?_
  -- regroup the coordinate factors by root
  let g : characterLattice T → ℝ≥0 := fun β =>
    (PositiveRealTorus.normCharacter F T₀ (j ≫ β) x : ℝ≥0)
  have hnorm : ∀ k, (σ k : ℝ≥0) ^ Module.finrank ℚ F = g (w k) := by
    intro k
    change _ = ((IdeleAbsoluteValue.full F (Lie.characterValue (j ≫ w k) x.1) : ℝ≥0ˣ) : ℝ≥0)
    rw [Lie.characterValue_comp j (w k) x.1, ← hσ k, PositiveRealIdeles.absoluteValue_full,
      Units.val_pow_eq_pow_val]
  have hsub : ((Finset.univ.image w : Finset (characterLattice T)) : Set (characterLattice T)) ⊆
      positiveRelativeRoots i ν := by
    intro β hβ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hβ
    exact hpos k
  rw [Finset.prod_congr rfl fun k _ => hnorm k, Finset.prod_comp g w]
  rw [finprod_mem_eq_prod_of_subset _ ?_ hsub]
  · apply Finset.prod_congr rfl
    intro β hβ
    rw [← hcard β (hsub hβ), Nat.card_eq_fintype_card, Fintype.card_subtype]
  · rintro β ⟨hβ, hne⟩
    by_contra hni
    apply hne
    have hempty : IsEmpty {k // w k = β} :=
      ⟨fun k => hni (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k.1, Finset.mem_univ _, k.2⟩))⟩
    change g β ^ Module.finrank F (weightSpace i β) = 1
    rw [← hcard β hβ, Nat.card_of_isEmpty, pow_zero]

end Langlands.Global.AdelicSiegelFactors
