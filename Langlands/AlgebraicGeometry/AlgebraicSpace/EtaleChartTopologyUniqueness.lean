import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartLocalSeparation
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Uniqueness of the topology of Conrad's Proposition 5.4

Schemes are locally separated algebraic spaces, quasi-separated when their structure
morphism is. Consequently the scheme of every étale chart of finite type of a space over a
field lies in the class of the corrected Proposition 5.4, and over a henselian valued
field every admissible family of topologies agrees with the étale-chart topology on that
class.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section SchemeDiagonal

variable {S : Scheme.{u}}

/-- The diagonal of the presheaf of a scheme `U` over `S` is representable, and its
represented projections are base changes of the scheme diagonal of `U → S`; hence they
have every property `P` of that diagonal that is stable under base change. -/
theorem relative_diag_schemeYoneda (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderBaseChange] (U : Over S) (hU : P (pullback.diagonal U.hom)) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)
      (diag ((schemeYoneda S).obj U)) := by
  apply relative_diag_of_representsEqualizer P
  intro T x y
  let g : T ⟶ U ⊗ U := lift x.down y.down
  let d : U ⟶ U ⊗ U := lift (𝟙 U) (𝟙 U)
  have hd : d.left = pullback.diagonal U.hom := by
    apply Limits.pullback.hom_ext
    · rw [pullback.diagonal_fst]
      exact Limits.pullback.lift_fst (𝟙 U.left) (𝟙 U.left) (by simp)
    · rw [pullback.diagonal_snd]
      exact Limits.pullback.lift_snd (𝟙 U.left) (𝟙 U.left) (by simp)
  have hsq : IsPullback (pullback.snd g d).left (pullback.fst g d).left d.left g.left :=
    (IsPullback.of_hasPullback g d).flip.map (Over.forget S)
  refine ⟨Limits.pullback g d, pullback.fst g d, ?_, fun T' h => ⟨?_, fun hxy => ?_⟩, ?_⟩
  · infer_instance
  · rintro ⟨z, rfl⟩
    change ULift.up ((z ≫ pullback.fst g d) ≫ x.down) = ULift.up ((z ≫ pullback.fst g d) ≫ y.down)
    have e₁ : pullback.fst g d ≫ x.down = pullback.snd g d := by
      have := congrArg (· ≫ fst U U) (pullback.condition (f := g) (g := d))
      simpa [g, d] using this
    have e₂ : pullback.fst g d ≫ y.down = pullback.snd g d := by
      have := congrArg (· ≫ snd U U) (pullback.condition (f := g) (g := d))
      simpa [g, d] using this
    rw [Category.assoc, Category.assoc, e₁, e₂]
  · have hxy' : h ≫ x.down = h ≫ y.down := congrArg ULift.down hxy
    refine ⟨pullback.lift h (h ≫ x.down) ?_, pullback.lift_fst _ _ _⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp [g, d]
    · simp [g, d, hxy']
  · rw [← hd] at hU
    exact MorphismProperty.of_isPullback hsq hU

/-- Every scheme is a locally separated algebraic space. -/
theorem isLocallySeparated_schemeToSpace (U : Over S) :
    IsLocallySeparated ((schemeToSpace S).obj U) := by
  have : MorphismProperty.RespectsIso @IsImmersion.{u} :=
    IsImmersion.isStableUnderBaseChange.respectsIso
  exact relative_diag_schemeYoneda @IsImmersion U inferInstance

/-- A scheme whose structure morphism is quasi-separated is a quasi-separated algebraic
space. -/
theorem isQuasiSeparated_schemeToSpace (U : Over S) [QuasiSeparated U.hom] :
    IsQuasiSeparated ((schemeToSpace S).obj U) := by
  have : MorphismProperty.RespectsIso @QuasiCompact.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_schemeYoneda @QuasiCompact U inferInstance

end SchemeDiagonal

variable {K : Type u} [NontriviallyNormedField K]

/-- A scheme locally of finite type over a field lies in the class of the corrected
Proposition 5.4. -/
theorem isLocallySeparatedLocallyFiniteType_schemeToSpace (U : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType U.hom] :
    IsLocallySeparatedLocallyFiniteType K ((schemeToSpace _).obj U) := by
  have := LocallyOfFiniteType.isLocallyNoetherian U.hom
  exact ⟨⟨isQuasiSeparated_schemeToSpace U, LocallyOfFiniteTypeOverBase.of_scheme U inferInstance⟩,
    isLocallySeparated_schemeToSpace U⟩

/-- A chart map is an étale morphism of algebraic spaces. -/
theorem EtaleFiniteTypeChart.isEtaleMorphism {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (c : EtaleFiniteTypeChart K X) : IsEtaleMorphism c.hom :=
  fun _ _ hφ => IsEtale.comp hφ c.isEtale

/-- **Uniqueness**: over a nontrivially normed field, every admissible family of topologies
agrees with the étale-chart topology on quasi-separated, locally separated spaces locally of
finite type. -/
theorem eq_etaleChartTopology_of_isAdmissible
    (τ : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)), TopologicalSpace (RingPoints K X K))
    (hτ : IsAdmissibleRationalPointTopology K τ) (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (hX : IsLocallySeparatedLocallyFiniteType K X) : τ X = etaleChartTopology K X := by
  obtain ⟨hfun, hsch, -, -, -, het⟩ := hτ
  have hc : ∀ c : EtaleFiniteTypeChart K X,
      @Continuous _ _ (schemePointTopology K c.scheme K) (τ X) c.pointMap ∧
        @IsOpenMap _ _ (schemePointTopology K c.scheme K) (τ X) c.pointMap := by
    intro c
    have := c.locallyOfFiniteType
    have hU := isLocallySeparatedLocallyFiniteType_schemeToSpace c.scheme
    let : TopologicalSpace (RingPoints K ((schemeToSpace _).obj c.scheme) K) :=
      τ ((schemeToSpace _).obj c.scheme)
    let : TopologicalSpace (RingPoints K X K) := τ X
    let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
    let e := (schemeRingPointsEquiv K c.scheme K).toHomeomorphOfContinuousOpen
      (hsch c.scheme hU).continuous (hsch c.scheme hU).isOpenMap
    have he : (c.pointMap : RingPoint K c.scheme K → RingPoints K X K) =
        RingPoints.map (A := K) c.hom ∘ e.symm := rfl
    rw [he]
    exact ⟨(hfun c.hom hU hX).comp e.symm.continuous,
      (het c.hom hU hX c.isEtaleMorphism).isOpenMap.comp e.symm.isOpenMap⟩
  ext O
  constructor
  · intro hO
    rw [etaleChartTopology_isOpen_iff]
    intro c
    exact @Continuous.isOpen_preimage _ _ (schemePointTopology K c.scheme K) (τ X) _ (hc c).1 O hO
  · intro hO
    rw [etaleChartTopology_isOpen_iff] at hO
    refine @isOpen_iff_forall_mem_open _ (τ X) _ |>.2 fun x hx => ?_
    obtain ⟨c, y, rfl⟩ := hX.1.exists_chart x
    exact ⟨c.pointMap '' (c.pointMap ⁻¹' O), Set.image_preimage_subset _ _,
      (hc c).2 _ (hO c), ⟨y, hx, rfl⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
