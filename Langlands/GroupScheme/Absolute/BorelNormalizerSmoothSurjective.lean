import Langlands.GroupScheme.Absolute.BorelNormalizerSmoothCentralGm
import Langlands.GroupScheme.Absolute.BorelNormalizerSurjective
import Langlands.GroupScheme.Absolute.BorelHomogeneousQuotient

/-! # The surjective commutator branch through actual smooth quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Normal

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A smooth normal closed subgroup with a proper homogeneous quotient is the
whole connected smooth affine group. Its affine group quotient is constructed. -/
theorem isIso_of_smooth_normal_of_proper_homogeneousQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : N ⟶ G) (hi : IsClosedSubgroup i) (hN : Smooth N.X.hom)
    (hnormal : (SubgroupFunctor.range i).IsNormal)
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsIso i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let D := SmoothNormalQuotient.ofClosedNormal i hi hN hnormal
  have : IsAffineHom D.quotient.X.hom := D.isAffineHom
  have : IsAffine D.quotient.X.left := isAffine_of_isAffineHom D.quotient.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ G.X.hom
  have hrange := range_eq_top_of_proper_homogeneousQuotient
    i D.projection D.isFppfQuotient q hq
  have hirep : (⊤ : SubgroupFunctor G).IsRepresentedBy i := ⟨inferInstance, hrange⟩
  have hidrep : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro g
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨g, Category.comp_id g⟩
  let e : N ≅ G := hirep.isoOfIsRepresentedBy hidrep
  have he : e.hom = i := by
    simpa using hirep.isoOfIsRepresentedBy_hom_comp hidrep
  rw [← he]
  infer_instance

end Normal

section Borel

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B U H : GroupScheme (Spec (CommRingCat.of k))}

/-- The surjective commutator branch constructs its quotients and requires only
properness of parabolic quotients as its remaining quotient proposition. -/
theorem IsBorelSubgroup.isIso_of_surjective_commutator_of_parabolicQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    {i : B ⟶ G} (hi : IsBorelSubgroup i)
    (a : U ⟶ B) (t : H ⟶ B) (hU : IsUnipotent U)
    (φ : H ⟶ H)
    [LocallyOfFiniteType φ.hom.hom.left] [Surjective φ.hom.hom.left]
    (x : rationalPoints G)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (rationalPoints G)))
    (hcomm : ∀ s : rationalPoints H,
      (s ≫ φ.hom.hom) ≫ (t ≫ i).hom.hom =
        x * (s ≫ (t ≫ i).hom.hom) * x⁻¹ * (s ≫ (t ≫ i).hom.hom)⁻¹)
    (hfactor : Function.Surjective (rationalPointProductMap a t)) :
    IsIso i := by
  have : Smooth B.X.hom := hi.smooth
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  let R := hi.homogeneousQuotient
  have : Smooth R.projection.left := R.smooth_projection
  have : Surjective R.projection.left := R.surjective_projection
  have : QuasiCompact R.projection.left := R.quasiCompact_projection
  have : IsProper R.scheme.hom := hi.quotient_isProper_of_parabolicQuotient hproper R
  have hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ R.projection = h ≫ R.projection →
        g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T :=
    fun T g h he => (R.fibers T g h).mp he
  have hx' : x ∈ (SubgroupFunctor.range i).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [SubgroupFunctor.normalizer_range_carrier_base_eq_algClosed_points hi.isClosedSubgroup]
    exact hx
  have hn :=
    SubgroupFunctor.isNormal_range_of_surjective_commutator_of_proper_homogeneousQuotient
      i hi.isClosedSubgroup a t hU φ x hx' hcomm hfactor R.projection hq
  exact isIso_of_smooth_normal_of_proper_homogeneousQuotient
    i hi.isClosedSubgroup hi.smooth hn R.projection hq

/-- An actual Borel point in the surjective commutator branch. -/
def borelPointOfSurjectiveCommutator
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    {i : B ⟶ G} (hi : IsBorelSubgroup i)
    (a : U ⟶ B) (t : H ⟶ B) (hU : IsUnipotent U)
    (φ : H ⟶ H)
    [LocallyOfFiniteType φ.hom.hom.left] [Surjective φ.hom.hom.left]
    (x : rationalPoints G)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (rationalPoints G)))
    (hcomm : ∀ s : rationalPoints H,
      (s ≫ φ.hom.hom) ≫ (t ≫ i).hom.hom =
        x * (s ≫ (t ≫ i).hom.hom) * x⁻¹ * (s ≫ (t ≫ i).hom.hom)⁻¹)
    (hfactor : Function.Surjective (rationalPointProductMap a t)) :
    {p : rationalPoints B // p ≫ i.hom.hom = x} := by
  have := hi.isIso_of_surjective_commutator_of_parabolicQuotient
    hproper a t hU φ x hx hcomm hfactor
  refine ⟨x ≫ (inv i).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

end Borel

end Langlands.GroupScheme
