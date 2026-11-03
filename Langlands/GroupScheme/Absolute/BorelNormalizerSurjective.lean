import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineFixed
import Langlands.GroupScheme.MatrixRepresentation.HomogeneousOrbit
import Langlands.GroupScheme.NormalProperQuotient
import Langlands.GroupScheme.Absolute.RationalNormalizer

/-! # The surjective-commutator branch of Borel self-normalization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace SubgroupFunctor

section NormalizerFactor

variable {S : Scheme.{u}} {G B N : GroupScheme S} {iN : N ⟶ G}

/-- The canonical factorization of a subgroup through a representative of its
all-test normalizer. -/
def normalizerFactor (i : B ⟶ G) (hN : (range i).normalizer.IsRepresentedBy iN) :
    B ⟶ N :=
  hN.factorHom i (range i).le_normalizer

/-- The normalizer factor followed by its inclusion is the original subgroup. -/
theorem normalizerFactor_comp (i : B ⟶ G)
    (hN : (range i).normalizer.IsRepresentedBy iN) :
    normalizerFactor i hN ≫ iN = i :=
  hN.factorHom_comp i (range i).le_normalizer

end NormalizerFactor

section SurjectiveCommutator

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B U H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- Surjectivity of a commutator on the second rational factor forces a closed
subgroup with proper homogeneous quotient to be normal. -/
theorem isNormal_range_of_surjective_commutator_of_proper_homogeneousQuotient
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] [IsReduced G.X.left]
    [IsReduced B.X.left] [LocallyOfFiniteType B.X.hom]
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (i : B ⟶ G) (hi : IsClosedSubgroup i)
    (a : U ⟶ B) (t : H ⟶ B) (hU : IsUnipotent U)
    (φ : H ⟶ H)
    [LocallyOfFiniteType φ.hom.hom.left] [Surjective φ.hom.hom.left]
    (x : rationalPoints G)
    (hx : x ∈ (range i).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ s : rationalPoints H,
      (s ≫ φ.hom.hom) ≫ (t ≫ i).hom.hom =
        x * (s ≫ (t ≫ i).hom.hom) * x⁻¹ * (s ≫ (t ≫ i).hom.hom)⁻¹)
    (hfactor : Function.Surjective (rationalPointProductMap a t))
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (range i).carrier T) :
    (range i).IsNormal := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨N, iN, hiN, hN⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range i hi).1
  obtain ⟨n, j, ρ, hline⟩ := Chevalley.exists_line_stabilizer k G N iN hiN
  let f := normalizerFactor i hN
  have hf : f ≫ iN = i := normalizerFactor_comp i hN
  have hfo : f.hom.hom ≫ iN.hom.hom = i.hom.hom := by
    rw [← Grp.comp_hom_hom, hf]
  let xN : rationalPoints N := (hN.pointsEquiv _).symm ⟨x, hx⟩
  have hxN : xN ≫ iN.hom.hom = x := hN.pointsEquiv_symm_comp ⟨x, hx⟩
  have hcommN : ∀ s : rationalPoints H,
      (s ≫ φ.hom.hom) ≫ (t ≫ f).hom.hom =
        xN * (s ≫ (t ≫ f).hom.hom) * xN⁻¹ * (s ≫ (t ≫ f).hom.hom)⁻¹ := by
    intro s
    apply hN.1.right_cancellation
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Grp.comp_hom_hom,
      Category.assoc, hfo, hxN] using hcomm s
  have hlineN : (ρ.restrict iN).StabilizesCoordinateLine j := by
    intro T y
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hline T (y ≫ iN.hom.hom)).mp (mem_range.mpr ⟨y, rfl⟩)
  have hv := (ρ.restrict iN).isFixedVector_coordinateVector_of_surjective_commutator
    j hlineN f a t hU φ xN hcommN hfactor
  rw [MatrixRepresentation.restrict_comp, hf] at hv
  have htop := ρ.range_eq_top_of_proper_homogeneousQuotient
    j iN hline i q hq hv
  have hn : (range i).normalizer = ⊤ := hN.2.symm.trans htop
  change (range i).IsNormalizedBy ⊤
  rw [← hn]
  exact (range i).isNormalizedBy_normalizer

end SurjectiveCommutator

end SubgroupFunctor

section Borel

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B U H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A Borel inclusion is an isomorphism in the surjective-commutator branch,
given the actual proper quotient and the affine normal-subgroup quotient
existence proposition. -/
theorem IsBorelSubgroup.isIso_of_surjective_commutator_of_proper_homogeneousQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsReduced H.X.left] [LocallyOfFiniteType H.X.hom]
    (hquot : NormalSubgroupQuotientStatement.{u})
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
    (hfactor : Function.Surjective (rationalPointProductMap a t))
    (q : G.X ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) :
    IsIso i := by
  have : Smooth B.X.hom := hi.smooth
  have : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  have hx' : x ∈ (SubgroupFunctor.range i).normalizer.carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [SubgroupFunctor.normalizer_range_carrier_base_eq_algClosed_points hi.isClosedSubgroup]
    exact hx
  have hn := SubgroupFunctor.isNormal_range_of_surjective_commutator_of_proper_homogeneousQuotient
    i hi.isClosedSubgroup a t hU φ x hx' hcomm hfactor q hq
  exact isIso_of_normal_of_proper_homogeneousQuotient hquot i hi.isClosedSubgroup hn q hq

end Borel

end Langlands.GroupScheme
