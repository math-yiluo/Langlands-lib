import Langlands.Representation.Exponents.CasselmanCentralDirections
import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation

/-! # The positive-cone clause for full represented parabolics

For an actual represented parabolic `p : P ⟶ G` that is an isomorphism, every compatible
root presentation has all simple roots in its face, so its positive cone contains `0`;
this uses the Levi half of the standard-cocharacter realization. Every normalized Jacquet
exponent of a representation with a unitary central character then has zero normalized
real part, so it lies in the positive cone. This extends the published identity-parabolic
clause `IdentityParabolicCasselmanConeStatement` from `p = l = 𝟙 G` to arbitrary full
represented parabolics.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The range of an isomorphism of group schemes is the whole group. -/
theorem SubgroupFunctor.range_eq_top_of_isIso {S : Scheme.{u}} {H G : GroupScheme S}
    (f : H ⟶ G) [IsIso f] : SubgroupFunctor.range f = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro x _
  refine SubgroupFunctor.mem_range.mpr ⟨x ≫ (inv f).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

namespace ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- If the Levi image is the whole group, every simple root lies in the standard face:
the realizing standard cocharacter is central, so it pairs to zero with every root. -/
theorem simpleRelativeRoots_subset_of_range_eq_top (r : ParabolicRootPresentation p l a)
    (h : SubgroupFunctor.range (l ≫ p) = ⊤) :
    simpleRelativeRoots r.data.i r.data.ν ⊆ r.data.J := by
  obtain ⟨ζ, hζ, -, hM⟩ := r.isCompatible.realization
  have hc : IsCentral (CommGroupScheme.groupHom ζ ≫ r.data.i) :=
    (isCentral_iff_dynamicCentralizer_eq_top _).mpr (hM.symm.trans h)
  intro α hα
  by_contra hJ
  have hpos := hζ.2.2 α hα hJ
  have hzero := root_restrict_eq_zero_of_isCentral r.data.i ζ isSplitTorus_gm hc
    (positiveRelativeRoots_subset_relativeRoots _ _ (simpleRelativeRoots_subset_positive _ _ hα))
  rw [latticePairing_apply, hzero, map_zero] at hpos
  exact lt_irrefl _ hpos

/-- If the Levi image is the whole group, the positive cone contains zero. -/
theorem zero_mem_positiveCone_of_range_eq_top (r : ParabolicRootPresentation p l a)
    (h : SubgroupFunctor.range (l ≫ p) = ⊤) :
    (0 : RealTorusSpace.Vstar A) ∈ r.positiveCone :=
  r.zero_mem_positiveCone_iff_simpleRoots_subset.mpr
    (r.simpleRelativeRoots_subset_of_range_eq_top h)

/-- If the Levi inclusion into the ambient group is an isomorphism, the positive cone
contains zero. -/
theorem zero_mem_positiveCone_of_isIso (r : ParabolicRootPresentation p l a)
    [IsIso (l ≫ p)] : (0 : RealTorusSpace.Vstar A) ∈ r.positiveCone :=
  r.zero_mem_positiveCone_of_range_eq_top (SubgroupFunctor.range_eq_top_of_isIso _)

end ParabolicRootPresentation

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Center

variable {k : Type u} [Field k] {G P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Through an isomorphism `l ≫ p`, every split-component point is central in `G(k)`. -/
theorem splitComponentPointsMap_mem_center_of_isIso (p : P ⟶ G) (l : M ⟶ P) [IsIso (l ≫ p)]
    (ha : IsSplitComponent a) (t : rationalPoints A.toGrp) :
    (splitComponentPointsMap (l ≫ p) a t : rationalPoints G) ∈
      Subgroup.center (rationalPoints G) := by
  have hsurj : Function.Surjective (rationalPoints.map (l ≫ p)) := by
    intro y
    refine ⟨rationalPoints.map (inv (l ≫ p)) y, ?_⟩
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
  exact Subgroup.map_center_le_center hsurj
    ⟨rationalPoints.map a t, ha.isCentralSplitTorus.isCentral.map_mem_center t, rfl⟩

end Center

section Exponents

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullParabolicAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Through an isomorphism `l ≫ p`, every normalized Jacquet exponent of a representation
with a unitary central character has zero normalized real part. -/
theorem normalizedJacquetExponent_realPart_eq_zero_of_isIso [IsIso (l ≫ p)]
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 := by
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  apply (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff
    ha.isCentralSplitTorus.1.1 χ hχ.1).mpr
  intro t
  exact normalizedJacquetExponent_norm_eq_one_of_mem_center p l r hp hl hr hmul ha π c χ hχ t
    (splitComponentPointsMap_mem_center_of_isIso p l ha t)

/-- Through an isomorphism `l ≫ p`, every normalized Jacquet exponent of a representation
with a unitary central character lies in the positive cone of every compatible root
presentation. -/
theorem normalizedJacquetExponent_mem_positiveCone_of_isIso [LocallyOfFiniteType G.X.hom]
    [IsIso (l ≫ p)] (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation) (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone := by
  rw [normalizedJacquetExponent_realPart_eq_zero_of_isIso p l r hp hl hr hmul ha π c χ hχ]
  exact pres.zero_mem_positiveCone_of_isIso

end Exponents

/-- The positive-cone clause of the represented Casselman criterion at every full actual
parabolic: if `p : P ⟶ G` is an isomorphism, every normalized Jacquet exponent along it of a
smooth representation with a unitary central character has normalized real part in the
positive cone of every compatible root presentation. -/
def FullParabolicCasselmanConeStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
      (pres : ParabolicRootPresentation p l a),
      IsIso p →
      ∀ (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
        Nonempty (UnitaryCentralCharacter π.representation) →
        ∀ χ : rationalPoints A.toGrp →* ℂˣ,
          IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
            Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
              pres.positiveCone

/-- The full-parabolic positive-cone clause holds: the rational Levi of a full parabolic of
a connected reductive group is an isomorphism, and the cone and real-part lemmas above
apply. -/
theorem fullParabolicCasselmanCone : FullParabolicCasselmanConeStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U A p l r a hp hl hr hmul ha pres hpIso π hc χ hχ
  have : IsIso l := hl.isIso_of_isIso_parabolic (p := p) hG
  obtain ⟨c⟩ := hc
  exact normalizedJacquetExponent_mem_positiveCone_of_isIso p l r hp hl hr hmul ha pres π c χ hχ

end Langlands.Aubert.General.RepresentedParabolic
