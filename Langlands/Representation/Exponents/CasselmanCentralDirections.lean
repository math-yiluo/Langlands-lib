import Langlands.Representation.Exponents.JacquetExponentRestriction
import Langlands.Representation.Exponents.NormalizedTemperedFullGroupProof
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Central directions in the represented-parabolic Casselman criterion

These internal lemmas establish the central-character restriction of each
normalized Jacquet exponent and the positive-cone clause for the identity
parabolic. They do not assert the proper-parabolic analytic criterion.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uG uV uB

section CentralScalars

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ]

/-- At an ambient central point of the actual Levi, the normalized Jacquet
quotient retains the prescribed central scalar. No inclusion of the entire
ambient center in the Levi is needed. -/
theorem normalizedJacquet_apply_of_unitaryCentralCharacter
    (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ)
    (c : UnitaryCentralCharacter π.representation) (m : L)
    (hm : (m : Γ) ∈ Subgroup.center Γ)
    (v : (normalizedJacquetFunctor N L hN hLN).obj π) :
    ((normalizedJacquetFunctor N L hN hLN).obj π).representation m v =
      (c.character ⟨m, hm⟩ : ℂ) • v := by
  obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective π.representation N 1 v
  rw [normalizedJacquetFunctor_obj_apply_of_mem_center N L hN hLN π m hm]
  have hw := c.acts ⟨m, hm⟩ w
  rw [hw, map_smul]
  rfl

/-- A normalized Jacquet generalized eigencharacter agrees with the original
central character at every point whose actual ambient image is central. -/
theorem normalizedJacquet_generalizedEigencharacter_apply_eq_centralCharacter
    {B : Type uB} [Group B]
    (N L : Subgroup Γ) (hN : IsClosed (N : Set Γ))
    (hLN : L ≤ Subgroup.normalizer (N : Set Γ))
    (π : SmoothRep.{0, uG, uV} ℂ Γ)
    (c : UnitaryCentralCharacter π.representation)
    (z : B →* L) (χ : B →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter
      (((normalizedJacquetFunctor N L hN hLN).obj π).representation.comp z) χ)
    (b : B) (hb : (z b : Γ) ∈ Subgroup.center Γ) :
    χ b = c.character ⟨z b, hb⟩ := by
  obtain ⟨d, v, hv, hd⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  have hscalar :
      ((normalizedJacquetFunctor N L hN hLN).obj π).representation (z b) =
        (c.character ⟨z b, hb⟩ : ℂ) • 1 := by
    ext w
    exact normalizedJacquet_apply_of_unitaryCentralCharacter N L hN hLN π c (z b) hb w
  have hpow := hd b
  change (((((normalizedJacquetFunctor N L hN hLN).obj π).representation (z b) -
    (χ b : ℂ) • 1) ^ d) v) = 0 at hpow
  have hzero : ((c.character ⟨z b, hb⟩ : ℂ) - (χ b : ℂ)) ^ d • v = 0 := by
    simpa only [hscalar, ← sub_smul, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply] using hpow
  apply Units.ext
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero
    ((smul_eq_zero.mp hzero).resolve_right hv))).symm

end CentralScalars

namespace RepresentedParabolic

open GroupScheme

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance casselmanCentralAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- The central-value comparison for every actual represented-parabolic
normalized exponent, without Jacquet admissibility or geometric existence inputs. -/
theorem normalizedJacquetExponent_apply_eq_centralCharacter
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (t : rationalPoints A.toGrp)
    (ht : (splitComponentPointsMap (l ≫ p) a t : rationalPoints G) ∈
      Subgroup.center (rationalPoints G)) :
    χ t = c.character ⟨splitComponentPointsMap (l ≫ p) a t, ht⟩ := by
  exact normalizedJacquet_generalizedEigencharacter_apply_eq_centralCharacter
    (pointImage (r ≫ p)) (pointImage (l ≫ p))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) π c (splitComponentPointsMap (l ≫ p) a) χ
    ((isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ) t ht

/-- Such an exponent is unitary at every split-component point mapping to the
ambient point center. -/
theorem normalizedJacquetExponent_norm_eq_one_of_mem_center
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (t : rationalPoints A.toGrp)
    (ht : (splitComponentPointsMap (l ≫ p) a t : rationalPoints G) ∈
      Subgroup.center (rationalPoints G)) :
    ‖(χ t : ℂ)‖ = 1 := by
  rw [normalizedJacquetExponent_apply_eq_centralCharacter
    p l r hp hl hr hmul ha π c χ hχ t ht]
  exact c.norm_eq_one _

section LocalField

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- The normalized real part of an exponent vanishes on every split torus
whose specified morphism through the Levi component is ambient central. -/
theorem normalizedJacquetExponent_realPart_restrict_eq_zero
    (ha : IsSplitComponent a)
    {B : CommGroupScheme (Spec (CommRingCat.of k))}
    (hB : IsSplitTorus B.toGrp) (f : B ⟶ A)
    (hf : IsCentral (CommGroupScheme.groupHom f ≫ a ≫ l ≫ p))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      (Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ) = 0 := by
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  rw [← Plancherel.SplitTorus.normalizedRealPart_comp_points
    hB ha.isCentralSplitTorus.1.1 f χ hχ.1]
  apply Plancherel.SplitTorus.normalizedRealPart_unique hB _ 0
  intro t
  have ht : (splitComponentPointsMap (l ≫ p) a
      (rationalPoints.map (CommGroupScheme.groupHom f) t) : rationalPoints G) ∈
        Subgroup.center (rationalPoints G) := hf.map_mem_center t
  simpa using normalizedJacquetExponent_norm_eq_one_of_mem_center
    p l r hp hl hr hmul ha π c χ hχ
      (rationalPoints.map (CommGroupScheme.groupHom f) t) ht

end LocalField

end RepresentedParabolic
end Langlands.Aubert.General

namespace Langlands.GroupScheme.ParabolicRootPresentation

universe u

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}

/-- Every positive root combination for the identity parabolic is zero; taking
all coefficients equal to one also gives the converse, including the empty case. -/
theorem positiveCone_identity
    (pres : ParabolicRootPresentation (𝟙 G) (𝟙 G) a) : pres.positiveCone = {0} := by
  ext x
  constructor
  · intro hx
    have hn := pres.positiveCone_subset_nonnegCone hx
    simpa only [pres.nonnegCone_identity] using hn
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    change ∃ c : RealTorusSpace.Vstar A → ℝ,
      (∀ β ∈ pres.restrictedRoots, 0 < c β) ∧
        ∑ β ∈ pres.finite_restrictedRoots.toFinset, c β • β = 0
    refine ⟨fun _ => 1, fun _ _ => zero_lt_one, ?_⟩
    apply Finset.sum_eq_zero
    intro β hβ
    rw [pres.restrictedRoot_eq_zero_identity
      (pres.finite_restrictedRoots.mem_toFinset.mp hβ), smul_zero]

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance casselmanIdentityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Every exponent of the full-group normalized Jacquet module has zero
normalized real part under the original unitary central character hypothesis. -/
theorem unitaryCentralCharacter_identityJacquetExponent_realPart_eq_zero
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (ha : IsSplitComponent a)
    (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
    {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ G)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication (𝟙 G) r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 := by
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  apply (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff
    ha.isCentralSplitTorus.1.1 χ hχ.1).mpr
  intro t
  apply normalizedJacquetExponent_norm_eq_one_of_mem_center
    (𝟙 G) (𝟙 G) r hp hl hr hmul ha π c χ hχ t
  exact ha.isCentralSplitTorus.isCentral.map_mem_center t

/-- The identity-parabolic positive-cone clause of Casselman's criterion follows
from the original unitary central character datum alone. -/
theorem unitaryCentralCharacter_identityJacquetExponent_mem_positiveCone
    (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (ha : IsSplitComponent a)
    (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
    {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ G)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication (𝟙 G) r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (pres : ParabolicRootPresentation (𝟙 G) (𝟙 G) a)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ) :
    haveI := hG.smooth
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone := by
  have := hG.smooth
  rw [pres.positiveCone_identity, Set.mem_singleton_iff]
  exact unitaryCentralCharacter_identityJacquetExponent_realPart_eq_zero
    ha hp hl r hr hmul π c χ hχ

/-- The full identity-parabolic cone clause, with the field and representation
universes inherited from the represented-parabolic criterion. -/
def IdentityParabolicCasselmanConeStatement : Prop :=
  ∀ (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ G}
    (ha : IsSplitComponent a)
    (hp : IsParabolicSubgroup (𝟙 G)) (hl : IsRationalLeviSubgroup (𝟙 G))
    {U : GroupScheme (Spec (CommRingCat.of k))} (r : U ⟶ G)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication (𝟙 G) r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (_c : UnitaryCentralCharacter π.representation)
    (pres : ParabolicRootPresentation (𝟙 G) (𝟙 G) a)
    (χ : rationalPoints A.toGrp →* ℂˣ),
    IsNormalizedJacquetExponent (𝟙 G) (𝟙 G) r hp hl hr hmul ha π χ →
      haveI := hG.smooth
      Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
        pres.positiveCone

/-- The identity-parabolic clause follows from the original unitary central
character, independently of either proper-parabolic analytic implication. -/
theorem identityParabolicCasselmanCone :
    IdentityParabolicCasselmanConeStatement.{u, v} (G := G) := by
  intro hG A a ha hp hl U r hr hmul π c pres χ hχ
  exact unitaryCentralCharacter_identityJacquetExponent_mem_positiveCone
    hG ha hp hl r hr hmul π c pres χ hχ

end Langlands.Aubert.General.RepresentedParabolic
