import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics
import Langlands.Representation.Aubert.General.SemidirectRestriction
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Langlands.Representation.Aubert.General.RationalIwasawaCartan

/-! # Factorization of `δ₀` along a standard parabolic subgroup

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and a standard parabolic `P_J = M_J U_J`, the actual minimal radical
decomposes as `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)`, and the Haar modulus `δ₀` of conjugation on
`U₀(F)` factors on `P₀(F) ∩ M_J(F)` as `δ₀ = δ₀^{M_J} δ_{U_J}`, where `δ₀^{M_J}` is the Haar
modulus of conjugation on `M_J(F) ∩ U₀(F)` (Waldspurger's `δ_0^M` for `M = M_J`) and `δ_{U_J}` the
Haar modulus of conjugation on `U_J(F)`. On elements central in `M_J(F)`, `δ₀ = δ_{U_J}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Decomposition

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For a connected reductive `G`, a maximal split torus, a generic cocharacter `ν` and a set `J` of
simple relative roots, the actual standard parabolic is `P_J(F) = M_J(F) ⋉ U_J(F)`: by the Library's
`standardCocharacter`, `P_J, M_J, U_J` are the dynamic subgroups of a standard cocharacter for
`J`, whose decomposition is `dynamic_isSemidirectDecomposition`. -/
theorem isSemidirectDecomposition_standard (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν J)
      (standardLeviPoints i ν J) (standardUnipotentPoints i ν J) := by
  have := hG.isSeparated
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  change Aubert.General.IsSemidirectDecomposition
    ((standardParabolic i ν J).carrier (Over.mk (𝟙 _)))
    ((standardLevi i ν J).carrier (Over.mk (𝟙 _)))
    ((standardUnipotent i ν J).carrier (Over.mk (𝟙 _)))
  rw [hP, hM, hU]
  exact Aubert.General.dynamic_isSemidirectDecomposition _ _

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The Levi projection of every decomposition `P_J(F) = M_J(F) ⋉ U_J(F)` is continuous: it is the
dynamic limit map of a standard cocharacter (`continuous_dynamic_projection`). -/
theorem continuous_projection_standard (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (h : Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν J)
      (standardLeviPoints i ν J) (standardUnipotentPoints i ν J)) :
    Continuous h.projection := by
  have := hG.isSeparated
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨hP, hM, hU⟩ := hcompare ζ hζ
  have hc := Aubert.General.continuous_dynamic_projection F G (CommGroupScheme.groupHom ζ ≫ i)
  have transport (P M U : Subgroup (rationalPoints G))
      (hP' : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier (Over.mk (𝟙 _)) = P)
      (hM' : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier (Over.mk (𝟙 _)) = M)
      (hU' : (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).carrier (Over.mk (𝟙 _)) = U)
      (h' : Aubert.General.IsSemidirectDecomposition P M U) : Continuous h'.projection := by
    subst hP' hM' hU'
    exact hc
  exact transport _ _ _ (by rw [← hP]) (by rw [← hM]) (by rw [← hU]) h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `P₀(F) ⊆ P_J(F)`: every relative root nonnegative on `ν` is nonnegative on a standard
cocharacter for `J` (`root_pairing_implications_of_subset`), so the proved root-sign comparison of
dynamic parabolic subgroups (`relativeRootSignInclusions`) applies. -/
theorem standardParabolicPoints_empty_le (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardParabolicPoints i ν ∅ ≤ standardParabolicPoints i ν J := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨hP, -, -⟩ := hcompare ζ hζ
  obtain ⟨-, hcompare₀⟩ := standardCocharacter F G hG S i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hP₀, -, -⟩ := hcompare₀ ν (isStandardCocharacter_empty_self i ν)
  have hneg := relativeRootNegation F G hG S i hi
  have hle := (relativeRootSignInclusions F G hG S i hi ν ζ).1.2 fun α hα h0 =>
    ((isStandardCocharacter_empty_self i ν).root_pairing_implications_of_subset i ν hν hneg hζ
      (Set.empty_subset J) hα).1 h0
  intro g hg
  have hg' : g ∈ (standardParabolic i ν ∅).carrier (Over.mk (𝟙 _)) := hg
  rw [hP₀] at hg'
  change g ∈ (standardParabolic i ν J).carrier (Over.mk (𝟙 _))
  rw [hP]
  exact hle _ hg'

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `U₀(F) ⊆ P_J(F)`. -/
theorem standardUnipotentPoints_empty_le_standardParabolicPoints (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardUnipotentPoints i ν ∅ ≤ standardParabolicPoints i ν J := fun _ hu =>
  standardParabolicPoints_empty_le hG hi hν hJ (standardUnipotent_le_standardParabolic i ν ∅ _ hu)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `U_J(F) ⊆ U₀(F)` for `J ⊆ Δ`. -/
theorem standardUnipotentPoints_le_empty_of_subset (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardUnipotentPoints i ν J ≤ standardUnipotentPoints i ν ∅ := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨⟨ζ, hζ⟩, -⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  exact BruhatTits.SpecialCompact.standardUnipotentPoints_le_empty hG hi hν hζ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **`U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)`**: the restriction of `P_J(F) = M_J(F) ⋉ U_J(F)` to
`U_J(F) ⊆ U₀(F) ⊆ P_J(F)` (`IsSemidirectDecomposition.restrict`). -/
theorem isSemidirectDecomposition_minimalUnipotent (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    Aubert.General.IsSemidirectDecomposition (standardUnipotentPoints i ν ∅)
      (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅)
      (standardUnipotentPoints i ν J) :=
  (isSemidirectDecomposition_standard hG hi hν hJ).restrict
    (standardUnipotentPoints_empty_le_standardParabolicPoints hG hi hν hJ)
    (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The projection of `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)` is continuous. -/
theorem continuous_projection_minimalUnipotent (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    Continuous (isSemidirectDecomposition_minimalUnipotent hG hi hν hJ).projection :=
  (isSemidirectDecomposition_standard hG hi hν hJ).continuous_restrict_projection
    (standardUnipotentPoints_empty_le_standardParabolicPoints hG hi hν hJ)
    (standardUnipotentPoints_le_empty_of_subset hG hi hν hJ)
    (continuous_projection_standard hG hi hν hJ _)

end Decomposition

section Modulus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

local instance rationalModulusSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- `P₀(F) ∩ M_J(F)` normalizes `M_J(F) ∩ U₀(F)`. -/
theorem standardParabolicLevi_le_normalizer :
    standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J ≤
      Subgroup.normalizer ((standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅ :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h₁ := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (Subgroup.mem_inf.mp hp).2) h
  have h₂ := Subgroup.mem_normalizer_iff.mp
    (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅
      (Subgroup.mem_inf.mp hp).1) h
  simp only [Subgroup.mem_inf] at h₁ h₂ ⊢
  exact and_congr h₁ h₂

/-- **Waldspurger's `δ_0^M` for `M = M_J`**: the Haar modulus of the conjugation action of the
minimal standard parabolic `P₀(F) ∩ M_J(F)` of `M_J(F)` on its radical `M_J(F) ∩ U₀(F)` (the
Library's `HaarModulus.closedRestrictCharacter` of this closed subgroup). -/
def standardLeviMinimalModulus :
    (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J : Subgroup (rationalPoints G)) →*
      ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter (standardLeviPoints i ν J ⊓ standardUnipotentPoints i ν ∅)
    ((isClosed_standardLeviPoints i ν J).inter (isClosed_standardUnipotentPoints i ν ∅))
    (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J)
    (standardParabolicLevi_le_normalizer i ν J)

/-- `δ_{U_J}` on `M_J(F)`: the Haar modulus of conjugation on `U_J(F)`. -/
def standardUnipotentModulus : standardLeviPoints i ν J →* ℝ≥0ˣ :=
  HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν J)
    (isClosed_standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)

variable {i ν J}

/-- **`δ₀ = δ₀^{M_J} δ_{U_J}` on `P₀(F) ∩ M_J(F)`**, for connected reductive `G`, a maximal split
torus, a generic cocharacter and `J ⊆ Δ`: the Haar moduli multiply along the continuous semidirect
decomposition `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)`, whose three factors are normalized by
`P₀(F) ∩ M_J(F)` (`IsSemidirectDecomposition.closedNormalizerCharacter_eq_mul`). -/
theorem rationalMinimalModulus_eq_mul (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (p : (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J :
      Subgroup (rationalPoints G))) :
    rationalMinimalModulus i ν ⟨p, (Subgroup.mem_inf.mp p.2).1⟩ =
      standardLeviMinimalModulus i ν J p *
        standardUnipotentModulus i ν J ⟨p, (Subgroup.mem_inf.mp p.2).2⟩ :=
  (isSemidirectDecomposition_minimalUnipotent hG hi hν hJ).closedNormalizerCharacter_eq_mul
    (continuous_projection_minimalUnipotent hG hi hν hJ)
    (isClosed_standardUnipotentPoints i ν ∅)
    ((isClosed_standardLeviPoints i ν J).inter (isClosed_standardUnipotentPoints i ν ∅))
    (isClosed_standardUnipotentPoints i ν J) (p : rationalPoints G)
    (standardParabolicPoints_le_normalizer_standardUnipotentPoints i ν ∅
      (Subgroup.mem_inf.mp p.2).1)
    (standardParabolicLevi_le_normalizer i ν J p.2)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J (Subgroup.mem_inf.mp p.2).2)

/-- The Haar modulus of conjugation by an element commuting with a closed subgroup is `1`. -/
theorem closedNormalizerCharacter_eq_one_of_commute (U : Subgroup (rationalPoints G))
    (hU : IsClosed (U : Set (rationalPoints G))) (g : Subgroup.normalizer (U : Set (rationalPoints G)))
    (hg : ∀ u ∈ U, (g : rationalPoints G) * u = u * g) :
    HaarModulus.closedNormalizerCharacter U hU g = 1 := by
  have he : HaarModulus.normalizerConj U g = ContinuousMulEquiv.refl U := by
    refine ContinuousMulEquiv.ext fun u => Subtype.ext ?_
    rw [HaarModulus.normalizerConj_apply, hg u u.2, mul_inv_cancel_right]
    rfl
  apply Units.ext
  simp only [HaarModulus.closedNormalizerCharacter, HaarModulus.normalizerCharacter_apply, he,
    MeasureTheory.mulEquivHaarChar_refl, Units.val_one]

/-- `δ₀^{M_J}(p) = 1` for `p ∈ P₀(F) ∩ M_J(F)` commuting with every element of `M_J(F)`. -/
theorem standardLeviMinimalModulus_eq_one_of_commute
    (p : (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J :
      Subgroup (rationalPoints G)))
    (hp : ∀ m ∈ standardLeviPoints i ν J, (p : rationalPoints G) * m = m * p) :
    standardLeviMinimalModulus i ν J p = 1 :=
  closedNormalizerCharacter_eq_one_of_commute _
    ((isClosed_standardLeviPoints i ν J).inter (isClosed_standardUnipotentPoints i ν ∅)) _
    fun u hu => hp u (Subgroup.mem_inf.mp hu).1

/-- **`δ₀ = δ_{U_J}` on elements central in `M_J(F)`**: for `p ∈ P₀(F) ∩ M_J(F)` commuting with
every element of `M_J(F)` (for example a point of a compatible split component of `M_J`),
`δ₀(p) = δ_{U_J}(p)`. -/
theorem rationalMinimalModulus_eq_standardUnipotentModulus_of_commute
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (p : (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J :
      Subgroup (rationalPoints G)))
    (hp : ∀ m ∈ standardLeviPoints i ν J, (p : rationalPoints G) * m = m * p) :
    rationalMinimalModulus i ν ⟨p, (Subgroup.mem_inf.mp p.2).1⟩ =
      standardUnipotentModulus i ν J ⟨p, (Subgroup.mem_inf.mp p.2).2⟩ := by
  rw [rationalMinimalModulus_eq_mul hG hi hν hJ p, standardLeviMinimalModulus_eq_one_of_commute p hp,
    one_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The points of the maximal split torus lie in `M₀(F)`. -/
theorem map_mem_standardLeviPoints_empty {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (q : A.toGrp ⟶ S.toGrp) (x : rationalPoints A.toGrp) :
    rationalPoints.map (q ≫ i) x ∈ standardLeviPoints i ν ∅ := by
  have h := Aubert.General.RationalPointFamily.torusPoints_le_levi i ν
    (∅ : Finset (Aubert.General.RationalPointFamily.SimpleRoot i ν))
    ((Aubert.General.RationalPointFamily.mem_torusPoints i (rationalPoints.map (q ≫ i) x)).mpr
      ⟨rationalPoints.map q x, by
        simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]⟩)
  simpa [Aubert.General.RationalPointFamily.levi] using h

/-- **`δ₀ = δ_{U_J}` on a compatible split component of `M_J`**: for every point `a` of the image
of `A(F)`, `δ₀(a) = δ_{U_J}(a)`. -/
theorem rationalMinimalModulus_eq_standardUnipotentModulus_splitComponent
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : BruhatTits.SpecialCompact.IsCompatibleStandardSplitComponent i ν J A q)
    (x : rationalPoints A.toGrp) :
    rationalMinimalModulus i ν ⟨rationalPoints.map (q ≫ i) x,
        standardLevi_le_standardParabolic i ν ∅ _ (map_mem_standardLeviPoints_empty (i := i) (ν := ν) q x)⟩ =
      standardUnipotentModulus i ν J
        ⟨rationalPoints.map (q ≫ i) x, hA.map_mem_standardLeviPoints i ν x⟩ :=
  rationalMinimalModulus_eq_standardUnipotentModulus_of_commute hG hi hν hJ
    ⟨rationalPoints.map (q ≫ i) x, Subgroup.mem_inf.mpr
      ⟨standardLevi_le_standardParabolic i ν ∅ _ (map_mem_standardLeviPoints_empty (i := i) (ν := ν) q x),
        hA.map_mem_standardLeviPoints i ν x⟩⟩
    fun _ hm => (hA.map_commute x hm).symm

end Modulus

end Langlands.HarishChandraSchwartz
