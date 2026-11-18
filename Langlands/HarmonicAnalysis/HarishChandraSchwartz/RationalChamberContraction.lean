import Langlands.GroupScheme.MatrixRepresentation.TorusCharacterDiagonalization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalChamber
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Geometry.Building.CocharacterUniformizerProof

/-! # Uniform conjugation height bounds on the actual minimal parabolic -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan

namespace Langlands.HarishChandraSchwartz

section Matrix

variable {F : Type*} [NormedField F] {n : Type} [Fintype n]
  [DecidableEq n] [Nonempty n]

/-- Conjugation by a contracting diagonal cocharacter does not increase the
matrix norm on its block parabolic. -/
theorem glNorm_conj_le_of_mem_blockParabolic (e : n → ℤ) (t : Fˣ)
    (ht : ‖(t : F)‖ ≤ 1) {p : GL n F} (hp : p ∈ blockParabolicSubgroup F e) :
    glNorm (diagonalUnits F e t * p * (diagonalUnits F e t)⁻¹) ≤ glNorm p := by
  have hentry : ∀ q ∈ blockParabolicSubgroup F e, ∀ r s,
      ‖((diagonalUnits F e t * q * (diagonalUnits F e t)⁻¹ : GL n F) :
        Matrix n n F) r s‖ ≤ ‖(q : Matrix n n F) r s‖ := by
    intro q hq r s
    have he := diagonalUnits_conj_apply e t⁻¹ q r s
    simp only [map_inv, inv_inv] at he
    rw [he]
    by_cases hlt : e r < e s
    · rw [(mem_blockParabolicSubgroup F e).mp hq r s hlt, mul_zero]
    · rw [norm_mul, norm_zpow]
      apply mul_le_of_le_one_left (norm_nonneg _)
      have ht' : 1 ≤ ‖((t⁻¹ : Fˣ) : F)‖ := by
        rw [Units.val_inv_eq_inv_val, norm_inv]
        exact (one_le_inv₀ (norm_pos_iff.mpr t.ne_zero)).mpr ht
      exact zpow_le_one_of_nonpos₀ ht' (by omega)
  apply glNorm_le
  · intro r s
    exact (hentry p hp r s).trans (norm_le_glNorm p r s)
  · intro r s
    rw [show (diagonalUnits F e t * p * (diagonalUnits F e t)⁻¹)⁻¹ =
      diagonalUnits F e t * p⁻¹ * (diagonalUnits F e t)⁻¹ by group]
    exact (hentry p⁻¹ ((blockParabolicSubgroup F e).inv_mem hp) r s).trans
      (norm_inv_le_glNorm p r s)

end Matrix

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Every cocharacter in the closed minimal chamber has a dynamic
parabolic containing the actual minimal standard parabolic. -/
theorem standardParabolic_empty_le_of_simpleRootPairings_nonneg
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (c : cocharacterLattice S)
    (hc : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S β c) :
    standardParabolic i ν ∅ ≤ Dynamic.parabolic (CommGroupScheme.groupHom c ≫ i) := by
  have := hi.isSplitSubtorus.mono
  let J : Set (characterLattice S) :=
    {β | β ∈ simpleRelativeRoots i ν ∧ latticePairing S β c = 0}
  have hJ : J ⊆ simpleRelativeRoots i ν := fun _ hβ => hβ.1
  have hstd : IsStandardCocharacter i ν J c := by
    refine ⟨hJ, fun _ hβ => hβ.2, ?_⟩
    intro β hβ hβJ
    have hne : latticePairing S β c ≠ 0 := fun he => hβJ ⟨hβ, he⟩
    exact lt_of_le_of_ne (hc β hβ) (Ne.symm hne)
  have he := ((standardCocharacter F G hG S i hi ν hν J hJ).2 c hstd).1
  rw [← he]
  exact ((standardParabolicOrder F G hG S i hi ν hν).1 ∅ J
    (Set.empty_subset _) hJ).1.mp (Set.empty_subset _)

omit [LocallyOfFiniteType G.X.hom] in
/-- Once the whole torus is diagonal in fixed coordinates, every dominant
uniformizer-section point contracts the actual minimal parabolic in norm. -/
theorem rationalMatrixNorm_conj_latticeSection_le
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) {χ : n → rationalCharacters S.toGrp}
    (hdiag : ρ.HasTorusCharacterDiagonal i χ)
    (c : cocharacterLattice S)
    (hc : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S β c)
    (p : rationalPoints G) (hp : p ∈ standardParabolicPoints i ν ∅) :
    MatrixRepresentation.rationalMatrixNorm F ρ
      (rationalPoints.map i (CocharacterUniformizer.latticeSection F S (.ofAdd c)) *
        p * (rationalPoints.map i
          (CocharacterUniformizer.latticeSection F S (.ofAdd c)))⁻¹) ≤
      MatrixRepresentation.rationalMatrixNorm F ρ p := by
  let χc := CommGroupScheme.groupHom c ≫ i
  let e : n → ℤ := fun j =>
    latticePairing S ((rationalCharacters.equivCharacterLattice S) (χ j)) c
  have hχc : χc ≫ ρ = diagonalCocharacter n (CommRingCat.of F) e :=
    (Category.assoc _ _ _).trans (hdiag.cocharacter c)
  have hpc : p ∈ (Dynamic.parabolic χc).rationalPoints :=
    standardParabolic_empty_le_of_simpleRootPairings_nonneg hG hi hν c hc _ hp
  have hblock : ρ.rationalMatrix p ∈ blockParabolicSubgroup F e := by
    rw [MatrixRepresentation.rationalMatrix_mem_blockParabolicSubgroup_iff]
    have hmap := Dynamic.parabolic_le_comap χc ρ _ hpc
    rw [SubgroupFunctor.mem_comap, hχc, parabolic_diagonalCocharacter] at hmap
    exact hmap
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have ht : ‖(SplitTorusValuation.uniformizerUnit F : F)‖ ≤ 1 := by
    change LocalField.residueNormalizedAbsoluteValue F (LocalField.uniformizer F) ≤ 1
    rw [LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)]
    have hq : (1 : ℝ) < LocalField.residueCardinality F := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    exact (inv_lt_one_of_one_lt₀ hq).le
  change glNorm (ρ.rationalMatrix _) ≤ glNorm (ρ.rationalMatrix p)
  rw [map_mul, map_mul, map_inv, hdiag.latticeSection c]
  exact glNorm_conj_le_of_mem_blockParabolic e _ ht hblock

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A fixed rational change of matrix coordinates changes the logarithmic
height by a uniformly bounded additive amount, in both directions. -/
theorem exists_rationalHeight_conjugate_compare
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n)
    (q : rationalPoints (groupScheme n (CommRingCat.of F))) :
    ∃ D ≥ 0, ∀ g : rationalPoints G,
      rationalHeight (F := F) (ρ.conjugate q) g ≤ D + rationalHeight (F := F) ρ g ∧
      rationalHeight (F := F) ρ g ≤ D + rationalHeight (F := F) (ρ.conjugate q) g := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have : IsUltrametricDist F :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (LocalField.residueNormalizedAbsoluteValue_add_le_max F)
  let Q := MatrixRepresentation.rationalMatrix (𝟙 (groupScheme n (CommRingCat.of F))) q
  let tauId : GL n F →* GL n F := MonoidHom.id _
  have hQ := height_nonneg tauId Q
  refine ⟨2 * height tauId Q, by positivity, fun g => ?_⟩
  have he : (ρ.conjugate q).rationalMatrix g = Q * ρ.rationalMatrix g * Q⁻¹ :=
    MatrixRepresentation.rationalMatrix_comp_innerIso ρ q g
  have he' : ρ.rationalMatrix g = Q⁻¹ * (ρ.conjugate q).rationalMatrix g * Q := by
    rw [he]
    group
  constructor
  · change height tauId ((ρ.conjugate q).rationalMatrix g) ≤
      2 * height tauId Q + height tauId (ρ.rationalMatrix g)
    rw [he]
    have h₁ := height_mul_le tauId (Q * ρ.rationalMatrix g) Q⁻¹
    have h₂ := height_mul_le tauId Q (ρ.rationalMatrix g)
    rw [height_inv] at h₁
    linarith
  · change height tauId (ρ.rationalMatrix g) ≤
      2 * height tauId Q + height tauId ((ρ.conjugate q).rationalMatrix g)
    rw [he']
    have h₁ := height_mul_le tauId (Q⁻¹ * (ρ.conjugate q).rationalMatrix g) Q
    have h₂ := height_mul_le tauId Q⁻¹ ((ρ.conjugate q).rationalMatrix g)
    rw [height_inv] at h₂
    linarith

/-- The compact torus norm kernel extends the section contraction to every
actual chamber point, in fixed torus-diagonal matrix coordinates. -/
theorem exists_rationalHeight_conj_le_of_torusDiagonal
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) {χ : n → rationalCharacters S.toGrp}
    (hdiag : ρ.HasTorusCharacterDiagonal i χ) :
    ∃ B ≥ 0, ∀ a : rationalPoints S.toGrp,
      (∀ β ∈ simpleRelativeRoots i ν, 0 ≤ RenardLeviCones.characterOrder S β a) →
      ∀ p ∈ standardParabolicPoints i ν ∅,
        rationalHeight (F := F) ρ
          (rationalPoints.map i a * p * (rationalPoints.map i a)⁻¹) ≤
            B + rationalHeight (F := F) ρ p := by
  let : IsAffineHom S.X.hom := hi.isSplitSubtorus.1.isAffineHom
  let Kt : Subgroup (rationalPoints G) :=
    (Langlands.Plancherel.rationalCommonNormKernel S.toGrp).map (rationalPoints.map i)
  have hKt : IsCompact (Kt : Set (rationalPoints G)) := by
    change IsCompact (rationalPoints.map i ''
      (Langlands.Plancherel.rationalCommonNormKernel S.toGrp : Set (rationalPoints S.toGrp)))
    exact (Langlands.Plancherel.SplitTorus.isCompact_commonNormKernel
      hi.isSplitSubtorus.1).image (continuous_rationalPointMap F i.hom.hom)
  obtain ⟨D, hD⟩ := hKt.bddAbove_image (continuous_rationalHeight ρ).continuousOn
  refine ⟨2 * max D 0, by positivity, fun a ha p hp => ?_⟩
  obtain ⟨c, hc, _⟩ :=
    (CocharacterUniformizer.isUniformizerLatticeSection F S hi.isSplitSubtorus.1).2.2 a
  have hval := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff F S a c).mp hc
  have hdom : ∀ β ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S β c.toAdd := by
    intro β hβ
    rw [← hval β]
    exact ha β hβ
  let s := rationalPoints.map i (CocharacterUniformizer.latticeSection F S c)
  let k := rationalPoints.map i (a * (CocharacterUniformizer.latticeSection F S c)⁻¹)
  have hk : k ∈ Kt := ⟨_, hc, rfl⟩
  have hks : rationalPoints.map i a = k * s := by
    dsimp only [k, s]
    rw [map_mul, map_inv]
    group
  have hconj : rationalPoints.map i a * p * (rationalPoints.map i a)⁻¹ =
      k * (s * p * s⁻¹) * k⁻¹ := by
    rw [hks]
    group
  have hs : rationalHeight (F := F) ρ (s * p * s⁻¹) ≤ rationalHeight (F := F) ρ p :=
    Real.log_le_log (rationalMatrixNorm_pos ρ _)
      (rationalMatrixNorm_conj_latticeSection_le hG hi hν ρ hdiag c.toAdd hdom p hp)
  have hkD : rationalHeight (F := F) ρ k ≤ max D 0 :=
    (hD (Set.mem_image_of_mem _ hk)).trans (le_max_left _ _)
  rw [hconj]
  have h₁ := rationalHeight_mul_le ρ (k * (s * p * s⁻¹)) k⁻¹
  have h₂ := rationalHeight_mul_le ρ k (s * p * s⁻¹)
  rw [rationalHeight_inv] at h₁
  linarith

/-- The actual minimal-parabolic conjugation height bound, for every
original matrix realization and every point of the full torus chamber. -/
theorem exists_rationalHeight_conj_le_on_minimalParabolic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ B ≥ 0, ∀ a : rationalPoints S.toGrp,
      (∀ β ∈ simpleRelativeRoots i ν, 0 ≤ RenardLeviCones.characterOrder S β a) →
      ∀ p ∈ standardParabolicPoints i ν ∅,
        rationalHeight (F := F) ρ
          (rationalPoints.map i a * p * (rationalPoints.map i a)⁻¹) ≤
            B + rationalHeight (F := F) ρ p := by
  obtain ⟨q, χ, hdiag⟩ :=
    MatrixRepresentation.exists_hasTorusCharacterDiagonal ρ i hi.isSplitSubtorus.1
  obtain ⟨D, hD, hcomp⟩ := exists_rationalHeight_conjugate_compare ρ q
  obtain ⟨B, hB, hb⟩ := exists_rationalHeight_conj_le_of_torusDiagonal hG hi hν
    (ρ.conjugate q) hdiag
  refine ⟨2 * D + B, by positivity, fun a ha p hp => ?_⟩
  have h₁ := (hcomp (rationalPoints.map i a * p * (rationalPoints.map i a)⁻¹)).2
  have h₂ := hb a ha p hp
  have h₃ := (hcomp p).1
  linarith

/-- Waldspurger II.3.3 with a positive constant, for arbitrary finite
matrix realizations and all actual chamber points. -/
theorem exists_one_add_rationalHeight_conj_le_on_minimalParabolic
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C ≥ 1, ∀ a : rationalPoints S.toGrp,
      (∀ β ∈ simpleRelativeRoots i ν, 0 ≤ RenardLeviCones.characterOrder S β a) →
      ∀ p ∈ standardParabolicPoints i ν ∅,
        1 + rationalHeight (F := F) ρ
          (rationalPoints.map i a * p * (rationalPoints.map i a)⁻¹) ≤
            C * (1 + rationalHeight (F := F) ρ p) := by
  obtain ⟨B, hB, hb⟩ := exists_rationalHeight_conj_le_on_minimalParabolic hG hi hν ρ
  refine ⟨1 + B, by linarith, fun a ha p hp => ?_⟩
  have h := hb a ha p hp
  have hσ := rationalHeight_nonneg ρ p
  nlinarith

/-- The same bound on the full ambient chamber, without choosing torus
parameters in the conclusion. -/
theorem exists_one_add_rationalHeight_conj_le_on_chamber
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) :
    ∃ C ≥ 1, ∀ a ∈ rationalMinimalChamber i ν,
      ∀ p ∈ standardParabolicPoints i ν ∅,
        1 + rationalHeight (F := F) ρ (a * p * a⁻¹) ≤
          C * (1 + rationalHeight (F := F) ρ p) := by
  obtain ⟨C, hC, hb⟩ := exists_one_add_rationalHeight_conj_le_on_minimalParabolic hG hi hν ρ
  refine ⟨C, hC, ?_⟩
  intro a ha p hp
  obtain ⟨s, rfl, hs⟩ := (mem_rationalMinimalChamber_iff_order i ν a).mp ha
  exact hb s hs p hp

end Rational

/-- Closed actual-point form of Waldspurger II.3.3. Neither compact
adaptation nor closedness of the finite matrix representation is needed. -/
def RationalMinimalParabolicConjugationHeightStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
      ∃ C ≥ 1, ∀ a ∈ rationalMinimalChamber i ν,
        ∀ p ∈ standardParabolicPoints i ν ∅,
          1 + rationalHeight (F := F) ρ (a * p * a⁻¹) ≤
            C * (1 + rationalHeight (F := F) ρ p)

/-- The closed contraction-height statement holds in arbitrary field universe. -/
theorem rationalMinimalParabolicConjugationHeight :
    RationalMinimalParabolicConjugationHeightStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν N _ ρ
  exact exists_one_add_rationalHeight_conj_le_on_chamber hG hi hν ρ

end Langlands.HarishChandraSchwartz
