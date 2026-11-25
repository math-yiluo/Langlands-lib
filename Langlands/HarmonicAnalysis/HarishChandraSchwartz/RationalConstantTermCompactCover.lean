import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermCompactCover
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay

/-! # Compact Cartan reduction for actual constant-term kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

private local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {K : Subgroup (rationalPoints G)}
  (hKo : IsOpen (K : Set (rationalPoints G))) (hKc : IsCompact (K : Set (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

local instance : SecondCountableTopology (standardLeviPoints i ν J) :=
  TopologicalSpace.Subtype.secondCountableTopology _

include hKo in
/-- Every actual ambient decay kernel has uniformly bounded translations on
an arbitrary compact subgroup, even when that subgroup does not preserve `Ξ` or `σ`. -/
theorem exists_rationalXi_kernel_compact_mul
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {K0 : Subgroup (rationalPoints G)} (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    (r : ℝ) :
    ∃ C : ℝ≥0, ∀ k₁ ∈ K0, ∀ k₂ ∈ K0, ∀ g : rationalPoints G,
      rationalXi hKc hPK (k₁ * g * k₂) *
          (1 + rationalHeight (F := F) ρ (k₁ * g * k₂)) ^ r ≤
        C * (rationalXi hKc hPK g * (1 + rationalHeight (F := F) ρ g) ^ r) := by
  let H := K ⊓ rationalHeightSubgroup (F := F) ρ
  let f : rationalPoints G → ℝ := fun g =>
    rationalXi hKc hPK g * (1 + rationalHeight (F := F) ρ g) ^ r
  have hF : UniformTranslationBound f :=
    (rationalXi_uniformTranslationBound hKo hKc hPK).mul_one_add_rpow
      (fun g => (rationalXi_pos hKo hKc hPK g).le)
      (rationalHeight_nonneg ρ) (rationalHeight_inv ρ) (rationalHeight_mul_le ρ) r
  have hf0 (g : rationalPoints G) : 0 ≤ f g :=
    mul_nonneg (rationalXi_pos hKo hKc hPK g).le
      (Real.rpow_nonneg (by linarith [rationalHeight_nonneg (F := F) ρ g]) _)
  have hHo : IsOpen (H : Set (rationalPoints G)) :=
    hKo.inter (isOpen_rationalHeightSubgroup ρ)
  have hbi (k₁ : rationalPoints G) (hk₁ : k₁ ∈ H)
      (k₂ : rationalPoints G) (hk₂ : k₂ ∈ H) (g : rationalPoints G) :
      f (k₁ * g * k₂) = f g := by
    dsimp [f]
    rw [rationalXi_mul_mul hKo hKc hPK hk₁.1 hk₂.1,
      rationalHeight_mul_mul ρ hk₁.2 hk₂.2]
  exact hF.exists_uniform_mul hf0 hHo
    (fun k hk g => by simpa only [mul_one] using hbi k hk 1 H.one_mem g)
    (fun k hk g => by simpa only [one_mul] using hbi 1 H.one_mem k hk g) hK0c

include hKo in
/-- Translation bound for the actual standard Levi spherical function. -/
theorem rationalLeviXi_uniformTranslationBound (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J))) :
    UniformTranslationBound (rationalLeviXi hKc hM) := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  exact xi_uniformTranslationBound
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    (hKo.preimage continuous_subtype_val)

include hKo in
/-- The same compact translation bound for actual Levi decay kernels. -/
theorem exists_rationalLeviXi_kernel_compact_mul (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    {KM : Subgroup (standardLeviPoints i ν J)}
    (hKMc : IsCompact (KM : Set (standardLeviPoints i ν J))) (r : ℝ) :
    ∃ C : ℝ≥0, ∀ k₁ ∈ KM, ∀ k₂ ∈ KM, ∀ m : standardLeviPoints i ν J,
      rationalLeviXi hKc hM (k₁ * m * k₂) *
          (1 + rationalHeight (F := F) ρ ((k₁ * m * k₂ : standardLeviPoints i ν J) :
            rationalPoints G)) ^ r ≤
        C * (rationalLeviXi hKc hM m * (1 + rationalHeight (F := F) ρ m) ^ r) := by
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  let H := (K ⊓ rationalHeightSubgroup (F := F) ρ).subgroupOf (standardLeviPoints i ν J)
  let f : standardLeviPoints i ν J → ℝ := fun m =>
    rationalLeviXi hKc hM m * (1 + rationalHeight (F := F) ρ m) ^ r
  have hF : UniformTranslationBound f :=
    (rationalLeviXi_uniformTranslationBound hKo hKc hG hi hν hJ hM).mul_one_add_rpow
      (fun m => (rationalLeviXi_pos hKo hKc hG hi hν hJ hM m).le)
      (fun m => rationalHeight_nonneg ρ m) (fun m => rationalHeight_inv ρ (m : rationalPoints G))
      (fun m n => rationalHeight_mul_le ρ (m : rationalPoints G) (n : rationalPoints G)) r
  have hf0 (m : standardLeviPoints i ν J) : 0 ≤ f m :=
    mul_nonneg (rationalLeviXi_pos hKo hKc hG hi hν hJ hM m).le
      (Real.rpow_nonneg (by linarith [rationalHeight_nonneg (F := F) ρ m]) _)
  have hHo : IsOpen (H : Set (standardLeviPoints i ν J)) :=
    (hKo.inter (isOpen_rationalHeightSubgroup ρ)).preimage continuous_subtype_val
  have hbi (k₁ : standardLeviPoints i ν J) (hk₁ : k₁ ∈ H)
      (k₂ : standardLeviPoints i ν J) (hk₂ : k₂ ∈ H) (m : standardLeviPoints i ν J) :
      f (k₁ * m * k₂) = f m := by
    have hXi : rationalLeviXi hKc hM (k₁ * m * k₂) = rationalLeviXi hKc hM m :=
      xi_mul_mul (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
        hk₁.1 hk₂.1 m
    have hheight : rationalHeight (F := F) ρ
        ((k₁ : rationalPoints G) * (m : rationalPoints G) * (k₂ : rationalPoints G)) =
        rationalHeight (F := F) ρ (m : rationalPoints G) :=
      rationalHeight_mul_mul ρ hk₁.2 hk₂.2 _
    dsimp [f]
    rw [hXi, hheight]
  exact hF.exists_uniform_mul hf0 hHo
    (fun k hk m => by simpa only [mul_one] using hbi k hk 1 H.one_mem m)
    (fun k hk m => by simpa only [one_mul] using hbi 1 H.one_mem k hk m) hKMc

/-- Actual Levi Cartan representatives from a finite family of centralizer points
and the full split-torus chamber of the Levi roots. -/
def rationalLeviCartanRepresentatives (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) (F0 : Finset (centralizerPoints i)) :
    Set (standardLeviPoints i ν J) :=
  {m | ∃ f ∈ F0, ∃ a : rationalPoints S.toGrp,
    a ∈ CocharacterUniformizer.CAplus F S J ∧
      (m : rationalPoints G) = (f : rationalPoints G) * rationalPoints.map i a}

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual Levi Cartan covering gives a literal subgroup double-coset cover. -/
theorem isDoubleCosetCover_rationalLeviCartanRepresentatives
    {K0 : Subgroup (rationalPoints G)} (hcover : StandardLeviCartanCovering F i ν J K0) :
    ∃ F0 : Finset (centralizerPoints i),
      IsDoubleCosetCover (K0.subgroupOf (standardLeviPoints i ν J))
        (rationalLeviCartanRepresentatives i ν J F0) := by
  obtain ⟨F0, hF0⟩ := hcover
  refine ⟨F0, fun m => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hm⟩ := hF0 m m.2
  let l : standardLeviPoints i ν J := ⟨k₁, hk₁.2⟩
  let r : standardLeviPoints i ν J := ⟨k₂, hk₂.2⟩
  let s := l⁻¹ * m * r⁻¹
  refine ⟨l, hk₁.1, s, ⟨f, hf, a, ha, ?_⟩, r, hk₂.1, ?_⟩
  · change k₁⁻¹ * (m : rationalPoints G) * k₂⁻¹ = _
    rw [hm]
    group
  · dsimp [s]
    group

include hKo in
/-- Extend actual representative estimates using the structural compact subgroup,
with no invariance requirement for that subgroup. -/
theorem rationalConstantTermEstimate_of_compact_doubleCosetCover
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    {K0 : Subgroup (rationalPoints G)}
    (hK0o : IsOpen (K0 : Set (rationalPoints G)))
    (hK0c : IsCompact (K0 : Set (rationalPoints G)))
    {T : Set (standardLeviPoints i ν J)}
    (hcover : IsDoubleCosetCover (K0.subgroupOf (standardLeviPoints i ν J)) T)
    (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure]
    (hT : ∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ m ∈ T,
      (NNReal.sqrt (standardUnipotentModulus i ν J m) : ℝ≥0∞) *
          ∫⁻ u : standardUnipotentPoints i ν J,
            ENNReal.ofReal (rationalXi hKc hPK ((m : rationalPoints G) * u) *
              (1 + rationalHeight (F := F) ρ ((m : rationalPoints G) * u)) ^ (-d')) ∂nuU ≤
        c * ENNReal.ofReal (rationalLeviXi hKc hM m *
          (1 + rationalHeight (F := F) ρ m) ^ (-d))) :
    ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
      (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
      (fun m => rationalHeight (F := F) ρ m) := by
  have hMcompact : IsCompact (K0.subgroupOf (standardLeviPoints i ν J) :
      Set (standardLeviPoints i ν J)) :=
    (isClosed_standardLeviPoints i ν J).isClosedEmbedding_subtypeVal.isCompact_preimage hK0c
  refine constantTermEstimate_of_doubleCosetCover (rationalIsConjModulus nuU)
    (fun k hk => standardUnipotentModulus_eq_one i ν J hK0o hK0c k hk) hcover ?_ ?_ hT
  · intro r
    obtain ⟨A, hA⟩ := exists_rationalXi_kernel_compact_mul hKo hKc ρ hPK hK0c (-r)
    exact ⟨A, fun k₁ hk₁ k₂ hk₂ g => hA k₁ hk₁ k₂ hk₂ g⟩
  · exact fun r => exists_rationalLeviXi_kernel_compact_mul hKo hKc ρ hG hi hν hJ hM hMcompact (-r)

/-- The compact-cover reduction for the actual weights, with an arbitrary
representative set and independently supplied compact subgroups. -/
def RationalConstantTermCompactCoverStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ K0 : Subgroup (rationalPoints G), IsOpen (K0 : Set (rationalPoints G)) →
      IsCompact (K0 : Set (rationalPoints G)) →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
      (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
        (K.subgroupOf (standardLeviPoints i ν J)))
      (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
      (nuU : Measure (standardUnipotentPoints i ν J)) [nuU.IsHaarMeasure]
      (T : Set (standardLeviPoints i ν J)),
      IsDoubleCosetCover (K0.subgroupOf (standardLeviPoints i ν J)) T →
      (∀ d : ℝ, ∃ d' : ℝ, ∃ c : ℝ≥0, ∀ m ∈ T,
        (NNReal.sqrt (standardUnipotentModulus i ν J m) : ℝ≥0∞) *
            ∫⁻ u : standardUnipotentPoints i ν J,
              ENNReal.ofReal (rationalXi hKc hPK ((m : rationalPoints G) * u) *
                (1 + rationalHeight (F := F) ρ ((m : rationalPoints G) * u)) ^ (-d')) ∂nuU ≤
          c * ENNReal.ofReal (rationalLeviXi hKc hM m *
            (1 + rationalHeight (F := F) ρ m) ^ (-d))) →
      ConstantTermEstimate nuU (standardUnipotentModulus i ν J) (rationalXi hKc hPK)
        (rationalHeight (F := F) ρ) (rationalLeviXi hKc hM)
        (fun m => rationalHeight (F := F) ρ m)

/-- The actual compact-cover reduction, at arbitrary field universe. -/
theorem rationalConstantTermCompactCover : RationalConstantTermCompactCoverStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ K0 hK0o hK0c K hKo hKc hPK hM
    N _ ρ nuU _ T hcover hT
  exact rationalConstantTermEstimate_of_compact_doubleCosetCover hKo hKc ρ hG hi hν hJ
    hPK hM hK0o hK0c hcover nuU hT

end Langlands.HarishChandraSchwartz
