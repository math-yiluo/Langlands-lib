import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Exponents.PresentationConeContractionProof

/-!
# Contraction of standard unipotent points by uniformizer powers

For a maximal split torus `i : S → G` of an affine group over a nonarchimedean local
field `F`, a generic cocharacter `ν` and a set `J` of simple roots, conjugation by
`ϖ^y = i(y(ϖ))` contracts every rational point `u` of the standard unipotent subgroup
`N_J` to `1` once `y` is orthogonal to `J` and pairs to at least `L` with the simple
roots outside `J` (Renard V.5.2 (iii)). The proof reads the conjugate in torus-weight
coordinates: a coordinate of weight `w` is multiplied by `ϖ^{⟨w, y⟩}`, and every weight
that does not vanish at `u` pairs positively with every standard cocharacter of `J`.
No basis of compact open subgroups is used.

`isCartanLatticeModel_rational_of_standard` is `isCartanLatticeModel_rational` without
its simultaneous-basis hypothesis.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.UniformizerContraction

open Langlands.GroupScheme RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology
open RepresentedParabolic.ConeContraction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- A character takes the value `ϖ^{⟨w, y⟩}` at the uniformizer power `y(ϖ)`. -/
theorem characterValue_uniformizerSection (w : characterLattice S) (y : cocharacterLattice S) :
    (Lie.characterValue w
        (affPt (Plancherel.RenardCartan.uniformizerSection S (Multiplicative.ofAdd y))) : F) =
      LocalField.uniformizer F ^ latticePairing S w y := by
  rw [characterValue_affPt]
  change ((rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm w)
    (CocharacterUniformizer.cocharacterPoints F S y
      (SplitTorusValuation.uniformizerUnit F)) : Fˣ) : F) = _
  rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
    Units.val_zpow_eq_zpow_val, SplitTorusValuation.uniformizerUnit_val]

variable (J : Finset (SimpleRoot i ν))

/-- The cocharacters orthogonal to `J` that pair to at least `K` with every simple root
outside `J`. -/
def cone (K : ℤ) : Set (cocharacterLattice S) :=
  {y | (∀ β ∈ J, simpleRootPairing i ν β y = 0) ∧ ∀ β ∉ J, K ≤ simpleRootPairing i ν β y}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem cone_antitone {K K' : ℤ} (h : K ≤ K') : cone i ν J K' ⊆ cone i ν J K :=
  fun _ hy => ⟨hy.1, fun β hβ => h.trans (hy.2 β hβ)⟩

/-- The filter of cocharacters eventually deep inside every cone. -/
def coneFilter : Filter (cocharacterLattice S) := ⨅ K : ℤ, 𝓟 (cone i ν J K)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_coneFilter_of_subset {K : ℤ} {s : Set (cocharacterLattice S)}
    (h : cone i ν J K ⊆ s) : s ∈ coneFilter i ν J :=
  mem_iInf_of_mem K (mem_principal.2 h)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem exists_cone_subset_of_mem {s : Set (cocharacterLattice S)}
    (hs : s ∈ coneFilter i ν J) : ∃ K : ℤ, cone i ν J K ⊆ s := by
  have hdir : Directed (· ≥ ·) (fun K : ℤ => 𝓟 (cone i ν J K)) := fun K₁ K₂ =>
    ⟨max K₁ K₂, principal_mono.2 (cone_antitone i ν J (le_max_left _ _)),
      principal_mono.2 (cone_antitone i ν J (le_max_right _ _))⟩
  obtain ⟨K, hK⟩ := (mem_iInf_of_directed hdir s).1 hs
  exact ⟨K, mem_principal.1 hK⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A uniform upper bound for the pairings of one cocharacter with the simple roots. -/
theorem exists_pairing_bound (hfinite : (simpleRelativeRoots i ν).Finite)
    (ζ : cocharacterLattice S) :
    ∃ D : ℤ, 1 ≤ D ∧ ∀ β : SimpleRoot i ν, latticePairing S β.1 ζ ≤ D := by
  obtain ⟨D, hD⟩ := (hfinite.image (fun β => latticePairing S β ζ)).bddAbove
  exact ⟨max D 1, le_max_right _ _, fun β => (hD ⟨β.1, β.2, rfl⟩).trans (le_max_left _ _)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Subtracting a bounded multiple of a standard cocharacter from a point deep in the cone
leaves a standard cocharacter. -/
theorem isStandard_sub_smul {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) {D : ℤ}
    (hD : ∀ β : SimpleRoot i ν, latticePairing S β.1 ζ ≤ D)
    {K m : ℤ} (hm : 0 ≤ m) (hK : m * D + 1 ≤ K) {y : cocharacterLattice S}
    (hy : y ∈ cone i ν J K) :
    IsStandardCocharacter i ν (rootSet i ν J) (y - m • ζ) := by
  refine ⟨rootSet_subset i ν J, fun α hα => ?_, fun α hα hαJ => ?_⟩
  · obtain ⟨β, hβ, rfl⟩ := hα
    have h1 := hy.1 β hβ
    rw [simpleRootPairing_apply] at h1
    rw [map_sub, map_zsmul, hζ.2.1 _ ((val_mem_rootSet i ν J β).mpr hβ), h1]
    simp
  · have hβJ : (⟨α, hα⟩ : SimpleRoot i ν) ∉ J := fun h =>
      hαJ ((val_mem_rootSet i ν J ⟨α, hα⟩).mpr h)
    have h1 := hy.2 _ hβJ
    have h2 := hD ⟨α, hα⟩
    rw [simpleRootPairing_apply] at h1
    rw [map_sub, map_zsmul, smul_eq_mul]
    nlinarith

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Deep in the cone, a weight positive on all standard cocharacters pairs with the
cocharacter at least one more than the depth parameter. -/
theorem add_one_le_pairing {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) {D : ℤ}
    (hD : ∀ β : SimpleRoot i ν, latticePairing S β.1 ζ ≤ D)
    {K m : ℤ} (hm : 0 ≤ m) (hK : m * D + 1 ≤ K) {y : cocharacterLattice S}
    (hy : y ∈ cone i ν J K) {w : characterLattice S}
    (hw : ∀ ζ', IsStandardCocharacter i ν (rootSet i ν J) ζ' → 1 ≤ latticePairing S w ζ') :
    m + 1 ≤ latticePairing S w y := by
  have h1 := hw _ (isStandard_sub_smul i ν J hζ hD hm hK hy)
  have h2 := hw _ hζ
  rw [map_sub, map_zsmul, smul_eq_mul] at h1
  nlinarith

variable [IsAffine G.X.left]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A torus eigenfunction in the augmentation ideal that does not vanish at a rational
point of `N_J` has a weight pairing positively with every standard cocharacter of `J`. -/
theorem one_le_pairing_of_ne_zero (hT : IsSplitTorus S.toGrp) {u : RationalPoint F G.X}
    (hu : u ∈ unipotent i ν J) {w : characterLattice S}
    {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace (AutomorphicAction.conjugation i) w)
    (h0 : Lie.pointCoordinates G (affPt u) (g : CharacterUnits.Coord G) ≠ 0)
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν (rootSet i ν J) ζ) :
    1 ≤ latticePairing S w ζ := by
  by_contra hlt
  apply h0
  have hmem : affPt u ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).carrier _ :=
    (Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)).comp_mem _
      ((mem_standardUnipotent i ν).1 hu ζ hζ)
  exact (Dynamic.CocharacterWeights.mem_unipotent_iff_weights i ζ hT (affPt u)).1
    hmem w (by omega) g hg

/-- A Lie coordinate of the conjugate of `u` by the uniformizer power `ϖ^y`. -/
def conjCoord (g : CharacterUnits.Coord G) (u : RationalPoint F G.X)
    (y : cocharacterLattice S) : F :=
  Lie.pointCoordinates G ((AutomorphicAction.conjugation i).act
    (affPt (Plancherel.RenardCartan.uniformizerSection S (Multiplicative.ofAdd y))) (affPt u)) g

/-- The contraction estimate for one torus eigenfunction in the augmentation ideal. -/
theorem tendsto_conjCoord_of_mem (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ) (hT : IsSplitTorus S.toGrp)
    {u : RationalPoint F G.X} (hu : u ∈ unipotent i ν J) {w : characterLattice S}
    {g : CoordinateWeights.augmentation G}
    (hg : g ∈ CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation i) w) :
    Tendsto (conjCoord i (g : CharacterUnits.Coord G) u) (coneFilter i ν J) (𝓝 0) := by
  intro V hV
  obtain ⟨ζ, hζ⟩ := hexists
  obtain ⟨N, hN⟩ := exists_uniformizer_pow_mul_mem
    (isCompact_singleton (x := Lie.pointCoordinates G (affPt u) (g : CharacterUnits.Coord G)))
    hV
  obtain ⟨D, -, hD⟩ := exists_pairing_bound i ν hfinite ζ
  rw [Filter.mem_map]
  refine mem_coneFilter_of_subset i ν J (K := (N : ℤ) * D + 1) fun y hy => ?_
  change conjCoord i (g : CharacterUnits.Coord G) u y ∈ V
  have he : CoordinateWeights.IsEigenfunction (AutomorphicAction.conjugation i) w
      (g : CharacterUnits.Coord G) := hg
  unfold conjCoord
  rw [he F _ (affPt u)]
  by_cases h0 : Lie.pointCoordinates G (affPt u) (g : CharacterUnits.Coord G) = 0
  · rw [h0, mul_zero]
    exact mem_of_mem_nhds hV
  · have hb := add_one_le_pairing i ν J hζ hD (Int.natCast_nonneg N) le_rfl hy
      (fun ζ' hζ' => one_le_pairing_of_ne_zero i ν J hT hu hg h0 hζ')
    rw [characterValue_uniformizerSection]
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le
      (show 0 ≤ latticePairing S w y by omega)
    rw [hj, zpow_natCast]
    exact hN j (by omega) _ rfl

/-- The contraction estimate for every coordinate in the augmentation ideal. -/
theorem tendsto_conjCoord_augmentation (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ) (hT : IsSplitTorus S.toGrp)
    {u : RationalPoint F G.X} (hu : u ∈ unipotent i ν J)
    (g : CoordinateWeights.augmentation G) :
    Tendsto (conjCoord i (g : CharacterUnits.Coord G) u) (coneFilter i ν J) (𝓝 0) := by
  classical
  have htop := (CoordinateWeights.coordinateWeightDecomposition F G inferInstance S hT
    (AutomorphicAction.conjugation i)).2.1.submodule_iSup_eq_top
  have hg : g ∈ ⨆ w, CoordinateWeights.augmentationWeightSpace
      (AutomorphicAction.conjugation i) w := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun g : CoordinateWeights.augmentation G =>
    Tendsto (conjCoord i (g : CharacterUnits.Coord G) u) (coneFilter i ν J) (𝓝 0)) hg
    (fun w g hg => tendsto_conjCoord_of_mem i ν J hfinite hexists hT hu hg) ?_ ?_
  · have h : conjCoord i ((0 : CoordinateWeights.augmentation G) : CharacterUnits.Coord G) u =
        fun _ => 0 := funext fun y => by simp [conjCoord]
    rw [h]
    exact tendsto_const_nhds
  · intro x y hx hy
    have h : conjCoord i ((x + y : CoordinateWeights.augmentation G) :
        CharacterUnits.Coord G) u =
        fun z => conjCoord i (x : CharacterUnits.Coord G) u z +
          conjCoord i (y : CharacterUnits.Coord G) u z := funext fun z => by simp [conjCoord]
    rw [h]
    simpa using hx.add hy

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X

/-- Conjugation by uniformizer powers deep in the cone contracts a point of `N_J`
to the identity. -/
theorem tendsto_conj (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ) (hT : IsSplitTorus S.toGrp)
    {u : RationalPoint F G.X} (hu : u ∈ unipotent i ν J) :
    Tendsto (fun y : cocharacterLattice S =>
        uniformizerPowers i (.ofAdd y) * u * (uniformizerPowers i (.ofAdd y))⁻¹)
      (coneFilter i ν J) (𝓝 1) := by
  rw [isInducing_pointRing.tendsto_nhds_iff, tendsto_pi_nhds]
  intro b
  set g := DynamicLie.chartCoordinates G b
  set o := Lie.coordinateOrigin G g
  let g' : CoordinateWeights.augmentation G := ⟨g - algebraMap F _ o, by
    rw [CoordinateWeights.mem_augmentation, map_sub, AlgHom.commutes]
    simp [o]⟩
  have h1 : ∀ y : cocharacterLattice S, Dynamic.AffineChart.pointRing
      (uniformizerPowers i (.ofAdd y) * u * (uniformizerPowers i (.ofAdd y))⁻¹) b =
        o + conjCoord i (g' : CharacterUnits.Coord G) u y := by
    intro y
    rw [← pointCoordinates_affPt_chartCoordinates]
    change Lie.pointCoordinates G (affPt (rationalPoints.map i
      (Plancherel.RenardCartan.uniformizerSection S (.ofAdd y)) * u *
        (rationalPoints.map i (Plancherel.RenardCartan.uniformizerSection S
          (.ofAdd y)))⁻¹)) _ = _
    rw [affPt_conj]
    change _ = o + Lie.pointCoordinates G _ (g - algebraMap F _ o)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    abel
  have h2 : Dynamic.AffineChart.pointRing (1 : RationalPoint F G.X) b = o := by
    rw [← pointCoordinates_affPt_chartCoordinates, affPt_one, Lie.pointCoordinates_one]
    rfl
  change Tendsto (fun y => Dynamic.AffineChart.pointRing
    (uniformizerPowers i (.ofAdd y) * u * (uniformizerPowers i (.ofAdd y))⁻¹) b) _
    (𝓝 (Dynamic.AffineChart.pointRing (1 : RationalPoint F G.X) b))
  simp_rw [h1, h2]
  simpa using tendsto_const_nhds.add
    (tendsto_conjCoord_augmentation i ν J hfinite hexists hT hu g')

end Langlands.Aubert.General.UniformizerContraction

namespace Langlands.Aubert.General

open Langlands.GroupScheme RationalPointFamily UniformizerContraction
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- **Contraction of a standard unipotent element** (Renard V.5.2 (iii)), without a basis
of compact open subgroups. For `u ∈ N_J` and a neighbourhood `O` of `1`,
`ϖ^y u ϖ^{-y} ∈ O` whenever `y` is orthogonal to `J` and pairs to at least `L` with the
simple roots outside `J`. -/
theorem uniformizerPowers_conj_mem_of_standard (hi : IsMaximalSplitTorus i)
    (hfinite : (simpleRelativeRoots i ν).Finite) (J : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν J) ζ)
    (u : rationalPoints G) (hu : u ∈ unipotent i ν J) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ O ∈ 𝓝 (1 : rationalPoints G), ∃ L : ℤ, ∀ y : cocharacterLattice S,
      (∀ β ∈ J, simpleRootPairing i ν β y = 0) → (∀ β ∉ J, L ≤ simpleRootPairing i ν β y) →
        uniformizerPowers i (.ofAdd y) * u * (uniformizerPowers i (.ofAdd y))⁻¹ ∈ O := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro O hO
  have htend := tendsto_conj i ν J hfinite hexists hi.isSplitSubtorus.1 hu
  obtain ⟨L, hL⟩ := exists_cone_subset_of_mem i ν J (htend hO)
  exact ⟨L, fun y hy hyL => hL ⟨hy, hyL⟩⟩

variable (j : Z ⟶ G) (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

/-- **The lattice model of `G(F)`**, without a basis of compact open subgroups. The
standard family of `G(F)`, its Cartan sets, the uniformizer powers `ϖ^x`, the simple-root
pairings and the image of a finite lattice transversal of `Z(F)` form an
`IsCartanLatticeModel`. -/
theorem isCartanLatticeModel_rational_of_standard [LocallyOfFiniteType G.X.hom]
    (hi : IsMaximalSplitTorus i) (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hval : ∀ c : cocharacterLattice S,
      (centralizerValuation s h (rationalPoints.map s
        (Plancherel.RenardCartan.uniformizerSection S (Multiplicative.ofAdd c)))).toAdd =
          1 ⊗ₜ[ℤ] c)
    {F0 : Set (rationalPoints Z)} (hF0 : F0.Finite) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCartanLatticeModel (levi i ν) (unipotent i ν) (rationalCartanSet i ν j s h F0)
      (uniformizerPowers i) (simpleRootPairing i ν) (rationalPoints.map j '' F0) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact
    { finite_F₀ := hF0.image _
      exists_rep := exists_rep_rationalCartanSet i ν j s h hsj hval hF0
      e_mem_levi := uniformizerPowers_mem_levi i ν
      F₀_subset_levi := fun I => by
        rintro _ ⟨f, -, rfl⟩
        exact map_mem_levi_of_isRepresentedBy i ν j hrep I f
      levi_le_normalizer := RationalPointFamily.levi_le_normalizer i ν
      commute_of_pair_eq_zero := fun I x hx m hm =>
        commute_uniformizerPowers i ν hfinite I (hexists I) x hx m hm
      exists_standard := fun I => by
        obtain ⟨ζ, hζ⟩ := hexists I
        exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
          fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
      contracts := fun J u hu =>
        uniformizerPowers_conj_mem_of_standard i ν hi hfinite J (hexists J) u hu }

end Langlands.Aubert.General
