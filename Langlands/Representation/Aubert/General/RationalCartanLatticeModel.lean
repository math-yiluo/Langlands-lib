import Langlands.Representation.Aubert.General.CartanLatticeContraction
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.GroupScheme.Rational.StandardLeviLieWeights
import Langlands.GroupScheme.Rational.SplitComponentCocharacters
import Langlands.GroupScheme.Dynamic.LieProof

/-!
# The lattice model of the Cartan elements of `G(F)`

For a maximal split torus `i : S → G` of a reductive group over a nonarchimedean
local field `F`, a generic cocharacter `ν`, a represented torus centralizer
`j : Z → G` with `s ≫ j = i`, and a finite subset `F₀ ⊆ Z(F)`:

* `uniformizerPowers i` is `x ↦ ϖ^x = i(x(ϖ))`, and `simpleRootPairing i ν β` is
  `x ↦ ⟨β, x⟩`;
* `rationalCartanSet i ν j s h F₀ I` is the image in `G(F)` of Renard's dominant
  Cartan representatives `C₀ F₀ ∩ Z_dom(M_I)`;
* `isCartanLatticeModel_rational` shows that these data, with the standard family
  `levi i ν`, `unipotent i ν`, form an `IsCartanLatticeModel`, given standard
  cocharacters for every `I`, the uniformizer valuation formula of the centralizer,
  and a simultaneous Renard V.5.2 basis. The contraction field comes from
  Renard V.5.2 (iii) for the standard split component of each `M_J`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open Langlands.AlgebraicGeometry.PointTopology
open scoped Topology

namespace Langlands.Aubert.General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The normalized norm of a character `α` at the uniformizer power `ϖ^c` is
`q^{-⟨α, c⟩}`. -/
theorem characterNorm_latticeSection (A : CommGroupScheme (Spec (CommRingCat.of F)))
    (α : characterLattice A) (c : cocharacterLattice A) :
    CocharacterUniformizer.characterNorm F A α
        (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)) =
      (LocalField.residueCardinality F : ℝ) ^ (-(latticePairing A α c)) := by
  unfold CocharacterUniformizer.characterNorm
  rw [Plancherel.rationalNormCharacters_val, rationalCharacterEval_apply]
  change LocalField.residueNormalizedAbsoluteValue F
    ((Gm.affinePointsEquiv (𝟙 _)
      ((((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
        (SplitTorusValuation.uniformizerUnit F)) ≫
          (CommGroupScheme.groupHom c).hom.hom) ≫
            (CommGroupScheme.groupHom α).hom.hom) : Fˣ) : F) = _
  rw [← comp_groupHom_comp, eq_gmEndEquiv_zsmul F (c ≫ α), Gm.comp_zsmul_id, map_zpow,
    MulEquiv.apply_symm_apply, Units.val_zpow_eq_zpow_val, map_zpow₀,
    SplitTorusValuation.uniformizerUnit_val,
    LocalField.residueNormalizedAbsoluteValue_uniformizer, ← zpow_mul, latticePairing_apply]
  ring_nf

/-- Large exponents make `q^{-p}` small. -/
theorem exists_residueCardinality_zpow_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℤ, ∀ p : ℤ, L ≤ p → (LocalField.residueCardinality F : ℝ) ^ (-p) < ε := by
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  refine ⟨n, fun p hp => lt_of_le_of_lt ?_ hn⟩
  calc (LocalField.residueCardinality F : ℝ) ^ (-p)
      ≤ (LocalField.residueCardinality F : ℝ) ^ (-(n : ℤ)) :=
        zpow_le_zpow_right₀ hq.le (neg_le_neg hp)
    _ = ((LocalField.residueCardinality F : ℝ)⁻¹) ^ n := by
        rw [zpow_neg, zpow_natCast, inv_pow]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Restricting a character along `q` pairs with `c` as the character pairs with
`q ∘ c`. -/
theorem latticePairing_componentCharacterRestriction
    {A S : CommGroupScheme (Spec (CommRingCat.of F))} (q : A.toGrp ⟶ S.toGrp)
    (β : characterLattice S) (c : cocharacterLattice A) :
    latticePairing A (BruhatTits.SpecialCompact.componentCharacterRestriction q β) c =
      latticePairing S β (c ≫ Additive.ofMul q) :=
  rfl

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

open RationalPointFamily

/-- The uniformizer powers `ϖ^x = i(x(ϖ))` in `G(F)`. -/
def uniformizerPowers : Multiplicative (cocharacterLattice S) →* rationalPoints G :=
  (rationalPoints.map i).comp (Plancherel.RenardCartan.uniformizerSection S)

/-- The integer pairing of a simple root with cocharacters. -/
def simpleRootPairing (β : SimpleRoot i ν) : cocharacterLattice S →+ ℤ :=
  (latticePairing S β.1).toAddMonoidHom

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem simpleRootPairing_apply (β : SimpleRoot i ν) (x : cocharacterLattice S) :
    simpleRootPairing i ν β x = latticePairing S β.1 x := rfl

/-- The uniformizer powers lie in every standard Levi. -/
theorem uniformizerPowers_mem_levi (I : Finset (SimpleRoot i ν)) (x : cocharacterLattice S) :
    uniformizerPowers i (.ofAdd x) ∈ levi i ν I :=
  torusPoints_le_levi i ν I ((mem_torusPoints i _).mpr ⟨_, rfl⟩)

/-- A uniformizer power `ϖ^x` with `x` orthogonal to `I` commutes with `M_I`. -/
theorem commute_uniformizerPowers (hfinite : (simpleRelativeRoots i ν).Finite)
    (I : Finset (SimpleRoot i ν))
    (hexists : ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (x : cocharacterLattice S) (hx : ∀ β ∈ I, simpleRootPairing i ν β x = 0)
    (m : rationalPoints G) (hm : m ∈ levi i ν I) :
    m * uniformizerPowers i (.ofAdd x) = uniformizerPowers i (.ofAdd x) * m := by
  have hm' : m ∈ (cocharacterAnnihilatorCentralizer i (rootSet i ν I)).carrier
      (Over.mk (𝟙 _)) := by
    rw [← standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfinite _ hexists]
    exact hm
  rw [mem_cocharacterAnnihilatorCentralizer] at hm'
  have h := hm' x (by rintro α ⟨β, hβ, rfl⟩; exact hx β hβ)
  rw [← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer] at h
  have hc := h (Over.mk (𝟙 _)) (𝟙 _)
    ((Gm.affinePointsEquiv (𝟙 _)).symm (SplitTorusValuation.uniformizerUnit F))
  rw [Category.id_comp, Grp.comp_hom_hom, ← Category.assoc] at hc
  exact hc

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Selected simple roots are positive roots of the standard Levi. -/
theorem mem_positiveRelativeRoots_leviTorusHom [LocallyOfFiniteType G.X.hom]
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {β : characterLattice S} (hβ : β ∈ J) :
    haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    β ∈ positiveRelativeRoots (Standard.leviTorusHom i ν J) ν := by
  have : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  exact ⟨selectedRoots_subset_relativeRoots_standardLeviTorusFactor dynamicLie i ν J
      (Standard.isRepresentedBy_leviHom i ν J) hJ hβ,
    (simpleRelativeRoots_subset_positive i ν (hJ hβ)).2⟩

variable (j : Z ⟶ G) (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

/-- **The Cartan set of `M_I`.** The image in `G(F)` of Renard's representatives
`(C₀ F₀) ∩ Z_dom(M_I)` for one finite lattice transversal `F₀` of the centralizer
`Z(F)` of the maximal split torus; the dominance is for the positive roots of the
standard Levi `M_I`. -/
def rationalCartanSet (F0 : Set (rationalPoints Z)) (I : Finset (SimpleRoot i ν)) :
    Set (rationalPoints G) :=
  haveI : IsAffineHom (Standard.leviScheme i ν (rootSet i ν I)).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν _).isAffineHom
  rationalPoints.map j '' Plancherel.RenardCartan.tildeC0Plus s F0
    (dominantCentralizer (Standard.leviTorusHom i ν (rootSet i ν I)) ν s h)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Points of the torus centralizer `Z(F)` lie in every standard Levi. -/
theorem map_mem_levi_of_isRepresentedBy (hrep : (torusCentralizer i).IsRepresentedBy j)
    (I : Finset (SimpleRoot i ν)) (f : rationalPoints Z) :
    rationalPoints.map j f ∈ levi i ν I := by
  apply centralizerPoints_le_levi i ν I
  rw [← torusCentralizer_carrier_base, ← hrep.2]
  exact SubgroupFunctor.mem_range.mpr ⟨f, rfl⟩

/-- Every Cartan element is `ϖ^x f` with `f` in the transversal and pairings with the
simple roots of `I` bounded below. -/
theorem exists_rep_rationalCartanSet [LocallyOfFiniteType G.X.hom] (hsj : s ≫ j = i)
    (hval : ∀ c : cocharacterLattice S,
      (centralizerValuation s h (rationalPoints.map s
        (Plancherel.RenardCartan.uniformizerSection S (Multiplicative.ofAdd c)))).toAdd =
          1 ⊗ₜ[ℤ] c)
    {F0 : Set (rationalPoints Z)} (hF0 : F0.Finite) (I : Finset (SimpleRoot i ν)) :
    ∃ B : ℤ, ∀ t ∈ rationalCartanSet i ν j s h F0 I, ∃ x : cocharacterLattice S,
      ∃ f ∈ rationalPoints.map j '' F0,
        t = uniformizerPowers i (.ofAdd x) * f ∧ ∀ β ∈ I, -B ≤ simpleRootPairing i ν β x := by
  obtain ⟨b, hb⟩ := ((I.finite_toSet.prod hF0).image (fun p : SimpleRoot i ν × _ =>
    RealTorusSpace.eval S p.1.1 (centralizerValuation s h p.2).toAdd)).bddAbove
  refine ⟨⌈b⌉, ?_⟩
  rintro _ ⟨z, ⟨hzC, hzD⟩, rfl⟩
  obtain ⟨c, hc, f, hf, rfl⟩ := (Plancherel.RenardCartan.mem_tildeC0 s F0 z).mp hzC
  obtain ⟨x, rfl⟩ := (Plancherel.RenardCartan.mem_C0 S s c).mp hc
  refine ⟨x, rationalPoints.map j f, ⟨f, hf, rfl⟩, ?_, fun β hβ => ?_⟩
  · rw [map_mul, uniformizerPowers, MonoidHom.comp_apply, ← hsj]
    rfl
  · have hpos := hzD β.1 (mem_positiveRelativeRoots_leviTorusHom i ν (rootSet_subset i ν I)
      ((val_mem_rootSet i ν I β).mpr hβ))
    rw [map_mul, toAdd_mul, hval, map_add, RealTorusSpace.eval_tmul, one_mul] at hpos
    have hfb : RealTorusSpace.eval S β.1 (centralizerValuation s h f).toAdd ≤ b :=
      hb ⟨(β, f), ⟨hβ, hf⟩, rfl⟩
    have hbc : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
    have : (-⌈b⌉ : ℝ) ≤ (latticePairing S β.1 x : ℝ) := by linarith
    simp only [simpleRootPairing_apply]
    exact_mod_cast this

open BruhatTits.SpecialCompact in
/-- **Contraction of a standard unipotent element** (Renard V.5.2 (iii)). For
`u ∈ N_J` and a neighbourhood `O` of `1`, `ϖ^y u ϖ^{-y} ∈ O` whenever `y` is
orthogonal to `J` and pairs to at least `L` with the simple roots outside `J`. -/
theorem uniformizerPowers_conj_mem (hi : IsMaximalSplitTorus i)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    (J : Finset (SimpleRoot i ν)) (u : rationalPoints G) (hu : u ∈ unipotent i ν J) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ O ∈ 𝓝 (1 : rationalPoints G), ∃ L : ℤ, ∀ y : cocharacterLattice S,
      (∀ β ∈ J, simpleRootPairing i ν β y = 0) → (∀ β ∉ J, L ≤ simpleRootPairing i ν β y) →
        uniformizerPowers i (.ofAdd y) * u * (uniformizerPowers i (.ofAdd y))⁻¹ ∈ O := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro O hO
  obtain ⟨B, hB, hJ⟩ := hbasis
  obtain ⟨-, A, q, ⟨-, M, jM, a, hjM, hjMc, hMred, ha, haq⟩, hmem⟩ :=
    hJ (rootSet i ν J) (rootSet_subset i ν J)
  obtain ⟨K, hKB, hKO⟩ := hB.2.mem_iff.mp hO
  obtain ⟨ε, hε, hεm⟩ := (hmem K hKB).2.2.2.2.1.1 {⟨u, hu⟩} isCompact_singleton
  obtain ⟨L, hL⟩ := exists_residueCardinality_zpow_lt (F := F) hε
  refine ⟨L, fun y hy hyL => ?_⟩
  -- `y` is a cocharacter of the split component `A`
  let t := standardLeviTorusFactor i ν (rootSet i ν J) hjM
  have : IsAffineHom M.X.hom := hMred.isAffineHom
  have : Mono t.hom.hom.left :=
    (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν _ hjM hjMc).isSplitSubtorus.mono
  have hf : CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S) ≫ t = a := by
    have : Mono jM.hom.hom := hjM.1
    apply Grp.hom_ext
    apply (cancel_mono jM.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc,
      standardLeviTorusFactor_comp, haq]
    rfl
  have hyc : y ∈ centralCocharacters t :=
    isCentral_standardLeviTorusFactor_of_annihilates i ν (rootSet i ν J) hjM hfinite
      (hexists J) y (by rintro α ⟨β, hβ, rfl⟩; exact hy β hβ)
  rw [← ha.range_cocharacterMapInt_eq_centralCocharacters _ hf] at hyc
  obtain ⟨c, rfl⟩ := hyc
  -- `ϖ^y` lies in the epsilon chamber of `A`
  have hCA : uniformizerPowers i (.ofAdd (RealTorusSpace.cocharacterMapInt
      (Additive.ofMul q : A ⟶ S) c)) ∈ standardComponentCAepsilon i ν (rootSet i ν J) q ε := by
    refine ⟨CocharacterUniformizer.latticeSection F A (.ofAdd c), ⟨⟨.ofAdd c, rfl⟩, ?_⟩, ?_⟩
    · rintro _ ⟨β, ⟨hβs, hβJ⟩, rfl⟩
      rw [characterNorm_latticeSection, latticePairing_componentCharacterRestriction]
      have hβJ' : (⟨β, hβs⟩ : SimpleRoot i ν) ∉ J := fun h =>
        hβJ ((val_mem_rootSet i ν J ⟨β, hβs⟩).mpr h)
      exact hL _ (hyL ⟨β, hβs⟩ hβJ')
    · change rationalPoints.map i (rationalPoints.map
        (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
          (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
      rw [Plancherel.RenardCartan.uniformizerSection_naturality]
      rfl
  obtain ⟨k, hk, hku⟩ := hεm _ hCA ⟨⟨u, hu⟩, rfl, rfl⟩
  apply hKO
  have : uniformizerPowers i (.ofAdd (RealTorusSpace.cocharacterMapInt
      (Additive.ofMul q : A ⟶ S) c)) * u *
        (uniformizerPowers i (.ofAdd (RealTorusSpace.cocharacterMapInt
          (Additive.ofMul q : A ⟶ S) c)))⁻¹ = k := by
    have hku' : _ = u := hku
    rw [← hku']
    group
  rw [this]
  exact hk.1

open BruhatTits.SpecialCompact in
/-- **The lattice model of `G(F)`.** The standard family of `G(F)`, its Cartan sets,
the uniformizer powers `ϖ^x`, the simple-root pairings and the image of a finite
lattice transversal of `Z(F)` form a `IsCartanLatticeModel`. -/
theorem isCartanLatticeModel_rational [LocallyOfFiniteType G.X.hom]
    (hi : IsMaximalSplitTorus i) (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrep : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hval : ∀ c : cocharacterLattice S,
      (centralizerValuation s h (rationalPoints.map s
        (Plancherel.RenardCartan.uniformizerSection S (Multiplicative.ofAdd c)))).toAdd =
          1 ⊗ₜ[ℤ] c)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
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
        uniformizerPowers_conj_mem i ν hi hfinite hexists hbasis J u hu }

end Langlands.Aubert.General
