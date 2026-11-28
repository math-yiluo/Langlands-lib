import Langlands.Global.AdelicCharacteristicShellMeasure
import Langlands.Global.AdelicParabolicCoordinateFibres
import Langlands.Global.AdelicRelativeIwasawaHeight
import Langlands.Global.AdelicTruncationShellProduct

/-! # Product coordinates on the actual characteristic shell -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus ArthurTruncation
  ArthurRelative AdelicSiegelFactors AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)

local notation "P" => fam.P J
local notation "M" => fam.M J
local notation "A" => fam.A J
local notation "T" => fam.T
local notation "p" => fam.p J
local notation "l" => fam.l J
local notation "u" => fam.iU J
local notation "a" => fam.a J
local notation "j" => fam.l J ≫ fam.p J
local notation "D" => fam.coroots
local notation "H₀" => fam.minimalHeight hK
local notation "hU" => fam.isUnipotentRadical J
set_option quotPrecheck false in
local notation "hM" => (fam.isCompatible J).levi.isConnectedReductive
set_option quotPrecheck false in
local notation "ha" => (fam.isCompatible J).splitComponent
local notation "G₁" => normOneSubgroup F G
local notation "M₁" => normOneSubgroup F M
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "X" => (N × (B × M₁)) × K
local notation "ΓJ" => parabolicRationalNormOneSubgroup (F := F) (fam.p J)
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "KM" => K.comap (ContinuousMonoidHom.toMonoidHom (map F M G (fam.l J ≫ fam.p J)))
local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "pcoord" => fam.characteristicShellCoordinates J hK
local notation "CLevi" => characteristicLeviChamber fam.connectedReductive fam.maximalSplit D J
local notation "CSplit" => characteristicSplitShell fam.connectedReductive fam.maximalSplit D J
local notation "CFull" => characteristicShell fam.connectedReductive fam.maximalSplit D J

local instance : IsClosedImmersion (p).hom.hom.left := fam.isClosedImmersion_p J
local instance : IsAffineHom (M).X.hom := (hM).isAffineHom
local instance : IsIso (subgroupMultiplication l u) :=
  Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
    (⟨⟨T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ : ParabolicRootPresentation p l a)
    fam.connectedReductive hU

/-- Multiplication of the four Iwasawa factors inside the ambient norm-one group. -/
def characteristicShellRepresentative (x : X) : G₁ :=
  (normOneParabolicImageEquiv p (normOneParabolicCoordinates p u l hU
    (x.1.1, relativeLeviDecomposition (j) a hM ha x.1.2))).val * compactToNormOne K hK.isCompact x.2

/-- The shell quotient map is multiplication followed by the rational parabolic projection. -/
theorem characteristicShellCoordinates_eq_mk (x : X) :
    pcoord x = LeftCosetSpace.mk ΓJ (fam.characteristicShellRepresentative J hK x) := rfl

/-- The underlying adelic value of the norm-one representative. -/
theorem characteristicShellRepresentative_val (x : X) :
    (fam.characteristicShellRepresentative J hK x).val =
      x.1.1.val * (fam.relativeSplitPoint J x.1.2.1 * map F M G (j) x.1.2.2.val) * x.2.val := by
  change map F P G p (normOneParabolicCoordinates p u l hU
    (x.1.1, relativeLeviDecomposition (j) a hM ha x.1.2)).val * x.2.val = _
  have hn : map F P G p (radicalInclusion p u x.1.1) = x.1.1.val := map_radicalInclusion p u x.1.1
  simp only [normOneParabolicCoordinates_apply, map_mul, hn]
  rw [← map_comp_apply_of_hom, relativeLeviDecomposition_apply, map_mul]
  rfl

include hK in
/-- Iwasawa coverage and the two Levi decompositions give surjectivity before rational quotienting. -/
theorem surjective_characteristicShellRepresentative :
    Function.Surjective (fam.characteristicShellRepresentative J hK) := by
  intro g
  obtain ⟨q, k, hk, hg⟩ := (fam.isIwasawaCompact_index hK J).exists_eq g.val
  have hg' : map F P G p q = g.val * k⁻¹ := by rw [← hg, mul_inv_cancel_right]
  have hq : q ∈ ambientNormOneLevi p := by
    change map F P G p q ∈ G₁
    rw [hg']
    exact (G₁).mul_mem g.property ((G₁).inv_mem (compactToNormOne K hK.isCompact ⟨k, hk⟩).property)
  obtain ⟨⟨n, m⟩, hnm⟩ := (normOneParabolicCoordinates p u l hU).surjective ⟨q, hq⟩
  obtain ⟨⟨b, m₁⟩, hb⟩ := (relativeLeviDecomposition (j) a hM ha).surjective m
  refine ⟨((n, (b, m₁)), ⟨k, hk⟩), Subtype.ext ?_⟩
  change map F P G p (normOneParabolicCoordinates p u l hU
    (n, relativeLeviDecomposition (j) a hM ha (b, m₁))).val * k = g.val
  rw [hb, hnm]
  exact hg

/-- The intrinsic Levi quotient height region, with both cutoffs projected onto the Levi coroot
space by the characteristic chamber. -/
def characteristicLeviHeightRegion (T₀ Tp : V T) : Set (NormOneRationalQuotient F M) :=
  LeftCosetSpace.mk ΓM '' {m : M₁ | H₀ (map F M G (j) m.val) ∈ CLevi T₀ Tp}

/-- The relative positive split height region for the increment of the cutoff. -/
def characteristicSplitHeightRegion (Tp S : V T) : Set B :=
  {b | H₀ (fam.relativeSplitPoint J b) ∈ CSplit Tp S}

private theorem characteristicLeviHeightRegion_inv (T₀ Tp : V T) (k : M₁) (hk : k.val ∈ KM)
    (q : NormOneRationalQuotient F M) :
    LeftCosetSpace.rightTranslate ΓM k q ∈ fam.characteristicLeviHeightRegion J hK T₀ Tp →
      q ∈ fam.characteristicLeviHeightRegion J hK T₀ Tp := by
  rintro ⟨m, hm, he⟩
  refine ⟨m * k⁻¹, ?_, ?_⟩
  · change H₀ (map F M G (j) (m.val * k.val⁻¹)) ∈ CLevi T₀ Tp
    have hk' : map F M G (j) k.val ∈ K := hk
    rw [map_mul, map_inv, fam.minimalHeight_mul_right hK _ (K.inv_mem hk')]
    exact hm
  · rw [← LeftCosetSpace.rightTranslate_mk, he, LeftCosetSpace.rightTranslate_mul,
      mul_inv_cancel, LeftCosetSpace.rightTranslate_one]

omit [NumberField F] in
private theorem add_mem_characteristicShell_iff (T₀ Tp S : V T)
    (hcut : ∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) (hS : ∀ α ∈ J.val, 0 ≤ eval T α S)
    {b m : V T} (hb : b ∈ aSpace T J.val) (hm : m ∈ corootSubspace D J.val) :
    b + m ∈ CFull T₀ Tp S ↔ b ∈ CSplit Tp S ∧ m ∈ CLevi T₀ Tp := by
  rw [truncationShellProduct fam.connectedReductive fam.maximalSplit D J fam.generic hcut hS, Set.mem_add]
  let proj := levelProjection fam.connectedReductive fam.maximalSplit fam.ν D J.val
  have hleft (y : V T) (hy : y ∈ aSpace T J.val) : proj y = y := by
    rw [← levelProjection_eq_projectionOnto fam.connectedReductive fam.maximalSplit fam.generic D J.property,
      Submodule.projectionOnto_apply_of_mem_left _ hy]
  have hright (y : V T) (hy : y ∈ corootSubspace D J.val) : proj y = 0 := by
    rw [← levelProjection_eq_projectionOnto fam.connectedReductive fam.maximalSplit fam.generic D J.property,
      Submodule.projectionOnto_apply_of_mem_right _ hy]
    rfl
  constructor
  · rintro ⟨m', hm', b', hb', he⟩
    have hp := congrArg proj he
    rw [map_add, map_add, hright m' hm'.1, hleft b' hb'.1.2.1, hleft b hb, hright m hm,
      zero_add, add_zero] at hp
    rw [hp, add_comm m', add_right_inj] at he
    exact ⟨hp ▸ hb', he ▸ hm'⟩
  · rintro ⟨hb', hm'⟩
    exact ⟨m, hm', b, hb', add_comm _ _⟩

private theorem replace_LeviRepresentative (n : N) (b : B) (m m' : M₁) (k : K)
    (hm : LeftCosetSpace.mk ΓM m = LeftCosetSpace.mk ΓM m') :
      ∃ n' : N, pcoord ((n', (b, m')), k) = pcoord ((n, (b, m)), k) := by
  obtain ⟨r, hr⟩ := (LeftCosetSpace.mk_eq_mk_iff ΓM _ _).mp hm
  change rationalNormOne F M r = m' * m⁻¹ at hr
  let q : RationalGroupPoints F P := (M).affinePointsTarget l _ r
  let d := mapNormOne F P G p (rationalNormOne F P q)
  have hd : d ∈ ΓJ := ⟨rationalNormOne F P q, ⟨q, rfl⟩, rfl⟩
  have hq : rational F P q = map F M P l (rational F M r) := (map_rational l r).symm
  have hδ : d.val = map F M G (j) (rational F M r) := by
    change map F P G p (rational F P q) = _
    rw [hq, ← map_comp_apply_of_hom]
  let n' := EisensteinConstantTerm.conjAdelic p u (hU).1.isNormal (rational F P q) n
  have hn' : n'.val = d.val * n.val * d.val⁻¹ := rfl
  have hmr : rationalNormOne F M r * m = m' := by rw [hr, inv_mul_cancel_right]
  have hm' : map F M G (j) m'.val = d.val * map F M G (j) m.val := by
    rw [← hmr, Subgroup.coe_mul, map_mul, hδ]
    rfl
  have hc : Commute (fam.relativeSplitPoint J b) d.val := by
    rw [hδ, relativeSplitPoint]
    exact (positivePointMap_commute F M A a (ha).1.2 b.val (rational F M r)).map (map F M G (j))
  refine ⟨n', ?_⟩
  rw [fam.characteristicShellCoordinates_eq_mk J hK, fam.characteristicShellCoordinates_eq_mk J hK]
  have he : fam.characteristicShellRepresentative J hK ((n', (b, m')), k) =
      d * fam.characteristicShellRepresentative J hK ((n, (b, m)), k) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, fam.characteristicShellRepresentative_val J hK,
      fam.characteristicShellRepresentative_val J hK]
    dsimp only [Prod.fst, Prod.snd]
    rw [hn', hm', ← mul_assoc (fam.relativeSplitPoint J b) d.val, hc.eq]
    group
  rw [he]
  exact LeftCosetSpace.mk_subgroup_mul ΓJ ⟨d, hd⟩ _

variable (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
  (Standard.leviScheme fam.i fam.ν ∅))

/-- The coordinate pullback of the actual parabolic shell is a product of the split shell
with the intrinsic Levi height region and the full radical and compact factors. -/
def CharacteristicShellRelativeProductStatement : Prop :=
  IsMaximalCompactSubgroup F M KM → IsRationalCovering C →
    ∀ T₀ Tp S : V T, (∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) → (∀ α ∈ J.val, 0 ≤ eval T α S) →
      pcoord ⁻¹' fam.presentedCharacteristicShellLift J hK C T₀ Tp S =
        {x | x.1.2.1 ∈ fam.characteristicSplitHeightRegion J hK Tp S ∧
          LeftCosetSpace.mk ΓM x.1.2.2 ∈ fam.characteristicLeviHeightRegion J hK T₀ Tp}

set_option maxHeartbeats 1500000 in
/-- Split the minimal height before quotienting. In the parabolic quotient the intrinsic Levi
condition is rationally saturated, and the coordinate fibre relation gives the exact preimage. -/
theorem characteristicShellRelativeProduct : fam.CharacteristicShellRelativeProductStatement J hK C := by
  intro hKM hcov T₀ Tp S hcut hS
  let f := pcoord
  let rep := fam.characteristicShellRepresentative J hK
  let W := {g : G₁ | H₀ g.val ∈ CFull T₀ Tp S}
  let B₀ := fam.characteristicSplitHeightRegion J hK Tp S
  let M₀ := {m : M₁ | H₀ (map F M G (j) m.val) ∈ CLevi T₀ Tp}
  let S₀ : Set X := {x | x.1.2.1 ∈ B₀ ∧ x.1.2.2 ∈ M₀}
  let S₁ : Set X := {x | x.1.2.1 ∈ B₀ ∧ LeftCosetSpace.mk ΓM x.1.2.2 ∈
    fam.characteristicLeviHeightRegion J hK T₀ Tp}
  have hRep : rep ⁻¹' W = S₀ := by
    ext x
    obtain ⟨hb, h⟩ := fam.relativeIwasawaHeight J hK
    change H₀ (rep x).val ∈ CFull T₀ Tp S ↔ _
    rw [fam.characteristicShellRepresentative_val J hK, (h x.1.1 x.1.2.1 x.1.2.2 x.2).1]
    exact fam.add_mem_characteristicShell_iff J T₀ Tp S hcut hS (hb x.1.2.1).1
      (h x.1.1 x.1.2.1 x.1.2.2 x.2).2
  have hImage : LeftCosetSpace.mk ΓJ '' W = f '' S₀ := by
    have hW : rep '' (rep ⁻¹' W) = W :=
      Set.image_preimage_eq W (fam.surjective_characteristicShellRepresentative J hK)
    calc
      _ = LeftCosetSpace.mk ΓJ '' (rep '' (rep ⁻¹' W)) :=
        congrArg (Set.image (LeftCosetSpace.mk ΓJ)) hW.symm
      _ = f '' (rep ⁻¹' W) := Set.image_image _ _ _
      _ = _ := congrArg (Set.image f) hRep
  have hImage' : f '' S₀ = f '' S₁ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hx.1, ⟨x.1.2.2, hx.2, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨⟨n, ⟨b, m⟩⟩, k⟩, ⟨hb, ⟨m', hm', hEq⟩⟩, rfl⟩
      obtain ⟨n', h⟩ := fam.replace_LeviRepresentative J hK n b m m' k hEq.symm
      exact ⟨((n', (b, m')), k), ⟨hb, hm'⟩, h⟩
  have hLift : fam.presentedCharacteristicShellLift J hK C T₀ Tp S = LeftCosetSpace.mk ΓJ '' W :=
    fam.characteristicHeightLift hK J C hcov _
  change f ⁻¹' (fam.presentedCharacteristicShellLift J hK C T₀ Tp S) = S₁
  rw [hLift, hImage, hImage']
  exact relativeParabolicCoordinateSaturation p u l hU a hM ha hK.isCompact hKM B₀ _
    (fam.characteristicLeviHeightRegion_inv J hK T₀ Tp)

open MeasureTheory

local notation "ΓN" =>
  AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))

/-- The factor restrictions of the relative Iwasawa measure on the shell. -/
def characteristicRelativeProductMeasure (dn : Measure N) (da : Measure B) (T₀ Tp S : V T) :
    Measure X :=
  ((dn.restrict (LeftCosetSpace.fundamentalDomain ΓN
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (u ≫ p))))).prod
    (((da.withDensity (relativePositiveDensity p l a)).restrict
        (fam.characteristicSplitHeightRegion J hK Tp S)).prod
      (((MeasureTheory.Measure.haar : Measure M₁).restrict
        (LeftCosetSpace.fundamentalDomain ΓM (isDiscrete_rationalNormOneSubgroup F M))).restrict
          (LeftCosetSpace.mk ΓM ⁻¹' fam.characteristicLeviHeightRegion J hK T₀ Tp)))).prod
    (compactHaarProbability F G K hK.isCompact)

set_option maxHeartbeats 1500000 in
/-- The fixed relative split Haar gives the actual shell measure after restricting the split
and intrinsic Levi factors individually. -/
theorem characteristicRelativeProductMeasure_preserving (hKM : IsMaximalCompactSubgroup F M KM)
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (dn : Measure N) [dn.IsHaarMeasure]
    (T₀ : V T) :
    ∃ R > 0, ∃ da : Measure B, da.IsHaarMeasure ∧ SigmaFinite da ∧
      ∀ Tp S : V T, (∀ α ∈ Δ, R ≤ eval T α Tp) →
        (∀ α ∈ Δ, 0 ≤ eval T α (Tp - T₀)) → (∀ α ∈ J.val, 0 ≤ eval T α S) →
        MeasurePreserving (LeftCosetSpace.projectionOfLE (fam.parabolicRationalNormOneSubgroup_le J) ∘ pcoord)
          (fam.characteristicRelativeProductMeasure J hK dn da T₀ Tp S)
          ((normOneRationalQuotientHaarMeasure F G).restrict
            (characteristicShellRegion fam.connectedReductive fam.maximalSplit D
              (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot C J T₀ Tp S)) := by
  obtain ⟨R, hR, da, hda, hsf, h⟩ :=
    fam.characteristicShellCoordinateMeasure_preserving J hK C dn hC hcov T₀
  refine ⟨R, hR, da, hda, hsf, fun Tp S hTp hcut hS => ?_⟩
  have hm := h Tp S hTp
  dsimp only at hm
  have hpre : pcoord ⁻¹' fam.presentedCharacteristicShellLift J hK C T₀ Tp S =
      (Set.univ ×ˢ (fam.characteristicSplitHeightRegion J hK Tp S ×ˢ
        (LeftCosetSpace.mk ΓM ⁻¹' fam.characteristicLeviHeightRegion J hK T₀ Tp))) ×ˢ Set.univ := by
    rw [fam.characteristicShellRelativeProduct J hK C hKM hcov T₀ Tp S hcut hS]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, and_true, Set.mem_preimage]
  rw [hpre, characteristicShellCoordinateMeasure, ← Measure.prod_restrict, ← Measure.prod_restrict,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ] at hm
  exact hm

end Langlands.Global.StandardParabolicFamily
