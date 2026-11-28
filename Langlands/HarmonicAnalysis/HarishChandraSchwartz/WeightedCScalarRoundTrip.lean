import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCAmbientRoundTrip
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCLowerRoundTrip
import Langlands.Representation.Plancherel.DynamicGalleryPointScalar

/-! # The scalar of the actual weighted c-family on a common regular region -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily StandardIntertwining DynamicCommonLeviComposition
  DynamicCommonLeviCompact DynamicCommonLeviContinuation ActualCommonLeviTensor
  DynamicOppositeCanonicalScalar ActualCommonLeviV3 ActualCommonLeviCompactTensor
  DynamicCommonLeviPresentations

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance cMainRTAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance cMainRTLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cMainRTLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance cMainRTLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  ActualCommonLeviV3.leviLocallyCompact ActualCommonLeviV3.leviMeasurable ActualCommonLeviV3.leviBorel

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance cMainRTPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "χ" => χG ≫ (G.innerIso (n : rationalPoints G)).hom
local notation "m" => (n : rationalPoints G)
local notation "L" => parameterScheme χ
local notation "M" => RationalPointFamily.levi i ν I
local notation "fM" => leviRationalPointHomeomorph i ν I
local notation "eG" => standardLeviDynamicHomeomorph hG hi hν I hζ
local notation "cg" => leviConjugation χG m
local notation "e₁" => standardLeviParameterIso hG hi hν I hζ
local notation "e₂" => parameterConjugationIso χG m
local notation "eL" => lowerParameterIso hG hi hν I I' hζ n hn
local notation "eI" => auxiliaryInnerParameterIso hG hi hν I I' hζ hζ' n hn
local notation "b" => lowerCocharacter i ν (rootSet i ν I') ζ n
local notation "j₀" => Standard.leviHom i ν (rootSet i ν I)
local notation "j₁" => Standard.leviHom i ν (rootSet i ν I')
local notation "e_s" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
local notation "eIpt" => auxiliaryInnerLeviEquiv hG hi hν I I' hζ hζ' n hn

local notation "f" => weightedCParameterIso hG hi hν I hζ n
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
local notation "Φ" => unramifiedCharactersHomeomorph fM ν₀
local notation "liftParam" => rationalUnramifiedCharacterRestrict (f).hom
local notation "τ" => rationalUnramifiedCharacterRestrict (eI).hom
local notation "δG" => rationalUnramifiedCharacterRestrict (e₂).hom
local notation "Z" => unramifiedCharacters (normCharacters χ)
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "GR" => unramifiedRegularFunctions (normCharacters χG)
local notation "LR" => unramifiedRegularFunctions (normCharacters b)
local notation "hp" => parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "Frac" => rationalUnramifiedFunctionField L hp hL
local notation "φ" => algebraMap R Frac
local notation "E" => rationalUnramifiedRegularFunctionsEquiv (e₂)
local notation "E'" => rationalUnramifiedFunctionFieldEquiv (parameterProjection_continuous χG)
  (parameterScheme_isConnectedReductive χG hG) hp hL (e₂)
local notation "tG" => lowerAmbient_isConnectedReductive hG hi hν I'

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u}) (hCST : CentralSplitTorusCharacterStatement.{u})
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))

local notation "A₀" => SmoothRep.pullback eG π.obj
local notation "A" => conjugateRepresentation χG m A₀
local notation "B" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj

variable (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG A₀)
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel

local notation "θ₀" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
local notation "eχ" => weightedC_conjugatedCocharacter_eq (i := i) (ζ := ζ) n
local notation "Vertex" => GalleryVertex χ


local notation "θ" => (⟨χ, rfl⟩ : Vertex)
local notation "x" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn ζ'
  (outerCentralizer_pos hG hi hν I' hζ')
local notation "y" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn (-ζ')
  (outerCentralizer_neg hG hi hν I' hζ')
local notation "ox" => GalleryVertex.opposite x
local notation "oθ" => GalleryVertex.opposite θ
local notation "V" => ({θ, oθ, x, ox, y} : Finset Vertex)

variable (iw : ∀ (v : Vertex) (g : rationalPoints G), ∃ p : parabolic v.val, ∃ k : K,
  g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : CompactContinuationSystem χ hG A K hK iw)

local notation "J[" v "," w "," z "]" => compactContinuationValue χ hG A K hK iw p v w z
local notation "R[" v "," w "]" => (p v w).regularRegion
local notation "U[" v "," z "]" => UnramifiedLeviInduction
  (commonDecomposition χ (v : Vertex).val (v : Vertex).property) (radical_isClosed (v : Vertex).val)
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "gConst" => (RationalPlancherelDensity.plancherelDensityConstant i ζ PG.K PG.hK : ℂ)
local notation "lConst" => (RationalPlancherelDensity.plancherelDensityConstant
  (Standard.leviTorusHom i ν (rootSet i ν I')) (conjugatedCocharacter i ζ n) PM.K PM.hK : ℂ)

local notation "Gδ" => weightedCAmbientDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "Lδ" => weightedCLowerDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  {sc : Tc.toGrp ⟶ L} (hs : IsSplitComponent sc)
  (hIr : (A).IsIrreducible) (hAd : (A).IsAdmissible)

local notation "AllRegular" => fun w : Z => ∀ v ∈ V, ∀ v' ∈ V, w ∈ R[v,v']

local notation "χs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I')


include hG hi hν hζ hζ' hn K hK iw p in
/-- The regular region of all ordered pairs among the five vertices, cut
by one nonzero regular function, is dense open on the unitary parameters. -/
theorem weightedC_commonRegion [DecidableEq Vertex] (e : R) (he : e ≠ 0) :
    ∃ S : Set Z, IsDenseOpenUnitaryRegion L S ∧ ∀ w ∈ S, AllRegular w ∧ e.val w ≠ 0 := by
  have hD₁ : IsDenseOpenUnitaryRegion L (⋂ v ∈ V, ⋂ w ∈ V, R[v,w]) := by
    apply isDenseOpenUnitaryRegion_biInter L
    intro v _
    apply isDenseOpenUnitaryRegion_biInter L
    intro w _
    exact isDenseOpenUnitaryRegion_nonzero L hL (p v w).presentation.denominator
      ((p v w).presentation.denominator_ne_zero (p v w).nonempty_region)
  refine ⟨(⋂ v ∈ V, ⋂ w ∈ V, R[v,w]) ∩ {w : Z | e.val w ≠ 0},
    hD₁.inter L (isDenseOpenUnitaryRegion_nonzero L hL e he), fun w hw => ⟨?_, hw.2⟩⟩
  exact fun v hv u hu => Set.mem_iInter.mp
    (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hw.1 v) hv) u) hu

set_option linter.unusedSectionVars false in
/-- Splitting the nonvanishing of the product used for the common region. -/
theorem weightedC_eight_ne_zero (Mden Gnum Gden Mnum c₀ c₁ cx cy : R) (w : Z)
    (hw : (((Mden * Gnum) * (Gden * (Mnum * (c₀ * c₁)))) * (cx * cy)).val w ≠ 0) :
    Mden.val w ≠ 0 ∧ Gnum.val w ≠ 0 ∧ Gden.val w ≠ 0 ∧
      Mnum.val w ≠ 0 ∧ c₀.val w ≠ 0 ∧ c₁.val w ≠ 0 ∧ cx.val w ≠ 0 ∧ cy.val w ≠ 0 := by
  have hw' : ((Mden.val w * Gnum.val w) * (Gden.val w * (Mnum.val w * (c₀.val w * c₁.val w)))) *
      (cx.val w * cy.val w) ≠ 0 := hw
  simp only [mul_ne_zero_iff] at hw'
  exact ⟨hw'.1.1.1, hw'.1.1.2, hw'.1.2.1, hw'.1.2.2.1, hw'.1.2.2.2.1, hw'.1.2.2.2.2,
    hw'.2.1, hw'.2.2⟩

set_option linter.unusedSectionVars false in
/-- The value of the cleared density-ratio fraction. -/
theorem weightedC_ratio_value (k : ℂ) (Mden Gnum Gden Mnum : R) (w : Z) (hmD : Mden.val w ≠ 0)
    (hgN : Gnum.val w ≠ 0) (hgD : Gden.val w ≠ 0) :
    (algebraMap ℂ R k * (Mnum * Gden)).val w / (Mden * Gnum).val w =
      k * ((Mnum.val w / Mden.val w) / (Gnum.val w / Gden.val w)) := by
  change k * (Mnum.val w * Gden.val w) / (Mden.val w * Gnum.val w) = _
  field_simp [hmD, hgN, hgD]

include hG hi hν hζ hζ' hn K hK iw p in
set_option maxHeartbeats 12000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- At one parameter of the common region, the outer round trip times the
cleared density ratio is the fixed constant. -/
theorem weightedC_roundTrip_point [Nontrivial A] [DecidableEq Vertex] (s t₀ t₁ k : ℂ)
    (ht₁ : t₁ ≠ 0) (Gnum Gden Mnum Mden c₀ c₁ : R)
    (hθ : ∀ w : Z, w ∈ R[θ,oθ] → w ∈ R[oθ,θ] → c₀.val w ≠ 0 →
      Gden.val w ≠ 0 ∧ (J[oθ,θ,w]).comp (J[θ,oθ,w]) = (t₀ * (Gnum.val w / Gden.val w)) • LinearMap.id)
    (hlow : ∀ w : Z, w ∈ R[y,ox] → w ∈ R[ox,y] → c₁.val w ≠ 0 → ∀ si : ℂ,
      (J[ox,y,w]).comp (J[y,ox,w]) = si • LinearMap.id → si = t₁ * (Mnum.val w / Mden.val w))
    (hsProd : ∀ z : Z, AllRegular z → Function.Surjective (J[y,x,z]) →
      ∀ sθ sx si so : ℂ,
        (J[oθ,θ,z]).comp (J[θ,oθ,z]) = sθ • LinearMap.id →
        (J[ox,x,z]).comp (J[x,ox,z]) = sx • LinearMap.id →
        (J[ox,y,z]).comp (J[y,ox,z]) = si • LinearMap.id →
        (J[x,y,z]).comp (J[y,x,z]) = so • LinearMap.id →
        so * si = s * sθ)
    (w : Z) (hAll : AllRegular w) (hx : (U[x,w]).IsIrreducible) (hy : (U[y,w]).IsIrreducible)
    (hgN : Gnum.val w ≠ 0) (hc₀w : c₀.val w ≠ 0) (hc₁w : c₁.val w ≠ 0) :
    ∃ j : ℂ, (J[x,y,w]).comp (J[y,x,w]) = j • LinearMap.id ∧
      (k * ((Mnum.val w / Mden.val w) / (Gnum.val w / Gden.val w))) * j = k * ((s * t₀) / t₁) := by
  have hvθ : θ ∈ V := by simp
  have hvoθ : oθ ∈ V := by simp
  have hvy : y ∈ V := by simp
  have hvox : ox ∈ V := by simp
  obtain ⟨hgDw, hθcomp⟩ := hθ w (hAll θ hvθ oθ hvoθ) (hAll oθ hvoθ θ hvθ) hc₀w
  obtain ⟨si, j, hsi, hj, hprod⟩ := gallery_roundTrip_point_product χ hG A K hK iw p θ x y
    s hsProd w hAll hx hy _ hθcomp
  rw [hlow w (hAll y hvy ox hvox) (hAll ox hvox y hvy) hc₁w si hsi] at hprod
  refine ⟨j, hj, ?_⟩
  exact weight_mul_roundTrip_of_scalar_product (div_ne_zero hgN hgDw)
    (hprod.trans (mul_assoc _ _ _).symm) ht₁ k

include hIr hAd hs hN in
set_option maxHeartbeats 12000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact package density ratio cancels the outer round-trip scalar on
an ambient open set that is dense also on the unitary parameters. Its
regular fraction agrees with the actual weight on their common domain. -/
theorem exists_weightedCScalar_roundTrip [Nontrivial A] [DecidableEq Vertex]
    (hPG : PG.canonicalScalar ≠ 0) (hPM : PM.canonicalScalar ≠ 0)
    (hix : ∃ c : R, c ≠ 0 ∧ ∀ w : Z, c.val w ≠ 0 → (U[x,w]).IsIrreducible)
    (hiy : ∃ c : R, c ≠ 0 ∧ ∀ w : Z, c.val w ≠ 0 → (U[y,w]).IsIrreducible) :
    ∃ (a d : R) (S : Set Z) (κ : ℂ), d ≠ 0 ∧ IsDenseOpenUnitaryRegion L S ∧
      (∀ w ∈ S, AllRegular w ∧ d.val w ≠ 0 ∧ (U[x,w]).IsIrreducible ∧ (U[y,w]).IsIrreducible ∧
        ∃ j : ℂ, (J[x,y,w]).comp (J[y,x,w]) = j • LinearMap.id ∧ (a.val w / d.val w) * j = κ) ∧
      (∀ z : unramifiedCharacters ν₀, ∀ hz : (Φ) z ∈ D₀, (liftParam) z ∈ S →
        Gδ ⟨(Φ) z, hz⟩ * (Lδ ⟨(Φ) z, hz⟩)⁻¹ = a.val ((liftParam) z) / d.val ((liftParam) z)) := by
  obtain ⟨Gnum, Gden, c₀, t₀, ht₀, hGnum, hGden, hc₀, hθ, hGδ⟩ :=
    exists_weightedC_ambientRoundTrip hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM iw p hPG
  obtain ⟨Mnum, Mden, c₁, t₁, ht₁, hMnum, hMden, hc₁, hlow, hLδ⟩ :=
    exists_weightedC_lowerRoundTrip hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM hN iw p hPM
  obtain ⟨s, _, hsProd⟩ := exists_gallery_roundTrip_product χ hG A K hK iw p hs θ x y hIr hAd
  have hm : lConst ≠ 0 :=
    packageDensityConstant_ne_zero PM (lowerTorus_isMaximalSplitTorus hi I').1.1
  obtain ⟨cx, hcx, hcxx⟩ := hix
  obtain ⟨cy, hcy, hcyy⟩ := hiy
  have he : ((Mden * Gnum) * (Gden * (Mnum * (c₀ * c₁)))) * (cx * cy) ≠ 0 :=
    weightedC_regular_mul_ne_zero hG n
      (weightedC_regular_mul_ne_zero hG n (weightedC_regular_mul_ne_zero hG n hMden hGnum)
        (weightedC_regular_mul_ne_zero hG n hGden (weightedC_regular_mul_ne_zero hG n hMnum
          (weightedC_regular_mul_ne_zero hG n hc₀ hc₁))))
      (weightedC_regular_mul_ne_zero hG n hcx hcy)
  obtain ⟨S, hS, hSw⟩ := weightedC_commonRegion hG hi hν I I' hζ hζ' n hn K hK π iw p _ he
  refine ⟨algebraMap ℂ R (gConst / lConst) * (Mnum * Gden), Mden * Gnum, S,
    (gConst / lConst) * (((s : ℂ) * (t₀ : ℂ)) / (t₁ : ℂ)),
    weightedC_regular_mul_ne_zero hG n hMden hGnum, hS, ?_, ?_⟩
  · intro w hw
    obtain ⟨hAll, hew⟩ := hSw w hw
    obtain ⟨hmD, hgN, hgD, -, hc₀w, hc₁w, hxirr, hyirr⟩ :=
      weightedC_eight_ne_zero n Mden Gnum Gden Mnum c₀ c₁ cx cy w hew
    have hx : (U[x,w]).IsIrreducible := hcxx w hxirr
    have hy : (U[y,w]).IsIrreducible := hcyy w hyirr
    obtain ⟨j, hj, hk⟩ := weightedC_roundTrip_point hG hi hν I I' hζ hζ' n hn K hK π iw p
      (s : ℂ) (t₀ : ℂ) (t₁ : ℂ) (gConst / lConst) (by exact_mod_cast ht₁.ne')
      Gnum Gden Mnum Mden c₀ c₁ hθ hlow hsProd w hAll hx hy hgN hc₀w hc₁w
    refine ⟨hAll, mul_ne_zero hmD hgN, hx, hy, j, hj, ?_⟩
    rw [weightedC_ratio_value n _ Mden Gnum Gden Mnum w hmD hgN hgD]
    exact hk
  · intro z hz hw
    obtain ⟨hAll, hew⟩ := hSw _ hw
    obtain ⟨hmD, hgN, hgD, hmN, -⟩ :=
      weightedC_eight_ne_zero n Mden Gnum Gden Mnum c₀ c₁ cx cy _ hew
    rw [hGδ z hz hgN, hLδ z hz hmN, weightedC_ratio_value n _ Mden Gnum Gden Mnum _ hmD hgN hgD]
    field_simp [hm, hmD, hgN, hgD, hmN]

end Langlands.HarishChandraSchwartz.WeakExpansion
