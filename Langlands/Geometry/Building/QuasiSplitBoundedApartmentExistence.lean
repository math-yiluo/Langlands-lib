import Langlands.Geometry.Building.TorusFieldRestrictedFiltrationBounds
import Langlands.Geometry.Building.SplitApartmentFiltrationBounds
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.QuasiSplitIntegerBoundedApartmentExistenceStatement

/-! # Bounded quasi-split apartments over henselian discretely valued fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

private instance quasiSplitBoundsAffine {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Integer-value surjectivity provides normalized extension values below every
real threshold, without a completeness or residue-field assumption. -/
theorem exists_henselianSeparableAddValuation_le
    {k : Type u} [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
    (hH : HenselianLocalRing v.valuationSubring)
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (hv : Function.Surjective v) (r : ℝ) :
    ∃ b : K, b ≠ 0 ∧ FieldTheory.henselianSeparableAddValuation v hH K b ≤ (r : WithTop ℝ) := by
  obtain ⟨n, hn⟩ := exists_int_le r
  obtain ⟨b, hb⟩ := hv (WithZero.exp (-n))
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact WithZero.zero_ne_coe hb
  refine ⟨algebraMap k K b, (map_ne_zero (algebraMap k K)).mpr hb0, ?_⟩
  rw [FieldTheory.henselianSeparableAddValuation_base v hH K hb0,
    hb, WithZero.log_exp, neg_neg, WithTop.coe_le_coe]
  exact hn

section Assembly

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [ValuativeRel k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (t : S ⟶ T) (jT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- The existing split-apartment descent construction admits algebraically bounded
filtrations at every point and real depth, with full centralizer compatibility. -/
theorem exists_bounded_isOmegaCompatible_of_descent
    (hR2 : QuasiSplitMultipliableOppositeStatement.{u})
    [FiniteDimensional k K] [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom] [LocallyOfFiniteType G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible] (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hit : CommGroupScheme.groupHom t ≫ jT = i) (hjc : IsClosedSubgroup jT)
    (hj : (torusCentralizer i).IsRepresentedBy jT)
    (hT : IsSplitTorus (T_K).toGrp) (hjK : IsMaximalTorus (T := T_K) j_K)
    (hbij : Function.Bijective (Cartan.restrictionEvaluation (CommGroupScheme.groupHom t))) :
    ∃ (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i),
      IntegerValuation.IsOmegaCompatible v D C ∧
        ∀ (x : D.Apartment) a, a ∈ relativeRoots i → ∀ r : ℝ,
          IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G)) := by
  classical
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  have hGK : IsConnectedReductive G_K := hG.baseChange_of_algebraicExtension (K := K)
  have : IsClosedImmersion (j_K).hom.hom.left := hjK.2.1
  have : Mono (j_K).hom.hom.left := inferInstance
  have hfactor : CommGroupScheme.groupHom t_K ≫ j_K = i_K := by
    rw [← hit, Functor.map_comp]
    rfl
  have : Mono (CommGroupScheme.groupHom t_K ≫ j_K).hom.hom.left := by
    rw [hfactor]
    infer_instance
  have hjKmax : IsMaximalSplitTorus (T := T_K) j_K := hjK.isMaximalSplitTorus hT
  have hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs (T := T_K) j_K hT).mp
      (rootRankOneFactorization K G_K hGK T_K j_K hjKmax)
  have hEbase : RelativeRoot.HasOppositeFactorPairs i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs i hS).mp
      (rootRankOneFactorization k G hG S i hi)
  obtain ⟨J, _, P, hP, hred⟩ := rootDatumExistence K G_K hGK T_K hT j_K hjK
  -- the upper order
  let ωK := henselianUnitsOrder v hH K
  let ω : Kˣ → ℝ := fun x => (ωK x).toAdd
  have hadd : ∀ x y : Kˣ, ω (x * y) = ω x + ω y := fun x y => by
    simp only [ω, map_mul, toAdd_mul]
  have hωσ : ∀ (σ : K ≃ₐ[k] K) (x : Kˣ), ω (Units.map σ.toMonoidHom x) = ω x := fun σ x => by
    simp only [ω, ωK, henselianUnitsOrder_galois]
  have hωext : ∀ x : kˣ, ω (Units.map (algebraMap k K).toMonoidHom x) = IntegerValuation.order v x :=
    henselianUnitsOrder_algebraMap v hH K
  -- the split apartment and a Galois-fixed point
  let DK : KPApartmentData (S := T_K) j_K ω :=
    KPApartmentData.ofSplitMaximalTorus G_K hGK T_K hT j_K hjK
      (FieldTheory.henselianSeparableAddValuation v hH K) ω
      (henselianUnitsOrder_coe v hH K)
      (three_le_encard_range_henselianSeparableAddValuation v hH K hv)
  have hD := KPApartmentData.galoisStable_of_isSplitTorus k K jT hGK hT hjK hadd hωσ DK
  let x := KPApartmentData.galoisFixedPoint k K jT DK hD
  have hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val :=
    KPApartmentData.galoisAction_galoisFixedPoint k K jT DK hD
  -- structural facts about the centralizer torus
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsClosedImmersion jT.hom.hom.left := hjc
  have : Mono jT.hom.hom.left := inferInstance
  have hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ jT) := hit ▸ hi
  have hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ jT)).IsRepresentedBy jT :=
    hit ▸ hj
  have ht : IsLargestSplitSubtorus (CommGroupScheme.groupHom t) :=
    (hf.of_comp hjc).isLargestSplitSubtorus
  have hnorm : ∀ n : normalizerPoints i, (n : rationalPoints G) ∈ normalizerPoints jT :=
    mem_normalizerPoints_of_torusCentralizer i jT hj
  have hzero : ∀ ψ ∈ relativeRoots (T := T_K) j_K, t_K ≫ ψ ≠ 0 := fun ψ hψ =>
    root_restrict_ne_zero_of_torusCentralizer k K t jT hS hT hcent ⟨ψ, hψ⟩
  have horbit : ∀ (c : characterLattice S),
      ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ ψ ∈ relativeRoots (T := T_K) j_K,
      t_K ≫ χ = (a_K c) → t_K ≫ ψ = (a_K c) →
      ∃ σ : K ≃ₐ[k] K, characterLattice.galoisRepresentation k K T σ χ = ψ := by
    intro c χ hχ ψ hψ hχc hψc
    have hβ : (⟨χ, hχ⟩ : roots (T := T_K) j_K) ∈ rootRestrictionFiber k K jT t c := hχc
    have horb := rootOrbit_eq_restrictionFiber_of_torusCentralizer k K t jT hf hjc hcent hT hP c hβ
    have hmem : (⟨ψ, hψ⟩ : roots (T := T_K) j_K) ∈ MulAction.orbit (K ≃ₐ[k] K)
        (⟨χ, hχ⟩ : roots (T := T_K) j_K) := by
      rw [horb]
      exact hψc
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hmem
    exact ⟨σ, congrArg Subtype.val hσ⟩
  -- original-point shifts and V 5
  have hshift := torusFieldOriginalPointShifts_of_galoisFixed i t jT hS hT hE DK x hfix hfactor ht
    hnorm
  have hopposite : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints i (-a), ∀ g'' ∈ rootGroupPoints i (-a),
        g' * g * g'' ∈ normalizerPoints i →
          torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE
              x.isValuation t_K (-a) g' +
            torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE
              x.isValuation t_K a g = 0 := by
    intro a ha g hg hg1 g' hg' g'' hg'' hN
    by_cases h2a : (2 : ℤ) • a ∈ relativeRoots i
    · have h2a' : 2 • a ∈ relativeRoots i := by
        rwa [two_zsmul, ← two_nsmul] at h2a
      exact hR2 k K S T G t jT i hS hT hG hi hit hjc hj hGK hjK hE ω DK x hfix hfactor P hP hred
        a ha h2a' g hg hg1 g' hg' g'' hg'' hN
    · exact torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem t jT i hS hT hE
        x.isValuation hfix hfactor hP hzero hnorm hEbase ha h2a (horbit a) hg hg1 hg' hg'' hN
  -- the descended valuation
  let ψ := torusFieldRestrictedValuationOfOriginalPointShifts i hS hT hE x.isValuation t_K
    hfactor hEbase ωK x.isSplitTorusCompatible ?hω hshift hopposite
  case hω =>
    obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.zero_ne_coe hπ
    refine ⟨Units.mk0 π hπ0, ?_⟩
    change ω (Units.map (algebraMap k K).toMonoidHom (Units.mk0 π hπ0)) ≠ 0
    rw [hωext, IntegerValuation.order, IntegerValuation.orderUnits_toAdd, Units.val_mk0, hπ,
      WithZero.log_exp]
    norm_num
  have hcompat : IsSplitTorusCompatible i (IntegerValuation.order v) ψ.1 := by
    have h := torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible i hS hT hE
      x.isValuation t_K hfactor ωK x.isSplitTorusCompatible
    have he : (fun t => (ωK (Units.map (algebraMap k K).toMonoidHom t)).toAdd) =
        IntegerValuation.order v := funext hωext
    rw [he] at h
    exact h
  have hN : ∀ n : normalizerPoints i, ∃ w : V S, n • ψ.1 = w +ᵥ ψ.1 :=
    (torusFieldOriginalPointShifts_iff i hS hT hE x.isValuation t_K hfactor).mp hshift
  let D := KPApartmentData.ofNormalizerShifts (IntegerValuation.order v) ψ.1 ψ.2 hcompat hN
  let C : CentralizerDatum i :=
    { Z := T.toGrp
      j := jT
      s := CommGroupScheme.groupHom t
      isClosedSubgroup := hjc
      isRepresentedBy := hj
      comp_eq := hit
      bijective := hbij }
  have hBψ : ∀ a ∈ relativeRoots i, ∀ r : ℝ,
      IsAlgebraicallyBounded k G.X (rootFiltration i ψ.1 a r) := by
    let e := henselianSeparableCofinalValuativeExtension v hH hv (K := K)
    let := e.relation
    let := e.extension
    have hBK : ∀ a ∈ relativeRoots (T := T_K) j_K, ∀ r : ℝ,
        IsAlgebraicallyBounded K (G_K).X (rootFiltration j_K x.val a r) := by
      intro a ha r
      exact DK.isAlgebraicallyBounded_filtration_of_isSplitTorus G_K hGK T_K hT j_K hjK
        (FieldTheory.henselianSeparableAddValuation v hH K) ω
        (henselianUnitsOrder_coe v hH K)
        (three_le_encard_range_henselianSeparableAddValuation v hH K hv)
        (henselianSeparableCofinalValuativeExtension_vle_iff v hH hv)
        (exists_henselianSeparableAddValuation_le v hH K hv) x a ha r
    intro a ha r
    exact isAlgebraicallyBounded_rootFiltration_torusFieldRestrict i hS hT hE
      x.isValuation e.cofinal t_K hfactor hBK a ha r
  refine ⟨D, C, ?_, KPApartmentData.isAlgebraicallyBounded_filtration_of_orbit D ψ.1 rfl hBψ⟩
  have hψD : ψ.1 ∈ D.carrier := AddAction.mem_orbit_self ψ.1
  refine (IntegerValuation.isOmegaCompatible_iff_of_mem hψD).mpr ?_
  exact torusFieldRestricted_isCentralizerCompatible i t jT v hS hT hE hadd hωσ hωext
    x.isValuation x.isSplitTorusCompatible hfactor ht hj hbij

end Assembly

/-- Full centralizer-compatible quasi-split apartments with bounds at every depth. -/
def QuasiSplitAllDepthBoundedApartmentExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible],
    Function.Surjective v → HenselianLocalRing v.valuationSubring →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∃ (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i),
          IntegerValuation.IsOmegaCompatible v D C ∧
            ∀ (x : D.Apartment) a, a ∈ relativeRoots i → ∀ r : ℝ,
              IsAlgebraicallyBounded k G.X (D.filtration x a r : Set (rationalPoints G))

/-- Construct the actual centralizer torus, split it over a finite Galois extension,
and descend the bounded split apartment. -/
theorem quasiSplitAllDepthBoundedApartmentExistence :
    QuasiSplitAllDepthBoundedApartmentExistenceStatement.{u} := by
  intro k _ _ v _ hv hH G _ hQS S i hi
  have := mono_of_isMaximalSplitTorus hi
  have hGr := hQS.isConnectedReductive
  have : Smooth G.X.hom := hGr.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨Z, j, hj, hjc⟩ := fieldCentralizerRepresentability k S G hi.1.1.isAffineHom i
  have hZ : IsTorus Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hQS hi hj
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { Z with comm := hZ.isCommMonObj }
  let jT : T.toGrp ⟶ G := j
  let t : S ⟶ T := Additive.ofMul (torusCentralizerFactor i hj)
  have : IsAffineHom T.toGrp.X.hom := hjc.isAffineHom
  have : LocallyOfFiniteType T.toGrp.X.hom := hjc.locallyOfFiniteType
  have hit : CommGroupScheme.groupHom t ≫ jT = i := torusCentralizerFactor_comp i hj
  have hself : torusCentralizer jT = SubgroupFunctor.range jT :=
    le_antisymm ((torusCentralizer_le_of_factor jT i (torusCentralizerFactor i hj)
      (torusCentralizerFactor_comp i hj)).trans hj.2.symm.le) (range_le_torusCentralizer jT)
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z hZ
  have hjK := isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself
  have hbij := Cartan.restrictionEvaluation_bijective_of_torusCentralizer hGr hi hjc hj hit
  exact exists_bounded_isOmegaCompatible_of_descent i t jT quasiSplitMultipliableOpposite
    v hv hH hGr hi hit hjc hj hK hjK hbij

/-- The all-depth construction implies the depth-zero bounded-existence interface. -/
theorem quasiSplitIntegerBoundedApartmentExistence :
    QuasiSplitIntegerBoundedApartmentExistenceStatement.{u} := by
  intro k _ _ v _ hv hH G _ hQS S i hi
  obtain ⟨D, C, hC, hB⟩ :=
    quasiSplitAllDepthBoundedApartmentExistence k v hv hH G hQS S i hi
  exact ⟨D, C, hC, fun x a ha => hB x a ha 0⟩

end Langlands.Geometry.Building
