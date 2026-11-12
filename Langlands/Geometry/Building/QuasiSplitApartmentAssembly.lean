import Langlands.Geometry.Building.QuasiSplitApartmentOpposite
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.FieldCentralizerRepresentabilityProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation

/-! # Assembly of the quasi-split apartment from the opposite-pair axiom at multipliable roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

/-- **The opposite-pair axiom at multipliable roots for the descended family.** Let
`i = groupHom t ≫ jT` be a maximal split torus of a connected reductive group `G` over `k`,
where the closed subgroup `jT` represents the full centralizer of `i`. Let `K/k` be a finite
Galois extension splitting `T`, so that `j_K` is a split maximal torus of `G_K`, and let `x`
be a Galois-fixed point of a normalizer-stable apartment class of `j_K`. Then the
torus-then-field restriction of `x` satisfies axiom V 5 at every relative root `a` of `i`
such that `2 • a` is also a relative root. -/
def QuasiSplitMultipliableOppositeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (S T : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [LocallyOfFiniteType G.X.hom] [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [IsAffineHom (baseChanged k K G).X.hom] [Smooth (baseChanged k K G).X.hom]
    (t : S ⟶ T) (jT : T.toGrp ⟶ G) (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map jT).hom.hom.left]
    [Mono (CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap k K)).map t) ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map jT).hom.hom.left]
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp),
    IsConnectedReductive G → IsMaximalSplitTorus i → CommGroupScheme.groupHom t ≫ jT = i →
    IsClosedSubgroup jT → (torusCentralizer i).IsRepresentedBy jT →
    IsConnectedReductive (baseChanged k K G) →
    IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) →
    ∀ (hE : RelativeRoot.HasOppositeFactorPairs
        (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map jT))
      (ω : Kˣ → ℝ)
      (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) ω)
      (x : D.Apartment),
    (∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ x.val = x.val) →
    CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap k K)).map t) ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map jT =
      (GroupScheme.baseChange (algebraBaseMap k K)).map i →
    ∀ {J : Type u} [Finite J]
      (P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
        (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))),
    IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) P →
    P.IsReduced →
    ∀ a ∈ relativeRoots i, 2 • a ∈ relativeRoots i →
    ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
    ∀ g' ∈ rootGroupPoints i (-a), ∀ g'' ∈ rootGroupPoints i (-a),
    g' * g * g'' ∈ normalizerPoints i →
      torusFieldRestrictedRootFunctionFamily (G := G)
          (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (j := (GroupScheme.baseChange (algebraBaseMap k K)).map jT) hS hT hE x.isValuation
          ((CommGroupScheme.baseChange (algebraBaseMap k K)).map t) (-a) g' +
        torusFieldRestrictedRootFunctionFamily (G := G)
          (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (j := (GroupScheme.baseChange (algebraBaseMap k K)).map jT) hS hT hE x.isValuation
          ((CommGroupScheme.baseChange (algebraBaseMap k K)).map t) a g = 0

section Normalizer

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Normalizer points of a torus normalize every closed representative of its full
centralizer. -/
theorem mem_normalizerPoints_of_torusCentralizer (i : S.toGrp ⟶ G) (jT : T.toGrp ⟶ G)
    [Mono jT.hom.hom.left] (hj : (torusCentralizer i).IsRepresentedBy jT)
    (n : normalizerPoints i) : (n : rationalPoints G) ∈ normalizerPoints jT := by
  apply torusNormalizer_le_normalizerPoints jT
  change (n : rationalPoints G) ∈ (SubgroupFunctor.range jT).normalizer.carrier _
  rw [hj.2]
  intro V a y hy
  have hn : a ≫ (n : rationalPoints G) ∈ (torusNormalizer i).carrier V :=
    (torusNormalizer i).comp_mem a (normalizerPoints_le_torusNormalizer i n.2)
  have hinv := torusCentralizer_isNormalizedBy_torusNormalizer i V _ y
    (((torusNormalizer i).carrier V).inv_mem hn) hy
  rw [inv_inv] at hinv
  exact ⟨torusCentralizer_isNormalizedBy_torusNormalizer i V _ y hn hy, hinv⟩

end Normalizer

section Order

variable {k : Type u} [Field k] (v : Valuation k (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring) (K : Type u) [Field K] [Algebra k K]
  [Algebra.IsSeparable k K]

/-- The real order on `Kˣ` of the normalized henselian valuation of a separable extension
`K` of `k`. -/
def henselianUnitsOrder : Kˣ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd
    ((FieldTheory.henselianSeparableAddValuation v hH K (x : K)).untop
      ((FieldTheory.henselianSeparableAddValuation v hH K).ne_top_iff.mpr x.ne_zero))
  map_one' := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, toAdd_one, WithTop.untop_eq_iff, Units.val_one, AddValuation.map_one]
    rfl
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    rw [WithTop.untop_eq_iff, Units.val_mul, AddValuation.map_mul, WithTop.coe_add,
      WithTop.coe_untop, WithTop.coe_untop]

theorem henselianUnitsOrder_coe (x : Kˣ) :
    FieldTheory.henselianSeparableAddValuation v hH K (x : K) =
      (((henselianUnitsOrder v hH K x).toAdd : ℝ) : WithTop ℝ) := by
  simp only [henselianUnitsOrder, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    WithTop.coe_untop]

theorem henselianUnitsOrder_algebraMap (x : kˣ) :
    (henselianUnitsOrder v hH K (Units.map (algebraMap k K).toMonoidHom x)).toAdd =
      IntegerValuation.order v x := by
  have h := henselianUnitsOrder_coe v hH K (Units.map (algebraMap k K).toMonoidHom x)
  have h' : FieldTheory.henselianSeparableAddValuation v hH K
      ((Units.map (algebraMap k K).toMonoidHom x : Kˣ) : K) =
        (((-WithZero.log (v x) : ℤ) : ℝ) : WithTop ℝ) :=
    FieldTheory.henselianSeparableAddValuation_base v hH K x.ne_zero
  rw [h', WithTop.coe_inj] at h
  rw [← h, IntegerValuation.order, IntegerValuation.orderUnits_toAdd]

theorem henselianUnitsOrder_galois (σ : K ≃ₐ[k] K) (x : Kˣ) :
    henselianUnitsOrder v hH K (Units.map σ.toMonoidHom x) = henselianUnitsOrder v hH K x := by
  apply Multiplicative.toAdd.injective
  have h1 := henselianUnitsOrder_coe v hH K (Units.map σ.toMonoidHom x)
  have h2 := henselianUnitsOrder_coe v hH K x
  rw [Units.coe_map] at h1
  change FieldTheory.henselianSeparableAddValuation v hH K (σ (x : K)) = _ at h1
  rw [FieldTheory.henselianSeparableAddValuation_invariant, h2, WithTop.coe_inj] at h1
  exact h1.symm

/-- The normalized henselian valuation takes at least three values. -/
theorem three_le_encard_range_henselianSeparableAddValuation (hv : Function.Surjective v) :
    3 ≤ (Set.range (FieldTheory.henselianSeparableAddValuation v hH K)).encard := by
  obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  have h1 : FieldTheory.henselianSeparableAddValuation v hH K (algebraMap k K π) =
      ((1 : ℝ) : WithTop ℝ) := by
    rw [FieldTheory.henselianSeparableAddValuation_base v hH K hπ0, hπ, WithZero.log_exp]
    norm_num
  have hsub : ({⊤, ((0 : ℝ) : WithTop ℝ), ((1 : ℝ) : WithTop ℝ)} : Set (WithTop ℝ)) ⊆
      Set.range (FieldTheory.henselianSeparableAddValuation v hH K) := by
    rintro y (rfl | rfl | rfl)
    · exact ⟨0, AddValuation.map_zero _⟩
    · exact ⟨1, AddValuation.map_one _⟩
    · exact ⟨_, h1⟩
  refine le_trans ?_ (Set.encard_le_encard hsub)
  rw [Set.encard_insert_of_notMem (by simp), Set.encard_insert_of_notMem (by norm_num),
    Set.encard_singleton]
  rfl

end Order

section Assembly

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
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

/-- **Descent of the split apartment, given V 5 at multipliable roots.** Let `K/k` be a finite
Galois extension splitting the closed torus `jT` that represents the full centralizer of the
maximal split torus `i = t ≫ jT` of a connected reductive group `G`. Then the
torus-then-field restriction of a Galois-fixed point of the split apartment of `(G_K, j_K)`
spans a normalizer-stable apartment class of `i` for the integer order of `v`, and this class
is centralizer compatible for the centralizer datum `(T, jT, t)`. -/
theorem exists_isOmegaCompatible_of_descent
    (hR2 : QuasiSplitMultipliableOppositeStatement.{u})
    [FiniteDimensional k K] [IsGalois k K]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom] [LocallyOfFiniteType G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hit : CommGroupScheme.groupHom t ≫ jT = i) (hjc : IsClosedSubgroup jT)
    (hj : (torusCentralizer i).IsRepresentedBy jT)
    (hT : IsSplitTorus (T_K).toGrp) (hjK : IsMaximalTorus (T := T_K) j_K)
    (hbij : Function.Bijective (Cartan.restrictionEvaluation (CommGroupScheme.groupHom t))) :
    ∃ (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i),
      IntegerValuation.IsOmegaCompatible v D C := by
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
  refine ⟨D, C, ?_⟩
  have hψD : ψ.1 ∈ D.carrier := AddAction.mem_orbit_self ψ.1
  refine (IntegerValuation.isOmegaCompatible_iff_of_mem hψD).mpr ?_
  exact torusFieldRestricted_isCentralizerCompatible i t jT v hS hT hE hadd hωσ hωext
    x.isValuation x.isSplitTorusCompatible hfactor ht hj hbij

end Assembly

/-- **Quasi-split apartments from V 5 at multipliable roots.** The task target
`QuasiSplitIntegerApartmentExistenceStatement` follows from
`QuasiSplitMultipliableOppositeStatement`. -/
theorem quasiSplitIntegerApartmentExistence_of_multipliableOpposite
    (hR2 : QuasiSplitMultipliableOppositeStatement.{u}) :
    QuasiSplitIntegerApartmentExistenceStatement.{u} := by
  intro k _ v hv hH G _ hQS S i hi
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
  exact exists_isOmegaCompatible_of_descent i t jT hR2 v hv hH hGr hi hit hjc hj hK hjK hbij

end Langlands.Geometry.Building
