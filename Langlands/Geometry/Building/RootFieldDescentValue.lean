import Langlands.Geometry.Building.SplitRootLineValue
import Langlands.Geometry.Building.RootFieldPointProduct
import Langlands.Geometry.Building.QuasiSplitApartmentAssembly
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.ApartmentClassGaloisComparison
import Langlands.Geometry.Building.RootFieldCoordinatesOfTorus

/-! # Values of the actual apartment on actual root-field points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "f_L" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "a_L" a => characterLattice.baseChange b S a

private instance rootFieldDescentAffine : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance rootFieldDescentSmooth : Smooth (G_L).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction orbitFintype

private instance rootFieldDescentSeparable
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    Algebra.IsSeparable k (rootOrbitField k L j β) :=
  Algebra.isSeparable_tower_bot_of_isSeparable k (rootOrbitField k L j β) L

/-- **Restricted values on actual root-field points.** Let `x_L` be a Galois-fixed point of
a normalizer-stable apartment class of the split maximal torus `j_L`, for the normalized
henselian order of `L`. On the actual root-field point of a nonzero element `x` of the
root field, the torus-then-field restriction of `x_L` is the normalized henselian value
of `x` plus a constant independent of `x`. -/
theorem exists_torusFieldRestricted_value_rootOrbitFieldPoint
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    [Mono (j_L).hom.hom.left]
    (hGL : IsConnectedReductive G_L) (hjL : IsMaximalTorus (T := T_L) j_L)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_L) j_L)
    (DK : KPApartmentData (S := T_L) j_L
      (fun x : Lˣ => (henselianUnitsOrder v hH L x).toAdd))
    (xK : DK.Apartment)
    (hfix : ∀ σ : L ≃ₐ[k] L, RootFunctionFamily.galoisAction k L T G σ xK.val = xK.val) :
    ∃ c : ℝ, ∀ x : rootOrbitField k L j β, x ≠ 0 →
      torusFieldRestrictedRootFunctionFamily (G := G) (T := T_L) (j := j_L) hS hT hE
          xK.isValuation f_L a
          (rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit x).val =
        FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β) x +
          ((c : ℝ) : WithTop ℝ) := by
  classical
  have hSL : IsSplitTorus (S_L).toGrp := hS.baseChange b
  have hfactor : CommGroupScheme.groupHom f_L ≫ j_L =
      CategoryTheory.Functor.map (GroupScheme.baseChange b)
        (CommGroupScheme.groupHom f ≫ j) := by
    rw [Functor.map_comp]
    rfl
  have haL : (a_L a) ∈ relativeRoots (T := S_L) (CommGroupScheme.groupHom f_L ≫ j_L) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := L) G S hS (CommGroupScheme.groupHom f ≫ j) a).mpr ha
  have hαL : (a_L a) ≠ 0 := haL.1
  have hhighL : ∀ χ ∈ relativeRoots (T := T_L) j_L, ∀ n : ℕ, 2 ≤ n →
      f_L ≫ χ ≠ n • (a_L a) := by
    intro χ hχ n hn h
    apply hhigh n hn
    have hmem : n • (a_L a) ∈ roots (T := S_L) (CommGroupScheme.groupHom f_L ≫ j_L) :=
      (mem_roots_comp_iff (T := T_L) (T' := S_L) hT hSL f_L j_L _).mpr
        ⟨hSL.nsmul_ne_zero hαL (by omega), χ, hχ, h⟩
    rw [hfactor, ← map_nsmul] at hmem
    exact (mem_roots_baseChange_iff (K := L) G S hS (CommGroupScheme.groupHom f ≫ j)
      (n • a)).mp hmem
  -- enumerate the orbit
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (Fin n ≃ MulAction.orbit (L ≃ₐ[k] L) β) :=
    ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
  let A : Fin n → characterLattice (T_L) := fun l => (e l).val.val
  have hinj : Function.Injective A := fun l m h =>
    e.injective (Subtype.ext (Subtype.ext h))
  have hrange : Set.range A =
      {χ | χ ∈ relativeRoots (T := T_L) j_L ∧ f_L ≫ χ = a_L a} := by
    ext χ
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨(e l).val.property, rootOrbit_restriction k L f j β horbit (e l)⟩
    · rintro ⟨hχ, hres⟩
      have hmem : (⟨χ, hχ⟩ : roots (T := T_L) (G := G_L) j_L) ∈
          MulAction.orbit (L ≃ₐ[k] L) β := by
        rw [horbit]
        exact hres
      obtain ⟨l, hl⟩ := e.surjective ⟨_, hmem⟩
      exact ⟨l, by simp only [A, hl]⟩
  have htrans : ∀ l m, ∃ σ : L ≃ₐ[k] L,
      characterLattice.galoisRepresentation k L T σ (A l) = A m := by
    intro l m
    obtain ⟨σ₁, h₁⟩ := MulAction.mem_orbit_iff.mp (e l).property
    obtain ⟨σ₂, h₂⟩ := MulAction.mem_orbit_iff.mp (e m).property
    refine ⟨σ₂ * σ₁⁻¹, ?_⟩
    have h : (σ₂ * σ₁⁻¹) • (e l).val = (e m).val := by
      rw [← h₁, ← h₂, smul_smul, inv_mul_cancel_right]
    exact congrArg Subtype.val h
  have hn : 0 < n := (e.symm ⟨β, MulAction.mem_orbit_self β⟩).pos
  let l₀ : Fin n := ⟨0, hn⟩
  -- the split value formula at the root `A l₀`
  obtain ⟨c, hc⟩ := exists_rootLine_value_of_isSplitTorus G_L hGL T_L hT j_L hjL
    (FieldTheory.henselianSeparableAddValuation v hH L)
    (fun x : Lˣ => (henselianUnitsOrder v hH L x).toAdd)
    (henselianUnitsOrder_coe v hH L)
    (three_le_encard_range_henselianSeparableAddValuation v hH L hv) DK
    (e l₀).val.property (e l₀).val.property.1
    (rootOrbit_hasNoHigherRoots k L f j hS hT ha.1 hhigh β horbit (e l₀))
    (rootOrbitLineEquiv k L j hG hj hT β (e l₀)) xK.mem
  refine ⟨c, fun x hx => ?_⟩
  let X : ∀ l, (RelativeRoot.subgroup (S := T_L) j_L (A l)).carrier (Over.mk (𝟙 _)) :=
    fun l => rootOrbitPointEquiv k L f j hG hj hS hT ha.1 hhigh β horbit (e l)
      (Multiplicative.ofAdd (rootOrbitEmbeddingEquiv k L j β (e l) x))
  have hX : RelativeRoot.rootPointsProduct (T := T_L) j_L A (Over.mk (𝟙 _)) X =
      rationalExtend k L G
        (rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit x).val :=
    (rootOrbitFieldPoint_fieldExtend_eq_product k L f j hG hj hS hT ha.1 hhigh β horbit
      e x).symm
  have hcoord : ∀ l, xK.val (A l) (X l).val = xK.val (A l₀) (X l₀).val := by
    intro l
    obtain ⟨σ, hσ⟩ := htrans l₀ l
    exact fiber_coordinate_value_eq_of_galois f j hS hT hE hfix hαL hhighL A hinj hrange X hX
      σ hσ
  have h0 : xK.val (A l₀) (X l₀).val =
      FieldTheory.henselianSeparableAddValuation v hH L
        (rootOrbitEmbeddingEquiv k L j β (e l₀) x) + ((c : ℝ) : WithTop ℝ) :=
    hc (rootOrbitEmbeddingEquiv k L j β (e l₀) x)
  have hval : FieldTheory.henselianSeparableAddValuation v hH L
      (rootOrbitEmbeddingEquiv k L j β (e l₀) x) =
      FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β) x :=
    FieldTheory.henselianSeparableAddValuation_algHom v hH L
      (rootOrbitEmbeddingEquiv k L j β (e l₀)) x
  have hne : FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β) x ≠ ⊤ :=
    (FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β)).ne_top_iff.mpr hx
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  have hc' : ∀ l, xK.val (A l) (X l).val = ((t + c : ℝ) : WithTop ℝ) := by
    intro l
    rw [hcoord l, h0, hval, ← ht, WithTop.coe_add]
  have hpos := torusRestrictedRootFunctionFamily_eq_of_coordinates (S := S_L) (T := T_L)
    hSL hT hE xK.isValuation f_L haL hhighL hn A hinj hrange X (t + c) hc'
  rw [hX] at hpos
  simp only [torusFieldRestrictedRootFunctionFamily, RootFunctionFamily.fieldRestrict_apply]
  rw [hpos, ← ht, WithTop.coe_add]

/-- **Values of the actual apartment on actual root-field points.** Let `i = f ≫ j` be a
maximal split torus of a connected reductive group `G`, where the closed maximal torus `j`
represents the full centralizer of `i` and is split by the finite Galois extension `L/k`.
Let `D` be a normalizer-stable apartment class of `i` for the integer order of `v`, satisfying
axiom V 6 for some centralizer datum. For every point `y` of `D` and every relative root `a`
with no higher multiples, the value of `y` on the actual root-field point of `x` is the
normalized henselian value of `x` plus a constant independent of `x`. -/
theorem exists_apartment_value_rootOrbitFieldPoint
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (hit : CommGroupScheme.groupHom f ≫ j = i) (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer i).IsRepresentedBy j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hjL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i)
    (hD : IntegerValuation.IsOmegaCompatible v D C) (y : D.Apartment) :
    ∃ c : ℝ, ∀ x : rootOrbitField k L j β,
      y.val a (rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit x).val =
        FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β) x +
          ((c : ℝ) : WithTop ℝ) := by
  classical
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have hGL : IsConnectedReductive G_L := hG.baseChange_of_algebraicExtension (K := L)
  have : IsClosedImmersion (j_L).hom.hom.left := hjL.2.1
  have : Mono (j_L).hom.hom.left := inferInstance
  have hfactor : CommGroupScheme.groupHom f_L ≫ j_L =
      CategoryTheory.Functor.map (GroupScheme.baseChange b) i := by
    rw [← hit, Functor.map_comp]
    rfl
  have : Mono (CommGroupScheme.groupHom f_L ≫ j_L).hom.hom.left := by
    rw [hfactor]
    infer_instance
  have hjLmax : IsMaximalSplitTorus (T := T_L) j_L := hjL.isMaximalSplitTorus hT
  have hE : RelativeRoot.HasOppositeFactorPairs (T := T_L) j_L :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs (T := T_L) j_L hT).mp
      (rootRankOneFactorization L G_L hGL T_L j_L hjLmax)
  have hEbase : RelativeRoot.HasOppositeFactorPairs i :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs i hS).mp
      (rootRankOneFactorization k G hG S i hi)
  obtain ⟨J, _, P, hP, hred⟩ := rootDatumExistence L G_L hGL T_L hT j_L hjL
  -- the upper order
  let ωL := henselianUnitsOrder v hH L
  let ω : Lˣ → ℝ := fun x => (ωL x).toAdd
  have hadd : ∀ x y : Lˣ, ω (x * y) = ω x + ω y := fun x y => by
    simp only [ω, map_mul, toAdd_mul]
  have hωσ : ∀ (σ : L ≃ₐ[k] L) (x : Lˣ), ω (Units.map σ.toMonoidHom x) = ω x := fun σ x => by
    simp only [ω, ωL, henselianUnitsOrder_galois]
  have hωext : ∀ x : kˣ,
      ω (Units.map (algebraMap k L).toMonoidHom x) = IntegerValuation.order v x :=
    henselianUnitsOrder_algebraMap v hH L
  -- the split apartment and a Galois-fixed point
  let DK : KPApartmentData (S := T_L) j_L ω :=
    KPApartmentData.ofSplitMaximalTorus G_L hGL T_L hT j_L hjL
      (FieldTheory.henselianSeparableAddValuation v hH L) ω
      (henselianUnitsOrder_coe v hH L)
      (three_le_encard_range_henselianSeparableAddValuation v hH L hv)
  have hDK := KPApartmentData.galoisStable_of_isSplitTorus k L j hGL hT hjL hadd hωσ DK
  let xK := KPApartmentData.galoisFixedPoint k L j DK hDK
  have hfix : ∀ σ : L ≃ₐ[k] L, RootFunctionFamily.galoisAction k L T G σ xK.val = xK.val :=
    KPApartmentData.galoisAction_galoisFixedPoint k L j DK hDK
  -- structural facts about the centralizer torus
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom.left := inferInstance
  have hmaxf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j) := hit ▸ hi
  have hcent' : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j :=
    hit ▸ hcent
  have hlarge : IsLargestSplitSubtorus (CommGroupScheme.groupHom f) :=
    (hmaxf.of_comp hjc).isLargestSplitSubtorus
  have hnorm : ∀ n : normalizerPoints i, (n : rationalPoints G) ∈ normalizerPoints j :=
    mem_normalizerPoints_of_torusCentralizer i j hcent
  have hzero : ∀ ψ ∈ relativeRoots (T := T_L) j_L, f_L ≫ ψ ≠ 0 := fun ψ hψ =>
    root_restrict_ne_zero_of_torusCentralizer k L f j hS hT hcent' ⟨ψ, hψ⟩
  have hfiber : ∀ (c : characterLattice S),
      ∀ χ ∈ relativeRoots (T := T_L) j_L, ∀ ψ ∈ relativeRoots (T := T_L) j_L,
      f_L ≫ χ = (a_L c) → f_L ≫ ψ = (a_L c) →
      ∃ σ : L ≃ₐ[k] L, characterLattice.galoisRepresentation k L T σ χ = ψ := by
    intro c χ hχ ψ hψ hχc hψc
    have hβ : (⟨χ, hχ⟩ : roots (T := T_L) j_L) ∈ rootRestrictionFiber k L j f c := hχc
    have horb := rootOrbit_eq_restrictionFiber_of_torusCentralizer k L f j hmaxf hjc hcent' hT
      hP c hβ
    have hmem : (⟨ψ, hψ⟩ : roots (T := T_L) j_L) ∈ MulAction.orbit (L ≃ₐ[k] L)
        (⟨χ, hχ⟩ : roots (T := T_L) j_L) := by
      rw [horb]
      exact hψc
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hmem
    exact ⟨σ, congrArg Subtype.val hσ⟩
  -- original-point shifts and V 5
  have hshift := torusFieldOriginalPointShifts_of_galoisFixed i f j hS hT hE DK xK hfix hfactor
    hlarge hnorm
  have hopposite : ∀ a ∈ relativeRoots i, ∀ g ∈ rootGroupPoints i a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints i (-a), ∀ g'' ∈ rootGroupPoints i (-a),
        g' * g * g'' ∈ normalizerPoints i →
          torusFieldRestrictedRootFunctionFamily (G := G) (T := T_L) (j := j_L) hS hT hE
              xK.isValuation f_L (-a) g' +
            torusFieldRestrictedRootFunctionFamily (G := G) (T := T_L) (j := j_L) hS hT hE
              xK.isValuation f_L a g = 0 := by
    intro a ha g hg hg1 g' hg' g'' hg'' hN
    by_cases h2a : (2 : ℤ) • a ∈ relativeRoots i
    · have h2a' : 2 • a ∈ relativeRoots i := by
        rwa [two_zsmul, ← two_nsmul] at h2a
      exact quasiSplitMultipliableOpposite k L S T G f j i hS hT hG hi hit hjc hcent hGL hjL hE
        ω DK xK hfix hfactor P hP hred a ha h2a' g hg hg1 g' hg' g'' hg'' hN
    · exact torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem f j i hS hT hE
        xK.isValuation hfix hfactor hP hzero hnorm hEbase ha h2a (hfiber a) hg hg1 hg' hg'' hN
  -- the descended valuation
  let ψ := torusFieldRestrictedValuationOfOriginalPointShifts i hS hT hE xK.isValuation f_L
    hfactor hEbase ωL xK.isSplitTorusCompatible ?hω hshift hopposite
  case hω =>
    obtain ⟨π, hπ⟩ := hv (WithZero.exp (-1 : ℤ))
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.zero_ne_coe hπ
    refine ⟨Units.mk0 π hπ0, ?_⟩
    change ω (Units.map (algebraMap k L).toMonoidHom (Units.mk0 π hπ0)) ≠ 0
    rw [hωext, IntegerValuation.order, IntegerValuation.orderUnits_toAdd, Units.val_mk0, hπ,
      WithZero.log_exp]
    norm_num
  have hcompat : IsSplitTorusCompatible i (IntegerValuation.order v) ψ.1 := by
    have h := torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible i hS hT hE
      xK.isValuation f_L hfactor ωL xK.isSplitTorusCompatible
    have he : (fun t => (ωL (Units.map (algebraMap k L).toMonoidHom t)).toAdd) =
        IntegerValuation.order v := funext hωext
    rw [he] at h
    exact h
  have hN : ∀ n : normalizerPoints i, ∃ w : V S, n • ψ.1 = w +ᵥ ψ.1 :=
    (torusFieldOriginalPointShifts_iff i hS hT hE xK.isValuation f_L hfactor).mp hshift
  let D' := KPApartmentData.ofNormalizerShifts (IntegerValuation.order v) ψ.1 ψ.2 hcompat hN
  have hbij : Function.Bijective
      (Cartan.restrictionEvaluation (CommGroupScheme.groupHom f)) :=
    Cartan.restrictionEvaluation_bijective_of_torusCentralizer hG hi hjc hcent hit
  let C' : CentralizerDatum i :=
    { Z := T.toGrp
      j := j
      s := CommGroupScheme.groupHom f
      isClosedSubgroup := hjc
      isRepresentedBy := hcent
      comp_eq := hit
      bijective := hbij }
  have hψD : ψ.1 ∈ D'.carrier := AddAction.mem_orbit_self ψ.1
  have hD' : IntegerValuation.IsOmegaCompatible v D' C' := by
    refine (IntegerValuation.isOmegaCompatible_iff_of_mem hψD).mpr ?_
    exact torusFieldRestricted_isCentralizerCompatible i f j v hS hT hE hadd hωσ hωext
      xK.isValuation xK.isSplitTorusCompatible hfactor hlarge hcent hbij
  -- uniqueness of the apartment class
  have hDD' : D = D' := hD.eq_of_isMaximalSplitTorus_of_centralizers hD' hG hi
  have hy : y.val ∈ AddAction.orbit (V S) ψ.1 := by
    have h : y.val ∈ D.carrier := y.mem
    have hc : D.carrier = D'.carrier := congrArg KPApartmentData.carrier hDD'
    rw [hc] at h
    exact h
  obtain ⟨w, hw⟩ := hy
  obtain ⟨c₁, hc₁⟩ := exists_torusFieldRestricted_value_rootOrbitFieldPoint k L f j v hv hH hG
    hj hS hT ha hhigh β horbit hGL hjL hE DK xK hfix
  refine ⟨c₁ + eval S a w, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have h1 : (rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit 0).val = 1 := by
      have h0 : rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit 0 = 1 := by
        unfold rootOrbitFieldPoint
        rw [AddEquiv.map_zero, AddEquiv.map_zero]
        rfl
      rw [h0]
      rfl
    have hai : a ∈ relativeRoots i := hit ▸ ha
    rw [h1, (y.isValuation.eq_top_iff a hai 1 (rootGroupPoints i a).one_mem).mpr rfl,
      AddValuation.map_zero, WithTop.top_add]
  · rw [← hw, RootFunctionFamily.vadd_apply]
    change torusFieldRestrictedRootFunctionFamily (G := G) (T := T_L) (j := j_L) hS hT hE
        xK.isValuation f_L a _ + _ = _
    rw [hc₁ x hx, add_assoc, ← WithTop.coe_add]

/-- **The actual filtration is a shifted root-field filtration.** In the situation of
`exists_apartment_value_rootOrbitFieldPoint`, with `i = f ≫ j`, the filtration subgroups
`U_{a,y,r}` of a point `y` of the apartment class are the additive filtration subgroups of the
published root-field coordinates of `a` for the normalized henselian valuation, shifted by
one constant `c` independent of the depth `r`. -/
theorem exists_filtration_eq_additiveRootFiltration
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    (hi : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j)) (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hjL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L) (hβ : β ∈ rootRestrictionFiber k L j f a)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (D : KPApartmentData (CommGroupScheme.groupHom f ≫ j) (IntegerValuation.order v))
    (C : CentralizerDatum (CommGroupScheme.groupHom f ≫ j))
    (hD : IntegerValuation.IsOmegaCompatible v D C) (y : D.Apartment) :
    ∃ c : ℝ, ∀ r : ℝ, D.filtration y a r =
      additiveRootFiltration
        (FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β))
        (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv
        (r - c) := by
  obtain ⟨c, hc⟩ := exists_apartment_value_rootOrbitFieldPoint k L f j v hv hH hG hj hS hi rfl
    hjc hcent hT hjL ha hhigh β horbit D C hD y
  refine ⟨c, fun r => ?_⟩
  set ω := FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β)
  set e := (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv
  have key : ∀ (g : rationalPoints G) (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a),
      y.val a g = additiveRootValue ω e g + ((c : ℝ) : WithTop ℝ) := by
    intro g hg
    have hx : (rootOrbitFieldPoint k L f j hG hj hS hT ha.1 hhigh β horbit
        (e.symm ⟨g, hg⟩).toAdd).val = g := by
      change (e (Multiplicative.ofAdd (e.symm ⟨g, hg⟩).toAdd)).val = g
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
    have h2 : additiveRootValue ω e g = ω (e.symm ⟨g, hg⟩).toAdd :=
      additiveRootValue_of_mem ω e ⟨g, hg⟩
    rw [h2]
    conv_lhs => rw [← hx]
    exact hc _
  have hle : ∀ t : WithTop ℝ, ((r : ℝ) : WithTop ℝ) ≤ t + ((c : ℝ) : WithTop ℝ) ↔
      ((r - c : ℝ) : WithTop ℝ) ≤ t := by
    intro t
    induction t using WithTop.recTopCoe with
    | top => simp only [WithTop.top_add, le_top]
    | coe t =>
      rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
      constructor <;> intro h <;> linarith
  ext g
  rw [KPApartmentData.mem_filtration, mem_additiveRootFiltration]
  constructor
  · rintro ⟨hg, hr⟩
    rw [key g hg, hle] at hr
    exact ⟨hg, hr⟩
  · rintro ⟨hg, hr⟩
    refine ⟨hg, ?_⟩
    rw [key g hg, hle]
    exact hr

/-- **The root-field depth shift.** For a point `y` of the actual apartment class and a
relative root `a` with no higher multiples, a real constant `c` such that the filtration
subgroups `U_{a,y,r}` are the additive root-field filtration subgroups at depth `r - c`; it
is chosen by `exists_filtration_eq_additiveRootFiltration`. -/
def rootFieldDepthShift
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    (hi : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j)) (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hjL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L) (hβ : β ∈ rootRestrictionFiber k L j f a)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (D : KPApartmentData (CommGroupScheme.groupHom f ≫ j) (IntegerValuation.order v))
    (C : CentralizerDatum (CommGroupScheme.groupHom f ≫ j))
    (hD : IntegerValuation.IsOmegaCompatible v D C) (y : D.Apartment) : ℝ :=
  (exists_filtration_eq_additiveRootFiltration k L f j v hv hH hG hj hS hi hjc hcent hT hjL ha
    hhigh β hβ horbit D C hD y).choose

/-- The filtration subgroups `U_{a,y,r}` of the actual apartment class are the additive
root-field filtration subgroups at depth `r` minus the root-field depth shift. -/
theorem filtration_eq_additiveRootFiltration_rootFieldDepthShift
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    [IsAffine T.toGrp.X.left] [IsAffine S.toGrp.X.left]
    (v : Valuation k (WithZero (Multiplicative ℤ))) (hv : Function.Surjective v)
    (hH : HenselianLocalRing v.valuationSubring)
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    (hi : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j)) (hjc : IsClosedSubgroup j)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hjL : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L) (hβ : β ∈ rootRestrictionFiber k L j f a)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (D : KPApartmentData (CommGroupScheme.groupHom f ≫ j) (IntegerValuation.order v))
    (C : CentralizerDatum (CommGroupScheme.groupHom f ≫ j))
    (hD : IntegerValuation.IsOmegaCompatible v D C) (y : D.Apartment) (r : ℝ) :
    D.filtration y a r =
      additiveRootFiltration
        (FieldTheory.henselianSeparableAddValuation v hH (rootOrbitField k L j β))
        (rootFieldCoordinatesOfOrbit k L f j hG hj hS hcent hT ha hhigh β hβ horbit).equiv
        (r - rootFieldDepthShift k L f j v hv hH hG hj hS hi hjc hcent hT hjL ha hhigh β hβ
          horbit D C hD y) :=
  (exists_filtration_eq_additiveRootFiltration k L f j v hv hH hG hj hS hi hjc hcent hT hjL ha
    hhigh β hβ horbit D C hD y).choose_spec r

end Langlands.Geometry.Building
