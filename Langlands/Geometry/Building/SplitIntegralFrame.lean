import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.Geometry.Building.IntegerOmegaApartmentRigidity
import Langlands.Geometry.Building.IntegerCentralizerStabilizer
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # Split integral frames on integer-valued building data

A split integral frame on `B : IntegerValuationBuildingData v G` consists of a subgroup
`K ≤ G(k)` and root parametrizations `u_a : k → U_a(k)` of the actual root groups of the
torus `B.S`, with Chevalley-type relations: `u_a(c) ∈ K` exactly for integral `c`, the
integral torus points lie in `K`, a rank-one relation between the normalizing products
of `u_a(c)` and `u_a(1)`, simple roots with integral Weyl points, and generation
statements. This module proves the torus translation formula on the apartment, the
root value formula `φ_a(u_a(c)) = ord(c) + φ_a(u_a(1))` at every apartment point, the
existence of a point `x` at which every value `φ_a(u_a(1))` vanishes, that `x` is special,
and that `K = G(k)^1 ∩ G(k)_x` (if `k` has a unit whose square is not `1`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- The value `a(t) ∈ kˣ` of a character `a` of `S` at `t ∈ S(k)`. -/
abbrev charEval (a : characterLattice B.S) : rationalPoints B.S.toGrp →* kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice B.S).symm a)

/-- The torus points as normalizer points, through the centralizer datum. -/
def torusNormalizer : rationalPoints B.S.toGrp →* normalizerPoints B.i :=
  B.centralizer.toNormalizer.comp (rationalPoints.map B.centralizer.s)

theorem coe_torusNormalizer (t : rationalPoints B.S.toGrp) :
    (B.torusNormalizer t : rationalPoints G) = rationalPoints.map B.i t := by
  have h : rationalPoints.map (B.centralizer.s ≫ B.centralizer.j) t =
      rationalPoints.map B.i t :=
    congrArg (fun f => rationalPoints.map f t) B.centralizer.comp_eq
  rw [← h, torusNormalizer, MonoidHom.comp_apply, coe_centralizerToNormalizer]
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

theorem weylAction_torusNormalizer (t : rationalPoints B.S.toGrp) :
    weylAction B.i (B.torusNormalizer t) = 1 :=
  weylAction_centralizerToNormalizer B.centralizer.isRepresentedBy _

/-- The action of a torus point on the values of an apartment point (the split-torus part
of KP axiom V 6). -/
theorem torusNormalizer_smul_val (t : rationalPoints B.S.toGrp) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) (g : rationalPoints G) :
    (B.torusNormalizer t • x).val a g =
      x.val a g + ((-IntegerValuation.order v (B.charEval a t) : ℝ) : WithTop ℝ) := by
  set n := B.torusNormalizer t with hn
  have hw : weylAction B.i n⁻¹ = 1 := by
    rw [hn, ← map_inv]
    exact B.weylAction_torusNormalizer t⁻¹
  have hnG : (n : rationalPoints G) = rationalPoints.map B.i t := B.coe_torusNormalizer t
  rw [KPApartmentData.val_smul, RootFunctionFamily.smul_apply, hw, LinearEquiv.coe_one, id, hnG]
  by_cases hg : g ∈ rootGroupPoints B.i a
  · exact x.isSplitTorusCompatible a ha t g hg
  · have hg' : (rationalPoints.map B.i t)⁻¹ * g * rationalPoints.map B.i t ∉
        rootGroupPoints B.i a := by
      intro hmem
      apply hg
      have hc := conj_mem_rootGroupPoints n hmem
      rwa [hn, B.weylAction_torusNormalizer t, LinearEquiv.coe_one, id, ← hn, hnG,
        show rationalPoints.map B.i t * ((rationalPoints.map B.i t)⁻¹ * g *
          rationalPoints.map B.i t) * (rationalPoints.map B.i t)⁻¹ = g by group] at hc
    rw [x.isValuation.eq_top_of_not_mem a ha _ hg', x.isValuation.eq_top_of_not_mem a ha g hg,
      WithTop.top_add]

private theorem coe_add_cancel {r e f : ℝ}
    (h : ((r : ℝ) : WithTop ℝ) + (e : WithTop ℝ) = (r : WithTop ℝ) + (f : WithTop ℝ)) :
    e = f := by
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h
  linarith

/-- The torus translation formula: `t ∈ S(k)` translates the apartment by a vector on which
each root `a` takes the value `-ord(a(t))`. -/
theorem rootForm_torusNormalizer_vsub (t : rationalPoints B.S.toGrp) (x : B.Apartment)
    (α : relativeRoots B.i) :
    rootForm B.i α (B.torusNormalizer t • x -ᵥ x) =
      -IntegerValuation.order v (B.charEval α t) := by
  obtain ⟨w, hw⟩ := B.apartment.equipollent_of_mem x.mem (B.torusNormalizer t • x).mem
  rw [KPApartmentData.vsub_eq_mk hw, rootForm_mk]
  obtain ⟨g, -, hg⟩ := x.isValuation.exists_ne_top α.2
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hg
  have h1 := B.torusNormalizer_smul_val t x α.2 g
  rw [hw, RootFunctionFamily.vadd_apply, ← hr] at h1
  exact coe_add_cancel h1

/-- The translation of a torus point is zero when all its root values are units. -/
theorem torusNormalizer_smul_eq_self {t : rationalPoints B.S.toGrp}
    (ht : ∀ a ∈ relativeRoots B.i, IntegerValuation.order v (B.charEval a t) = 0)
    (x : B.Apartment) : B.torusNormalizer t • x = x := by
  obtain ⟨w, hw⟩ := B.apartment.equipollent_of_mem x.mem (B.torusNormalizer t • x).mem
  have hw0 : w ∈ rootAnnihilator B.i := by
    refine mem_rootAnnihilator.2 fun a ha => ?_
    have h := B.rootForm_torusNormalizer_vsub t x ⟨a, ha⟩
    rw [KPApartmentData.vsub_eq_mk hw, rootForm_mk, ht a ha, neg_zero] at h
    exact h
  refine KPApartmentData.Apartment.ext ?_
  rw [hw]
  exact x.isValuation.vadd_eq_self_iff.2 hw0

/-- A split integral frame on `B` (internal definition, see the Markdown): an integral
subgroup `K ≤ G(k)`, parametrizations `u a : k → U_a(k)` of the actual root groups with
Chevalley-type relations, a set of simple roots with integral Weyl points, and generation
statements for `K` and for the Weyl group. -/
structure SplitIntegralFrame where
  /-- The integral subgroup. -/
  K : Subgroup (rationalPoints G)
  /-- The root parametrizations `u a : k → U_a(k)`. -/
  u : characterLattice B.S → k → rationalPoints G
  u_add : ∀ a ∈ relativeRoots B.i, ∀ c d : k, u a (c + d) = u a c * u a d
  u_mem : ∀ a ∈ relativeRoots B.i, ∀ c : k, u a c ∈ B.rootGroup a
  u_surjective : ∀ a ∈ relativeRoots B.i, ∀ g ∈ B.rootGroup a, ∃ c : k, u a c = g
  u_eq_one : ∀ a ∈ relativeRoots B.i, ∀ c : k, u a c = 1 → c = 0
  /-- The torus acts on `u a` through the character `a`. -/
  torus_conj : ∀ a ∈ relativeRoots B.i, ∀ (t : rationalPoints B.S.toGrp) (c : k),
    rationalPoints.map B.i t * u a c * (rationalPoints.map B.i t)⁻¹ =
      u a ((B.charEval a t : k) * c)
  /-- The rank-one relation `n(u_a(c)) = a^∨(c) n(u_a(1))` between normalizing products. -/
  rankOne : ∀ a ∈ relativeRoots B.i, ∀ c : kˣ,
    ∃ (p q : rationalPoints G × rationalPoints G) (t : rationalPoints B.S.toGrp),
      RelativeRoot.IsOppositeFactorPair B.i a (u a c) p ∧
        RelativeRoot.IsOppositeFactorPair B.i a (u a 1) q ∧
        B.charEval a t = c ^ 2 ∧
        p.1 * u a c * p.2 = rationalPoints.map B.i t * (q.1 * u a 1 * q.2)
  /-- The relative root system is reduced. -/
  two_smul_not_mem : ∀ a ∈ relativeRoots B.i, 2 • a ∉ relativeRoots B.i
  u_mem_K : ∀ a ∈ relativeRoots B.i, ∀ c : k, u a c ∈ K ↔ v c ≤ 1
  centralizer_mem_K : ∀ z ∈ characterValuationKernel v B.centralizer.Z,
    rationalPoints.map B.centralizer.j z ∈ K
  /-- `K` is generated by `Z(k)^1` and the integral root points. -/
  K_le_closure : K ≤ Subgroup.closure
    (rationalPoints.map B.centralizer.j '' (characterValuationKernel v B.centralizer.Z : Set _) ∪
      ⋃ a ∈ relativeRoots B.i, u a '' {c | v c ≤ 1})
  /-- The simple roots. -/
  simple : Set (characterLattice B.S)
  simple_subset : simple ⊆ relativeRoots B.i
  simple_linearIndependent :
    LinearIndependent ℝ fun b : simple => rootForm B.i ⟨b, simple_subset b.2⟩
  /-- The integral Weyl point `u_{-b}(-1) u_b(1) u_{-b}(-1)` of a simple root normalizes `S`. -/
  weyl_mem : ∀ b ∈ simple, u (-b) (-1) * u b 1 * u (-b) (-1) ∈ normalizerPoints B.i
  /-- Every root is reached from the simple roots by simple reflections. -/
  induction : ∀ P : characterLattice B.S → Prop, (∀ b ∈ simple, P b) →
    (∀ b (hb : b ∈ simple), ∀ a ∈ relativeRoots B.i, P a →
      P (weylAction B.i ⟨_, weyl_mem b hb⟩ a)) →
    ∀ a ∈ relativeRoots B.i, P a
  /-- The simple Weyl points generate the Weyl group. -/
  weyl_generated : ∀ n : normalizerPoints B.i, ∃ m ∈ Subgroup.closure
      (Set.range fun b : simple => (⟨_, weyl_mem b b.2⟩ : normalizerPoints B.i)),
    weylAction B.i n = weylAction B.i m

namespace SplitIntegralFrame

variable {B} (F : B.SplitIntegralFrame)

theorem u_ne_one {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) (c : kˣ) :
    F.u a c ≠ 1 :=
  fun h => c.ne_zero (F.u_eq_one a ha c h)

theorem u_one_ne_one {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    F.u a 1 ≠ 1 := by
  simpa using F.u_ne_one ha 1

/-- The value `x_a(u_a(1))` at an apartment point, as a real number. -/
def rootValue (x : B.Apartment) (a : characterLattice B.S) : ℝ :=
  (x.val a (F.u a 1)).untopD 0

theorem val_u_one (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    x.val a (F.u a 1) = (F.rootValue x a : WithTop ℝ) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 fun h =>
    F.u_one_ne_one ha ((x.isValuation.eq_top_iff a ha _ (F.u_mem a ha 1)).1 h)
  rw [rootValue, ← hr, WithTop.untopD_coe]

private theorem order_sq (c : kˣ) :
    IntegerValuation.order v (c ^ 2) = 2 * IntegerValuation.order v c := by
  simp only [IntegerValuation.order, map_pow, toAdd_pow, nsmul_eq_mul]
  push_cast
  ring

/-- The root value formula `x_a(u_a(c)) = ord(c) + x_a(u_a(1))`, from the rank-one relation
and the displacement of the normalizing products. -/
theorem val_u (x : B.Apartment) {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (c : kˣ) :
    x.val a (F.u a c) =
      ((IntegerValuation.order v c + F.rootValue x a : ℝ) : WithTop ℝ) := by
  obtain ⟨p, q, t, hp, hq, ht, heq⟩ := F.rankOne a ha c
  have hc1 := F.u_ne_one ha c
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 fun h =>
    hc1 ((x.isValuation.eq_top_iff a ha _ (F.u_mem a ha c)).1 h)
  have hD := B.apartment.rootForm_oppositeFactorPair_vsub B.isConnectedReductive
    B.isMaximalSplitTorus (α := ⟨a, ha⟩) (F.u_mem a ha c) hc1 hp x hr.symm
  have hD1 := B.apartment.rootForm_oppositeFactorPair_vsub B.isConnectedReductive
    B.isMaximalSplitTorus (α := ⟨a, ha⟩) (F.u_mem a ha 1) (F.u_one_ne_one ha) hq x
    (F.val_u_one x ha)
  have hn : (⟨p.1 * F.u a c * p.2, hp.2.2⟩ : normalizerPoints B.i) =
      B.torusNormalizer t * ⟨q.1 * F.u a 1 * q.2, hq.2.2⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, B.coe_torusNormalizer]
    exact heq
  rw [hn, mul_smul, ← vsub_add_vsub_cancel _ ((⟨q.1 * F.u a 1 * q.2, hq.2.2⟩ :
    normalizerPoints B.i) • x) x, map_add, B.rootForm_torusNormalizer_vsub, hD1] at hD
  change -IntegerValuation.order v (B.charEval a t) + _ = _ at hD
  rw [ht, order_sq] at hD
  rw [← hr]
  congr 1
  linarith

theorem u_zero {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) : F.u a 0 = 1 := by
  have h := F.u_add a ha 0 0
  rw [add_zero] at h
  simpa using h

include F in
/-- The opposite of a root is a root (from the rank-one relation). -/
theorem neg_mem {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    -a ∈ relativeRoots B.i := by
  obtain ⟨-, q, -, -, hq, -⟩ := F.rankOne a ha 1
  have hflip := hq.weylAction_eq_neg B.i B.isMaximalSplitTorus.isSplitSubtorus.1 ha.1
    (F.u_mem a ha 1) (F.u_one_ne_one ha)
  rw [← hflip]
  exact weylAction_mapsTo_relativeRoots B.i _ ha

theorem u_one_mem_K {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    F.u a 1 ∈ F.K :=
  (F.u_mem_K a ha 1).2 (by rw [map_one])

private theorem order_nonneg_iff (c : kˣ) :
    0 ≤ IntegerValuation.order v c ↔ v (c : k) ≤ 1 := by
  have hne : v (c : k) ≠ 0 := (Valuation.ne_zero_iff v).2 c.ne_zero
  rw [IntegerValuation.order, IntegerValuation.orderUnits_toAdd, Int.cast_nonneg_iff, neg_nonneg,
    WithZero.log_le_iff_le_exp hne, WithZero.exp_zero]

/-- Translating a point changes the root values by the root form. -/
theorem rootValue_vadd (w : TranslationSpace B.i) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    F.rootValue (w +ᵥ x) a = F.rootValue x a + rootForm B.i ⟨a, ha⟩ w := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (rootAnnihilator B.i) w
  have h := F.val_u_one ((Submodule.Quotient.mk w : TranslationSpace B.i) +ᵥ x) ha
  rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, F.val_u_one x ha,
    ← WithTop.coe_add, WithTop.coe_inj] at h
  rw [rootForm_mk, ← h]

/-- The root forms of the simple roots are jointly surjective. -/
theorem rootForm_simple_surjective :
    Function.Surjective (LinearMap.pi fun b : F.simple =>
      rootForm B.i ⟨b, F.simple_subset b.2⟩) := by
  classical
  have := B.isConnectedReductive.smooth
  have hfin : F.simple.Finite :=
    (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i).subset F.simple_subset
  let : Fintype F.simple := hfin.fintype
  set f := LinearMap.pi fun b : F.simple => rootForm B.i ⟨b, F.simple_subset b.2⟩ with hf
  refine LinearMap.dualMap_injective_iff.1 ((injective_iff_map_eq_zero _).2 fun φ hφ => ?_)
  have hs : ∀ (b : F.simple) (c : ℝ), (Pi.single b c : F.simple → ℝ) = c • Pi.single b 1 :=
    fun b c => by rw [← Pi.single_smul', smul_eq_mul, mul_one]
  have hsum : ∑ b : F.simple, φ (Pi.single b 1) • rootForm B.i ⟨b, F.simple_subset b.2⟩ = 0 := by
    refine LinearMap.ext fun w => ?_
    have h0 := LinearMap.congr_fun hφ w
    rw [LinearMap.dualMap_apply, LinearMap.zero_apply] at h0
    rw [LinearMap.zero_apply, ← h0, ← Finset.univ_sum_single (f w), map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hs b (f w b), map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm, hf,
      LinearMap.pi_apply]
  have hg := Fintype.linearIndependent_iff.1 F.simple_linearIndependent _ hsum
  refine LinearMap.pi_ext fun b c => ?_
  rw [hs b c, map_smul, hg b, smul_zero, LinearMap.zero_apply]

/-- There is an apartment point at which all simple root values vanish. -/
theorem exists_rootValue_simple_eq_zero :
    ∃ x : B.Apartment, ∀ b ∈ F.simple, F.rootValue x b = 0 := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty B.Apartment)
  obtain ⟨w, hw⟩ := F.rootForm_simple_surjective fun b => -F.rootValue x₀ b
  refine ⟨w +ᵥ x₀, fun b hb => ?_⟩
  have h := congrFun hw ⟨b, hb⟩
  rw [LinearMap.pi_apply] at h
  rw [F.rootValue_vadd w x₀ (F.simple_subset hb), h, add_neg_cancel]

/-- An integral normalizing point fixing `x` can only increase root values. -/
theorem rootValue_le_of_smul_eq_self {n : normalizerPoints B.i} (hnK : (n : rationalPoints G) ∈ F.K)
    {x : B.Apartment} (hnx : n • x = x) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) :
    F.rootValue x a ≤ F.rootValue x (weylAction B.i n a) := by
  set b := weylAction B.i n a with hb_def
  have hb : b ∈ relativeRoots B.i := weylAction_mapsTo_relativeRoots B.i n ha
  set g := (n : rationalPoints G)⁻¹ * F.u b 1 * (n : rationalPoints G) with hg_def
  have hg : g ∈ B.rootGroup a := by
    have h := conj_mem_rootGroupPoints n⁻¹ (F.u_mem b hb 1)
    rwa [hb_def, weylAction_inv_apply_apply, InvMemClass.coe_inv, inv_inv] at h
  obtain ⟨c, hc⟩ := F.u_surjective a ha g hg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [F.u_zero ha] at hc
    apply F.u_one_ne_one hb
    have h' : F.u b 1 = (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ := by
      rw [hg_def]
      group
    rw [h', ← hc, mul_one, mul_inv_cancel]
  have hgK : g ∈ F.K :=
    F.K.mul_mem (F.K.mul_mem (F.K.inv_mem hnK) (F.u_one_mem_K hb)) hnK
  have hcv : v c ≤ 1 := (F.u_mem_K a ha c).1 (hc ▸ hgK)
  have hval : x.val b (F.u b 1) = x.val a g := by
    conv_lhs => rw [← hnx]
    rw [KPApartmentData.val_smul, RootFunctionFamily.smul_apply, hb_def,
      weylAction_inv_apply_apply]
  have hu := F.val_u x ha (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, ← hval, F.val_u_one x hb, WithTop.coe_inj] at hu
  rw [hu]
  have := (order_nonneg_iff (v := v) (Units.mk0 c hc0)).2 (by rwa [Units.val_mk0])
  linarith

/-- An integral normalizing point fixing `x` preserves root values. -/
theorem rootValue_weylAction_of_smul_eq_self {n : normalizerPoints B.i}
    (hnK : (n : rationalPoints G) ∈ F.K) {x : B.Apartment} (hnx : n • x = x)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i) :
    F.rootValue x (weylAction B.i n a) = F.rootValue x a := by
  refine le_antisymm ?_ (F.rootValue_le_of_smul_eq_self hnK hnx ha)
  have hnK' : ((n⁻¹ : normalizerPoints B.i) : rationalPoints G) ∈ F.K := by
    rw [InvMemClass.coe_inv]
    exact F.K.inv_mem hnK
  have hnx' : n⁻¹ • x = x := by
    rw [inv_smul_eq_iff, hnx]
  have h := F.rootValue_le_of_smul_eq_self hnK' hnx'
    (weylAction_mapsTo_relativeRoots B.i n ha)
  rwa [weylAction_inv_apply_apply] at h

/-- The integral Weyl point of a simple root. -/
def simpleWeyl (b : characterLattice B.S) (hb : b ∈ F.simple) : normalizerPoints B.i :=
  ⟨_, F.weyl_mem b hb⟩

theorem simpleWeyl_mem_K {b : characterLattice B.S} (hb : b ∈ F.simple) :
    (F.simpleWeyl b hb : rationalPoints G) ∈ F.K := by
  have hb' := F.simple_subset hb
  have hnb := F.neg_mem hb'
  have h1 : F.u (-b) (-1) ∈ F.K := (F.u_mem_K (-b) hnb (-1)).2 (by rw [Valuation.map_neg, map_one])
  show F.u (-b) (-1) * F.u b 1 * F.u (-b) (-1) ∈ F.K
  exact F.K.mul_mem (F.K.mul_mem h1 (F.u_one_mem_K hb')) h1

theorem simpleWeyl_smul_eq_self {b : characterLattice B.S} (hb : b ∈ F.simple)
    {x : B.Apartment} (hx : F.rootValue x b = 0) : F.simpleWeyl b hb • x = x := by
  have hb' := F.simple_subset hb
  have hnb := F.neg_mem hb'
  have hp : RelativeRoot.IsOppositeFactorPair B.i b (F.u b 1)
      (F.u (-b) (-1), F.u (-b) (-1)) :=
    ⟨F.u_mem (-b) hnb (-1), F.u_mem (-b) hnb (-1), F.weyl_mem b hb⟩
  have hx' : x.val b (F.u b 1) = 0 := by
    rw [F.val_u_one x hb', hx, WithTop.coe_zero]
  exact B.apartment.oppositeFactorPair_smul_eq_self B.isConnectedReductive B.isMaximalSplitTorus
    (α := ⟨b, hb'⟩) (F.u_mem b hb' 1) (F.u_one_ne_one hb') hp x hx'

/-- **The hyperspecial point of a split integral frame**: an apartment point at which every
root value `x_a(u_a(1))` vanishes. -/
theorem exists_rootValue_eq_zero :
    ∃ x : B.Apartment, ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0 := by
  obtain ⟨x, hx⟩ := F.exists_rootValue_simple_eq_zero
  refine ⟨x, F.induction (fun a => F.rootValue x a = 0) hx fun b hb a ha hxa => ?_⟩
  change F.rootValue x (weylAction B.i (F.simpleWeyl b hb) a) = 0
  rw [F.rootValue_weylAction_of_smul_eq_self (F.simpleWeyl_mem_K hb)
    (F.simpleWeyl_smul_eq_self hb (hx b hb)) ha, hxa]

/-! ### The integral subgroup is the one-stabilizer of the point -/

/-- The rational characters of `G` are trivial on the root parametrizations (as soon as `k`
has a unit whose square is not `1`). -/
theorem rationalCharacterEval_u (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (χ : rationalCharacters G) (c : k) :
    rationalCharacterEval χ (F.u a c) = 1 := by
  obtain ⟨d, hd⟩ := hk
  obtain ⟨-, -, t, -, -, ht, -⟩ := F.rankOne a ha d
  have hadd : ∀ c c' : k, rationalCharacterEval χ (F.u a (c + c')) =
      rationalCharacterEval χ (F.u a c) * rationalCharacterEval χ (F.u a c') := fun c c' => by
    rw [F.u_add a ha, map_mul]
  have hconj : ∀ c : k, rationalCharacterEval χ (F.u a ((B.charEval a t : k) * c)) =
      rationalCharacterEval χ (F.u a c) := fun c => by
    rw [← F.torus_conj a ha t c, map_mul, map_mul, map_inv,
      mul_comm (rationalCharacterEval χ (rationalPoints.map B.i t)), mul_assoc, mul_inv_cancel,
      mul_one]
  have he : (B.charEval a t : k) - 1 ≠ 0 := by
    rw [sub_ne_zero, ht]
    exact fun h => hd (Units.ext (by rw [h, Units.val_one]))
  have h1 : (B.charEval a t : k) * (c / ((B.charEval a t : k) - 1)) =
      c + c / ((B.charEval a t : k) - 1) := by
    have : ((B.charEval a t : k) - 1) * (c / ((B.charEval a t : k) - 1)) = c := by
      field_simp
    linear_combination this
  have h2 := hconj (c / ((B.charEval a t : k) - 1))
  rw [h1, hadd] at h2
  simpa using h2

theorem u_mem_characterValuationKernel (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (c : k) : F.u a c ∈ characterValuationKernel v G :=
  mem_characterValuationKernel.2 fun χ => by
    rw [F.rationalCharacterEval_u hk ha χ c, Units.val_one, map_one]

theorem u_mem_filtration {x : B.Apartment} {a : characterLattice B.S}
    (ha : a ∈ relativeRoots B.i) (hx : F.rootValue x a = 0) {c : k} (hc : v c ≤ 1) :
    F.u a c ∈ B.filtration x a 0 := by
  refine KPApartmentData.mem_filtration.2 ⟨F.u_mem a ha c, ?_⟩
  by_cases hc0 : c = 0
  · rw [hc0, F.u_zero ha, (x.isValuation.eq_top_iff a ha _ (B.rootGroup a).one_mem).2 rfl]
    exact le_top
  · have h := F.val_u x ha (Units.mk0 c hc0)
    rw [Units.val_mk0, hx, add_zero] at h
    rw [h]
    exact WithTop.coe_le_coe.2 ((order_nonneg_iff (Units.mk0 c hc0)).2 (by rwa [Units.val_mk0]))

/-- `K ⊆ G(k)^1 ∩ G(k)_x` at a point where all root values vanish. -/
theorem K_le_oneStabilizer (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) :
    F.K ≤ B.oneStabilizer (B.apartmentMap x) := by
  refine F.K_le_closure.trans ((Subgroup.closure_le _).2 ?_)
  rintro g (⟨z, hz, rfl⟩ | hg)
  · exact B.map_mem_oneStabilizer hz x
  · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq] at hg
    obtain ⟨a, ha, c, hc, rfl⟩ := hg
    refine Subgroup.mem_inf.2 ⟨F.u_mem_characterValuationKernel hk ha c, ?_⟩
    have h := B.apartment.rootFixer_le_sharpFixer ⟨a, ha⟩ {x}
    rw [B.apartment.rootFixer_singleton] at h
    exact B.sharpFixer_le_fixer x (h (F.u_mem_filtration ha (hx a ha) hc))

/-- `G(k)^♯_x ⊆ K` at a point where all root values vanish. -/
theorem sharpFixer_le_K {x : B.Apartment} (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) :
    B.sharpFixer {x} ≤ F.K := by
  show B.apartment.sharpFixer {x} ≤ F.K
  rw [B.apartment.sharpFixer_eq_closure, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨⟨a, ha⟩, hg⟩ := hg
  rw [SetLike.mem_coe, B.apartment.rootFixer_singleton] at hg
  obtain ⟨hgU, hgv⟩ := KPApartmentData.mem_filtration.1 hg
  obtain ⟨c, rfl⟩ := F.u_surjective a ha g hgU
  by_cases hc0 : c = 0
  · rw [hc0, F.u_zero ha]
    exact F.K.one_mem
  · refine (F.u_mem_K a ha c).2 ?_
    have h := F.val_u x ha (Units.mk0 c hc0)
    rw [Units.val_mk0, hx a ha, add_zero] at h
    rw [h] at hgv
    have h0 := (order_nonneg_iff (Units.mk0 c hc0)).1 (WithTop.coe_le_coe.1 hgv)
    rwa [Units.val_mk0] at h0

/-- A normalizing point in `G(k)^1` fixing a point where all root values vanish lies in `K`. -/
theorem normalizer_mem_K (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) {n : normalizerPoints B.i}
    (hn1 : (n : rationalPoints G) ∈ characterValuationKernel v G) (hnx : n • x = x) :
    (n : rationalPoints G) ∈ F.K := by
  obtain ⟨m, hm, hw⟩ := F.weyl_generated n
  have hmK : (m : rationalPoints G) ∈ F.K := by
    have hle : Subgroup.closure (Set.range fun b : F.simple =>
        (⟨_, F.weyl_mem b b.2⟩ : normalizerPoints B.i)) ≤
        F.K.comap (normalizerPoints B.i).subtype :=
      (Subgroup.closure_le _).2 (by
        rintro _ ⟨b, rfl⟩
        exact F.simpleWeyl_mem_K b.2)
    exact hle hm
  have hmx : m • x = x := by
    have hle : Subgroup.closure (Set.range fun b : F.simple =>
        (⟨_, F.weyl_mem b b.2⟩ : normalizerPoints B.i)) ≤
        MulAction.stabilizer (normalizerPoints B.i) x :=
      (Subgroup.closure_le _).2 (by
        rintro _ ⟨b, rfl⟩
        exact F.simpleWeyl_smul_eq_self b.2 (hx b (F.simple_subset b.2)))
    exact hle hm
  have hm1 := (Subgroup.mem_inf.1 (F.K_le_oneStabilizer hk hx hmK)).1
  set z := m⁻¹ * n with hz_def
  have hzW : weylAction B.i z = 1 := by
    rw [hz_def, map_mul, map_inv, hw, inv_mul_cancel]
  have hzC := (B.isMaximalSplitTorus.isSplitSubtorus.1.weylAction_eq_one_iff B.i z).1 hzW
  obtain ⟨y, hy⟩ : ∃ y, B.centralizer.toNormalizer y = z := by
    rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at hzC
    obtain ⟨y, hy⟩ := hzC
    exact ⟨y, Subtype.ext hy⟩
  have hyz : rationalPoints.map B.centralizer.j y = (z : rationalPoints G) := by
    rw [← hy, CentralizerDatum.toNormalizer, coe_centralizerToNormalizer]
  have hz1 : (z : rationalPoints G) ∈ characterValuationKernel v G := by
    rw [hz_def, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (characterValuationKernel v G).mul_mem
      ((characterValuationKernel v G).inv_mem hm1) hn1
  have hzx : B.centralizer.toNormalizer y • x = x := by
    rw [hy, hz_def, mul_smul, hnx, inv_smul_eq_iff, hmx]
  have hyK := F.centralizer_mem_K y
    (B.mem_characterValuationKernel_of_smul_eq (hyz ▸ hz1) hzx)
  rw [hyz] at hyK
  have hnz : (n : rationalPoints G) = (m : rationalPoints G) * (z : rationalPoints G) := by
    rw [hz_def, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_cancel_left]
  rw [hnz]
  exact F.K.mul_mem hmK hyK

/-- `G(k)^1 ∩ G(k)_x ⊆ K` at a point where all root values vanish. -/
theorem oneStabilizer_le_K (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) :
    B.oneStabilizer (B.apartmentMap x) ≤ F.K := by
  intro g hg
  obtain ⟨hg1, hgx⟩ := Subgroup.mem_inf.1 hg
  have hNx : (MulAction.stabilizer (normalizerPoints B.i) x).map (normalizerPoints B.i).subtype ≤
      Subgroup.normalizer (B.sharpFixer {x} : Set (rationalPoints G)) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨n, hn, rfl⟩ s hs
    have h := B.apartment.sharpFixer_le_comap n {x} hs
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Set.smul_set_singleton,
      MulAction.mem_stabilizer_iff.1 hn] at h
    exact h
  have hmem : g ∈ ((B.sharpFixer {x} ⊔ (MulAction.stabilizer (normalizerPoints B.i) x).map
      (normalizerPoints B.i).subtype : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    rw [SetLike.mem_coe, ← B.apartment.reducedFixer_apartmentMap]
    exact hgx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hNx] at hmem
  obtain ⟨s, hs, n', hn', rfl⟩ := hmem
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hn'
  have hsK := F.sharpFixer_le_K hx hs
  have hs1 := (Subgroup.mem_inf.1 (F.K_le_oneStabilizer hk hx hsK)).1
  have hn1 : (n : rationalPoints G) ∈ characterValuationKernel v G := by
    have h := (characterValuationKernel v G).mul_mem
      ((characterValuationKernel v G).inv_mem hs1) hg1
    rwa [inv_mul_cancel_left] at h
  exact F.K.mul_mem hsK (F.normalizer_mem_K hk hx hn1 (MulAction.mem_stabilizer_iff.1 hn))

/-- **The integral subgroup of a split integral frame is the one-stabilizer of the point
where all root values vanish.** -/
theorem K_eq_oneStabilizer (hk : ∃ d : kˣ, d ^ 2 ≠ 1) {x : B.Apartment}
    (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) :
    F.K = B.oneStabilizer (B.apartmentMap x) :=
  le_antisymm (F.K_le_oneStabilizer hk hx) (F.oneStabilizer_le_K hk hx)

/-! ### The point is special -/

include F in
/-- The root form of every root is nonzero: the root takes the value `2` on the coroot class
of the rank-one pair of `u_a(1)`. -/
theorem rootForm_ne_zero (α : relativeRoots B.i) : rootForm B.i α ≠ 0 := by
  obtain ⟨-, q, -, -, hq, -⟩ := F.rankOne α α.2 1
  intro h
  have h2 := rootForm_oppositeFactorPairCorootClass B.isMaximalSplitTorus.isSplitSubtorus.1
    (F.u_mem α α.2 1) (F.u_one_ne_one α.2) hq
  rw [h, LinearMap.zero_apply] at h2
  norm_num at h2

/-- At a point where the value of `u_a(1)` vanishes, the affine functional `a(· - x)` is an
affine root: `u_a(1) ∈ U_ψ` has value `0`, so it is not in `U_{ψ+}`, and `U_{2a}(k) = {1}`. -/
theorem affineFunctional_mem_affineRoots {x : B.Apartment} (α : relativeRoots B.i)
    (hx : F.rootValue x α = 0) : B.apartment.affineFunctional α x 0 ∈ B.affineRoots := by
  have hval : x.val α (F.u α 1) = ((B.apartment.affineFunctional α x 0 x : ℝ) : WithTop ℝ) := by
    rw [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add,
      F.val_u_one x α.2, hx]
  refine ⟨α, rfl, fun hsub => ?_⟩
  have hmem : F.u α 1 ∈ B.apartment.affineRootGroup α (B.apartment.affineFunctional α x 0) :=
    (KPApartmentData.mem_affineRootGroup_iff (D := B.apartment)
      (KPApartmentData.affineFunctional_linear α x 0) x).2 ⟨F.u_mem α α.2 1, hval.ge⟩
  obtain ⟨p, hp, d, hd, hpd⟩ := hsub hmem
  have hbot : doubleRootGroupPoints B.i (α : characterLattice B.S) = ⊥ :=
    by simp [doubleRootGroupPoints, F.two_smul_not_mem α α.2]
  rw [SetLike.mem_coe, hbot, Subgroup.mem_bot] at hd
  change p * d = F.u α 1 at hpd
  rw [hd, mul_one] at hpd
  rw [SetLike.mem_coe, hpd] at hp
  obtain ⟨-, hlt⟩ := (KPApartmentData.mem_affineRootGroupPlus_iff (D := B.apartment)
    (KPApartmentData.affineFunctional_linear α x 0) x).1 hp
  rw [hval] at hlt
  exact lt_irrefl _ hlt

/-- **The point where all root values vanish is special.** -/
theorem isSpecialPoint {x : B.Apartment} (hx : ∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) :
    AffineRootSystem.IsSpecialPoint B.affineRoots x := by
  refine (AffineRootSystem.isSpecialPoint_iff_ker (fun ψ hψ => ?_) x).2 fun ψ hψ => ?_
  · obtain ⟨α, hα, -⟩ := hψ
    rw [hα]
    exact F.rootForm_ne_zero α
  · obtain ⟨α, hα, -⟩ := hψ
    refine ⟨B.apartment.affineFunctional α x 0,
      ⟨F.affineFunctional_mem_affineRoots α (hx α α.2), ?_⟩, ?_⟩
    · rw [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add]
    · rw [hα, KPApartmentData.affineFunctional_linear]

/-- **A split integral frame determines a special point whose one-stabilizer is `K`.** -/
theorem exists_isSpecialPoint_K_eq_oneStabilizer (hk : ∃ d : kˣ, d ^ 2 ≠ 1) :
    ∃ x : B.Apartment, (∀ a ∈ relativeRoots B.i, F.rootValue x a = 0) ∧
      B.IsSpecialPoint (B.apartmentMap x) ∧ F.K = B.oneStabilizer (B.apartmentMap x) := by
  obtain ⟨x, hx⟩ := F.exists_rootValue_eq_zero
  exact ⟨x, hx, B.apartment.isSpecialBuildingPoint_apartmentMap (F.isSpecialPoint hx),
    F.K_eq_oneStabilizer hk hx⟩

end SplitIntegralFrame

end IntegerValuationBuildingData

end Langlands.Geometry.Building
