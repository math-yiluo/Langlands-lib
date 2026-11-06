import Langlands.Shimura.LevelHecke
import Langlands.Representation.Induction.PermutationModule

/-! # Hecke algebras of levels over arbitrary rings -/

noncomputable section

universe t v w w'

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory Langlands.Induction

/-! ## Permutation modules and Frobenius reciprocity -/

section Algebraic

variable {G : Type v} [Group G] (R : Type t) [CommRing R]

/-- The permutation representation of `G` on `R[G/L]`, the finitely supported functions on
the left cosets `G ⧸ L`. -/
abbrev permRep (L : Subgroup G) : Representation R G (G ⧸ L →₀ R) :=
  permutation R G (G ⧸ L) R

/-- The `K`-fixed vectors of `R[G/L]`: the finitely supported functions on `G ⧸ L` that are
invariant under `K`. -/
abbrev HeckeSpace (K L : Subgroup G) : Type (max v t) :=
  fixedVectors (permRep R L) K

variable {R}

/-- The function `δ_L` with value `1` at the coset `L` and `0` elsewhere, fixed by `L`. -/
def unitElement (L : Subgroup G) : HeckeSpace R L L :=
  ⟨Finsupp.single ((1 : G) : G ⧸ L) 1, fun l => by
    change permutation R G (G ⧸ L) R (l : G) (Finsupp.single _ 1) = _
    rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    congr 1
    exact QuotientGroup.eq.mpr (by simp)⟩

@[simp] theorem unitElement_coe (L : Subgroup G) :
    (unitElement (R := R) L : G ⧸ L →₀ R) = Finsupp.single ((1 : G) : G ⧸ L) 1 := rfl

variable {V : Type w} [AddCommGroup V] [Module R V] (ρ : Representation R G V)

/-- For `v` fixed by `L`, the vector `ρ(x) v` attached to the coset `x L`; it does not depend on
the representative `x`. -/
def cosetVector {L : Subgroup G} (v : fixedVectors ρ L) (q : G ⧸ L) : V :=
  Quotient.liftOn' q (fun x => ρ x v) (fun a b hab => by
    have h : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp hab
    have e : b = a * (a⁻¹ * b) := by group
    change ρ a v = ρ b v
    rw [e, map_mul, Module.End.mul_apply]
    exact (congrArg (ρ a) (v.property ⟨_, h⟩)).symm)

@[simp] theorem cosetVector_mk {L : Subgroup G} (v : fixedVectors ρ L) (x : G) :
    cosetVector ρ v (x : G ⧸ L) = ρ x v := rfl

theorem cosetVector_smul {L : Subgroup G} (v : fixedVectors ρ L) (g : G) (q : G ⧸ L) :
    cosetVector ρ v (g • q) = ρ g (cosetVector ρ v q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetVector_mk, cosetVector_mk, map_mul,
      Module.End.mul_apply]

theorem cosetVector_add {L : Subgroup G} (v w : fixedVectors ρ L) (q : G ⧸ L) :
    cosetVector ρ (v + w) q = cosetVector ρ v q + cosetVector ρ w q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact map_add (ρ x) (v : V) (w : V)

theorem cosetVector_smul_vector {L : Subgroup G} (r : R) (v : fixedVectors ρ L) (q : G ⧸ L) :
    cosetVector ρ (r • v) q = r • cosetVector ρ v q := by
  induction q using QuotientGroup.induction_on with
  | H x => exact map_smul (ρ x) r (v : V)

/-- Frobenius reciprocity: for `v` fixed by `L`, the intertwining map `R[G/L] → V` sending
`δ_{xL}` to `ρ(x) v`. -/
def frobenius {L : Subgroup G} (v : fixedVectors ρ L) : (permRep R L).IntertwiningMap ρ where
  toLinearMap := Finsupp.linearCombination R (cosetVector ρ v)
  isIntertwining' g := by
    refine Finsupp.lhom_ext fun q r => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, permutation_single,
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, cosetVector_smul,
      map_smul]

theorem frobenius_apply {L : Subgroup G} (v : fixedVectors ρ L) (a : G ⧸ L →₀ R) :
    frobenius ρ v a = Finsupp.linearCombination R (cosetVector ρ v) a := rfl

@[simp] theorem frobenius_unitElement {L : Subgroup G} (v : fixedVectors ρ L) :
    frobenius ρ v (unitElement (R := R) L : G ⧸ L →₀ R) = v := by
  rw [frobenius_apply, unitElement_coe, Finsupp.linearCombination_single, one_smul,
    cosetVector_mk, map_one, Module.End.one_apply]

/-- Every intertwining map from `R[G/L]` is the Frobenius map of its value at `δ_L`. -/
theorem frobenius_eval {L : Subgroup G} (φ : (permRep R L).IntertwiningMap ρ)
    (hφ : φ (unitElement (R := R) L : G ⧸ L →₀ R) ∈ fixedVectors ρ L) :
    frobenius ρ ⟨φ (unitElement (R := R) L : G ⧸ L →₀ R), hφ⟩ = φ := by
  apply Representation.IntertwiningMap.ext
  refine Finsupp.lhom_ext fun q r => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    change Finsupp.linearCombination R _ (Finsupp.single _ r) = φ (Finsupp.single _ r)
    rw [Finsupp.linearCombination_single, cosetVector_mk]
    change r • ρ x (φ (Finsupp.single ((1 : G) : G ⧸ L) 1)) = φ (Finsupp.single (x : G ⧸ L) r)
    rw [← Representation.IntertwiningMap.isIntertwining _ _ φ, permutation_single,
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, ← map_smul, Finsupp.smul_single_one]

/-! ## The action of `R[G/L]^K` on fixed vectors -/

/-- The action of `a ∈ R[G/L]^K` on `L`-fixed vectors, `a • v = ∑_{xL} a(xL) ρ(x) v`, which is
fixed by `K`. -/
def heckeAct (K L : Subgroup G) :
    HeckeSpace R K L →ₗ[R] fixedVectors ρ L →ₗ[R] fixedVectors ρ K :=
  LinearMap.mk₂ R (fun a v => ⟨frobenius ρ v a, fun k => by
      change ρ (k : G) (frobenius ρ v a) = frobenius ρ v a
      rw [← Representation.IntertwiningMap.isIntertwining _ _ (frobenius ρ v)]
      exact congrArg (frobenius ρ v) (a.property k)⟩)
    (fun a b v => Subtype.ext (map_add (frobenius ρ v) (a : G ⧸ L →₀ R) b))
    (fun r a v => Subtype.ext (map_smul (frobenius ρ v) r (a : G ⧸ L →₀ R)))
    (fun a v w => Subtype.ext (by
      change Finsupp.linearCombination R (cosetVector ρ (v + w)) (a : G ⧸ L →₀ R) =
        Finsupp.linearCombination R (cosetVector ρ v) a +
          Finsupp.linearCombination R (cosetVector ρ w) a
      simp only [Finsupp.linearCombination_apply, cosetVector_add, smul_add, Finsupp.sum_add]))
    (fun r a v => Subtype.ext (by
      change Finsupp.linearCombination R (cosetVector ρ (r • v)) (a : G ⧸ L →₀ R) =
        r • Finsupp.linearCombination R (cosetVector ρ v) a
      simp only [Finsupp.linearCombination_apply, cosetVector_smul_vector, Finsupp.smul_sum]
      exact Finsupp.sum_congr fun _ _ => smul_comm _ _ _))

theorem heckeAct_coe (K L : Subgroup G) (a : HeckeSpace R K L) (v : fixedVectors ρ L) :
    (heckeAct ρ K L a v : V) = frobenius ρ v a := rfl

/-- The action as a sum over the support of `a`, with chosen coset representatives. -/
theorem heckeAct_apply (K L : Subgroup G) (a : HeckeSpace R K L) (v : fixedVectors ρ L) :
    (heckeAct ρ K L a v : V) =
      (a : G ⧸ L →₀ R).sum fun q r => r • ρ (Quotient.out q : G) v := by
  rw [heckeAct_coe, frobenius_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun q _ => ?_
  congr 1
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

/-- `δ_L` acts as the identity on `L`-fixed vectors. -/
@[simp] theorem heckeAct_unitElement (L : Subgroup G) (v : fixedVectors ρ L) :
    heckeAct ρ L L (unitElement L) v = v :=
  Subtype.ext (frobenius_unitElement ρ v)

theorem cosetVector_unitElement (M : Subgroup G) (q : G ⧸ M) :
    cosetVector (permRep R M) (unitElement M) q = Finsupp.single q 1 := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    change permutation R G (G ⧸ M) R x (Finsupp.single _ 1) = _
    rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- On `R[G/M]`, an element `a` of `R[G/M]^K` sends `δ_M` to `a`. -/
@[simp] theorem heckeAct_permRep_unitElement (K M : Subgroup G) (a : HeckeSpace R K M) :
    heckeAct (permRep R M) K M a (unitElement M) = a := by
  apply Subtype.ext
  change Finsupp.linearCombination R (cosetVector (permRep R M) (unitElement M))
    (a : G ⧸ M →₀ R) = a
  rw [show cosetVector (permRep R M) (unitElement M) = fun q => Finsupp.single q 1 from
    funext (cosetVector_unitElement M), Finsupp.linearCombination_apply]
  simp only [Finsupp.smul_single_one]
  exact Finsupp.sum_single _

section Naturality

variable {ρ} {W : Type w'} [AddCommGroup W] [Module R W] {σ : Representation R G W}

theorem cosetVector_map (f : ρ.IntertwiningMap σ) {L : Subgroup G} (v : fixedVectors ρ L)
    (q : G ⧸ L) : cosetVector σ (fixedVectorsMap f L v) q = f (cosetVector ρ v q) := by
  induction q using QuotientGroup.induction_on with
  | H x => exact (Representation.IntertwiningMap.isIntertwining _ _ f x (v : V)).symm

/-- The action commutes with intertwining maps. -/
theorem fixedVectorsMap_heckeAct (f : ρ.IntertwiningMap σ) (K L : Subgroup G)
    (a : HeckeSpace R K L) (v : fixedVectors ρ L) :
    fixedVectorsMap f K (heckeAct ρ K L a v) = heckeAct σ K L a (fixedVectorsMap f L v) := by
  apply Subtype.ext
  change f.toLinearMap (Finsupp.linearCombination R (cosetVector ρ v) (a : G ⧸ L →₀ R)) =
    Finsupp.linearCombination R (cosetVector σ (fixedVectorsMap f L v)) a
  rw [Finsupp.apply_linearCombination]
  congr 2
  funext q
  exact (cosetVector_map f v q).symm

end Naturality

/-- The action is associative: `a • (b • v) = (a • b) • v`, where `a • b` is the action of `a`
on `b ∈ R[G/M]^L ⊆ R[G/M]`. -/
theorem heckeAct_heckeAct (K L M : Subgroup G) (a : HeckeSpace R K L) (b : HeckeSpace R L M)
    (v : fixedVectors ρ M) :
    heckeAct ρ K L a (heckeAct ρ L M b v) =
      heckeAct ρ K M (heckeAct (permRep R M) K L a b) v := by
  have hb : heckeAct ρ L M b v = fixedVectorsMap (frobenius ρ v) L b := rfl
  rw [hb, ← fixedVectorsMap_heckeAct]
  rfl

/-! ## Convolution -/

variable (R) in
/-- The convolution `R[G/L]^K × R[G/M]^L → R[G/M]^K`, the action on the permutation
representation `R[G/M]`. -/
abbrev heckeMul (K L M : Subgroup G) :
    HeckeSpace R K L →ₗ[R] HeckeSpace R L M →ₗ[R] HeckeSpace R K M :=
  heckeAct (permRep R M) K L

/-- The convolution formula `(a * b)(z) = ∑_{yL} a(yL) b(y⁻¹ z)`. -/
theorem heckeMul_apply (K L M : Subgroup G) (a : HeckeSpace R K L) (b : HeckeSpace R L M)
    (z : G ⧸ M) :
    (heckeMul R K L M a b : G ⧸ M →₀ R) z =
      (a : G ⧸ L →₀ R).sum fun q r => r * (b : G ⧸ M →₀ R) ((Quotient.out q : G)⁻¹ • z) := by
  rw [heckeAct_apply, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun q _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  congr 1
  exact permutation_apply _ _ _

theorem heckeMul_assoc (K L M N : Subgroup G) (a : HeckeSpace R K L) (b : HeckeSpace R L M)
    (c : HeckeSpace R M N) :
    heckeMul R K M N (heckeMul R K L M a b) c = heckeMul R K L N a (heckeMul R L M N b c) :=
  (heckeAct_heckeAct (permRep R N) K L M a b c).symm

/-! ## The Hecke algebra of a subgroup -/

variable (R) in
/-- The Hecke algebra of `K` over `R`: the `K`-fixed vectors of `R[G/K]` with convolution. -/
def LevelHeckeAlgebra (K : Subgroup G) : Type (max v t) := HeckeSpace R K K

namespace LevelHeckeAlgebra

variable (K : Subgroup G)

instance : AddCommGroup (LevelHeckeAlgebra R K) :=
  inferInstanceAs (AddCommGroup (HeckeSpace R K K))

instance : Module R (LevelHeckeAlgebra R K) :=
  inferInstanceAs (Module R (HeckeSpace R K K))

/-- An element of the Hecke algebra from a `K`-fixed vector of `R[G/K]`. -/
def ofHeckeSpace : HeckeSpace R K K ≃ₗ[R] LevelHeckeAlgebra R K := LinearEquiv.refl R _

instance : Ring (LevelHeckeAlgebra R K) :=
  { (inferInstance : AddCommGroup (LevelHeckeAlgebra R K)) with
    mul := fun a b => heckeMul R K K K a b
    one := unitElement K
    mul_assoc := fun a b c => heckeMul_assoc K K K K a b c
    one_mul := fun a => heckeAct_unitElement (permRep R K) K a
    mul_one := fun a => heckeAct_permRep_unitElement K K a
    left_distrib := fun a b c => map_add (heckeMul R K K K a) b c
    right_distrib := fun a b c => LinearMap.map_add₂ (heckeMul R K K K) a b c
    zero_mul := fun a => LinearMap.map_zero₂ (heckeMul R K K K) a
    mul_zero := fun a => map_zero (heckeMul R K K K a) }

theorem mul_def (a b : LevelHeckeAlgebra R K) : a * b = heckeMul R K K K a b := rfl

theorem one_def : (1 : LevelHeckeAlgebra R K) = unitElement K := rfl

instance : Algebra R (LevelHeckeAlgebra R K) :=
  Algebra.ofModule (fun r a b => LinearMap.map_smul₂ (heckeMul R K K K) r a b)
    (fun r a b => map_smul (heckeMul R K K K a) r b)

/-- The `K`-fixed vectors of a representation are a module over the Hecke algebra of `K`. -/
instance instModuleFixedVectors : Module (LevelHeckeAlgebra R K) (fixedVectors ρ K) where
  smul a v := heckeAct ρ K K a v
  one_smul v := heckeAct_unitElement ρ K v
  mul_smul a b v := (heckeAct_heckeAct ρ K K K a b v).symm
  smul_zero a := map_zero (heckeAct ρ K K a)
  smul_add a v w := map_add (heckeAct ρ K K a) v w
  add_smul a b v := LinearMap.map_add₂ (heckeAct ρ K K) a b v
  zero_smul v := LinearMap.map_zero₂ (heckeAct ρ K K) v

theorem smul_def (a : LevelHeckeAlgebra R K) (v : fixedVectors ρ K) :
    a • v = heckeAct ρ K K a v := rfl

instance : IsScalarTower R (LevelHeckeAlgebra R K) (fixedVectors ρ K) :=
  ⟨fun r a v => LinearMap.map_smul₂ (heckeAct ρ K K) r a v⟩

end LevelHeckeAlgebra

end Algebraic

/-! ## Double-coset elements for compact open levels -/

section Levels

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (R : Type t)
  [CommRing R]

/-- The point `k g L` of `G ⧸ L` attached to the coset of `k` in `K / (K ∩ g L g⁻¹)`. -/
def cosetPoint (K L : CompactOpenLevel G) (g : G) (q : HeckeCosets K L g) : G ⧸ L.subgroup :=
  Quotient.liftOn' q (fun k : K.subgroup => (((k : G) * g : G) : G ⧸ L.subgroup))
    (fun a b hab => by
      have hm := mem_heckeLevel.mp
        (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))
      apply QuotientGroup.eq.mpr
      have e : ((a : G) * g)⁻¹ * ((b : G) * g) = g⁻¹ * ((a⁻¹ * b : K.subgroup) : G) * g := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact hm.2)

@[simp] theorem cosetPoint_mk (K L : CompactOpenLevel G) (g : G) (k : K.subgroup) :
    cosetPoint K L g (k : HeckeCosets K L g) = (((k : G) * g : G) : G ⧸ L.subgroup) := rfl

theorem cosetPoint_injective (K L : CompactOpenLevel G) (g : G) :
    Function.Injective (cosetPoint K L g) := by
  intro q₁ q₂ h
  induction q₁ using QuotientGroup.induction_on with
  | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
      have h' := QuotientGroup.eq.mp h
      apply QuotientGroup.eq.mpr
      apply Subgroup.mem_subgroupOf.mpr
      apply mem_heckeLevel.mpr
      refine ⟨(a⁻¹ * b).property, ?_⟩
      have e : ((a : G) * g)⁻¹ * ((b : G) * g) = g⁻¹ * ((a⁻¹ * b : K.subgroup) : G) * g := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [← e]
      exact h'

/-- The points `k g L` are exactly the `K`-orbit of `g L` in `G ⧸ L`, that is, the double coset
`K g L` modulo `L`. -/
theorem mem_range_cosetPoint (K L : CompactOpenLevel G) (g : G) (z : G ⧸ L.subgroup) :
    z ∈ Set.range (cosetPoint K L g) ↔
      z ∈ MulAction.orbit K.subgroup ((g : G) : G ⧸ L.subgroup) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H k => exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : HeckeCosets K L g), rfl⟩

/-- The element `[K g L] δ_L = ∑_{k ∈ K / (K ∩ g L g⁻¹)} δ_{k g L}` of `R[G/L]^K`. -/
def heckeElement (K L : CompactOpenLevel G) (g : G) : HeckeSpace R K.subgroup L.subgroup :=
  heckeOperator (permRep R L.subgroup) K L g (unitElement L.subgroup)

theorem heckeElement_coe (K L : CompactOpenLevel G) (g : G) :
    (heckeElement R K L g : G ⧸ L.subgroup →₀ R) =
      ∑ q : HeckeCosets K L g, Finsupp.single (cosetPoint K L g q) 1 := by
  rw [heckeElement, heckeOperator_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H k =>
    change permutation R G (G ⧸ L.subgroup) R ((k : G) * g) (Finsupp.single _ 1) = _
    rw [permutation_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rfl

open Classical in
/-- The element attached to `K g L` is the indicator function of the double coset `K g L`
modulo `L`. -/
theorem heckeElement_apply (K L : CompactOpenLevel G) (g : G) (z : G ⧸ L.subgroup) :
    (heckeElement R K L g : G ⧸ L.subgroup →₀ R) z =
      if z ∈ MulAction.orbit K.subgroup ((g : G) : G ⧸ L.subgroup) then 1 else 0 := by
  rw [heckeElement_coe, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with hz
  · obtain ⟨q₀, rfl⟩ := (mem_range_cosetPoint K L g _).mpr hz
    rw [Finset.sum_eq_single q₀
      (fun q _ hq => ite_eq_right fun h => hq (cosetPoint_injective K L g h))
      (fun h => absurd (Finset.mem_univ q₀) h), ite_eq_left rfl]
  · refine Finset.sum_eq_zero fun q _ => ite_eq_right fun h => hz ?_
    exact (mem_range_cosetPoint K L g z).mp ⟨q, h⟩

variable {R}
variable {V : Type w} [AddCommGroup V] [Module R V] (ρ : Representation R G V)

/-- The action of the element attached to `K g L` is the double-coset operator `[K g L]`. -/
theorem heckeAct_heckeElement (K L : CompactOpenLevel G) (g : G) (v : fixedVectors ρ L.subgroup) :
    heckeAct ρ K.subgroup L.subgroup (heckeElement R K L g) v = heckeOperator ρ K L g v := by
  have h := LinearMap.congr_fun (fixedVectorsMap_heckeOperator K L g (frobenius ρ v))
    (unitElement L.subgroup)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  have hu : fixedVectorsMap (frobenius ρ v) L.subgroup (unitElement L.subgroup) = v :=
    Subtype.ext (frobenius_unitElement ρ v)
  rw [hu] at h
  rw [← h]
  rfl

/-- The composite of two double-coset operators is the action of the convolution of their
elements: `[K g L] ∘ [L h M] = ([K g L] * [L h M]) •`. -/
theorem heckeOperator_comp_heckeOperator (K L M : CompactOpenLevel G) (g h : G) :
    (heckeOperator ρ K L g).comp (heckeOperator ρ L M h) =
      heckeAct ρ K.subgroup M.subgroup
        (heckeMul R K.subgroup L.subgroup M.subgroup (heckeElement R K L g)
          (heckeElement R L M h)) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, ← heckeAct_heckeElement, ← heckeAct_heckeElement,
    heckeAct_heckeAct]

/-- The element of the Hecke algebra of `K` attached to the double coset `K g K`. -/
def doubleCoset (K : CompactOpenLevel G) (g : G) : LevelHeckeAlgebra R K.subgroup :=
  heckeElement R K K g

theorem doubleCoset_smul (K : CompactOpenLevel G) (g : G) (v : fixedVectors ρ K.subgroup) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) • v = heckeOperator ρ K K g v :=
  heckeAct_heckeElement ρ K K g v

theorem doubleCoset_one (K : CompactOpenLevel G) :
    (doubleCoset K 1 : LevelHeckeAlgebra R K.subgroup) = 1 := by
  change heckeOperator (permRep R K.subgroup) K K 1 (unitElement K.subgroup) = unitElement _
  rw [heckeOperator_self, LinearMap.id_apply]

/-- `[K g K] ∘ [K h K]` is the action of the product of the double-coset elements. -/
theorem heckeOperator_comp_heckeOperator_self (K : CompactOpenLevel G) (g h : G)
    (v : fixedVectors ρ K.subgroup) :
    heckeOperator ρ K K g (heckeOperator ρ K K h v) =
      ((doubleCoset K g * doubleCoset K h : LevelHeckeAlgebra R K.subgroup)) • v := by
  rw [mul_smul, doubleCoset_smul, doubleCoset_smul]

end Levels

/-! ## Smooth representations -/

section Smooth

variable {G : Type v} [Group G] [TopologicalSpace G] (R : Type t) [CommRing R]

/-- The `K`-fixed vectors of smooth representations, as modules over the Hecke algebra of `K`. -/
def heckeModuleFunctor (K : Subgroup G) :
    SmoothRep.{t, v, w} R G ⥤ ModuleCat.{w} (LevelHeckeAlgebra R K) where
  obj A := ModuleCat.of (LevelHeckeAlgebra R K) (fixedVectors A.obj.ρ K)
  map f := ModuleCat.ofHom
    { toFun := fixedVectorsMap f.hom.hom K
      map_add' := map_add (fixedVectorsMap f.hom.hom K)
      map_smul' := fun a v => fixedVectorsMap_heckeAct f.hom.hom K K a v }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem heckeModuleFunctor_obj (K : Subgroup G) (A : SmoothRep.{t, v, w} R G) :
    (heckeModuleFunctor R K).obj A =
      ModuleCat.of (LevelHeckeAlgebra R K) (fixedVectors A.obj.ρ K) := rfl

end Smooth

end Langlands.Shimura.LevelHecke
