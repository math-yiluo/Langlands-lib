import Langlands.Shimura.LevelHeckeAlgebra
import Mathlib.GroupTheory.DoubleCoset

/-! # Double-coset bases, structure constants and degrees of level Hecke algebras -/

noncomputable section

universe t v x

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory Langlands.Induction

/-! ## Invariant functions on a set whose orbits are finite -/

section Orbits

variable {G : Type v} [Group G] {X : Type x} [MulAction G X] {R : Type t} [CommRing R]
variable {K : Subgroup G}

/-- A `K`-invariant finitely supported function takes the same value at `k • x` and `x`. -/
theorem apply_smul_of_mem_fixedVectors {f : X →₀ R}
    (hf : f ∈ fixedVectors (permutation R G X R) K) (k : K) (y : X) : f (k • y) = f y := by
  have h : permutation R G X R (k : G) f (k • y) = f (k • y) :=
    congrArg (fun φ : X →₀ R => φ (k • y)) (hf k)
  rw [permutation_apply, Subgroup.smul_def, inv_smul_smul] at h
  exact h.symm

/-- A `K`-invariant finitely supported function is constant on `K`-orbits. -/
theorem apply_eq_of_mem_orbit {f : X →₀ R} (hf : f ∈ fixedVectors (permutation R G X R) K)
    {y z : X} (h : z ∈ MulAction.orbit K y) : f z = f y := by
  obtain ⟨k, rfl⟩ := h
  exact apply_smul_of_mem_fixedVectors hf k y

theorem mem_orbit_out_of_mk_eq {y : X} {O : MulAction.orbitRel.Quotient K X}
    (h : (Quotient.mk'' y : MulAction.orbitRel.Quotient K X) = O) :
    y ∈ MulAction.orbit K (Quotient.out O) := by
  rw [← MulAction.orbitRel_apply]
  exact Quotient.eq''.mp (h.trans (Quotient.out_eq' O).symm)

theorem out_mk_mem_orbit (y : X) :
    Quotient.out (Quotient.mk'' y : MulAction.orbitRel.Quotient K X) ∈ MulAction.orbit K y := by
  rw [← MulAction.orbitRel_apply]
  exact Quotient.eq''.mp (Quotient.out_eq' _)

variable (R K)

open Classical in
/-- The indicator function `1_O` of a `K`-orbit `O`, finitely supported when the orbits are
finite. -/
def orbitIndicator (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (O : MulAction.orbitRel.Quotient K X) : X →₀ R :=
  Finsupp.onFinset (hK (Quotient.out O)).toFinset
    (fun y => if (Quotient.mk'' y : MulAction.orbitRel.Quotient K X) = O then 1 else 0)
    (fun y hy => by
      rw [Set.Finite.mem_toFinset]
      by_contra h'
      exact hy (ite_eq_right fun hyO => h' (mem_orbit_out_of_mk_eq hyO)))

variable {R K}

open Classical in
theorem orbitIndicator_apply (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (O : MulAction.orbitRel.Quotient K X) (y : X) :
    orbitIndicator R K hK O y =
      if (Quotient.mk'' y : MulAction.orbitRel.Quotient K X) = O then 1 else 0 :=
  Finsupp.onFinset_apply

theorem orbitIndicator_mem (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (O : MulAction.orbitRel.Quotient K X) :
    orbitIndicator R K hK O ∈ fixedVectors (permutation R G X R) K := by
  intro k
  ext y
  change permutation R G X R (k : G) (orbitIndicator R K hK O) y = _
  rw [permutation_apply, orbitIndicator_apply, orbitIndicator_apply]
  have e : (Quotient.mk'' ((k : G)⁻¹ • y) : MulAction.orbitRel.Quotient K X) =
      Quotient.mk'' y := by
    rw [← Subgroup.coe_inv, ← Subgroup.smul_def]
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  rw [e]

variable (R K) in
/-- The coordinates of a `K`-invariant function: its values at chosen orbit representatives. -/
def orbitCoordinates :
    fixedVectors (permutation R G X R) K →ₗ[R] (MulAction.orbitRel.Quotient K X →₀ R) where
  toFun f := by
    classical
    exact Finsupp.onFinset ((f : X →₀ R).support.image Quotient.mk'')
      (fun O => (f : X →₀ R) (Quotient.out O))
      (fun O hO => Finset.mem_image.mpr
        ⟨Quotient.out O, Finsupp.mem_support_iff.mpr hO, Quotient.out_eq' O⟩)
  map_add' f g := by
    ext O
    simp only [Finsupp.onFinset_apply, Finsupp.add_apply, Submodule.coe_add]
  map_smul' r f := by
    ext O
    simp only [Finsupp.onFinset_apply, Finsupp.smul_apply, Submodule.coe_smul,
      RingHom.id_apply]

theorem orbitCoordinates_apply (f : fixedVectors (permutation R G X R) K)
    (O : MulAction.orbitRel.Quotient K X) :
    orbitCoordinates R K f O = (f : X →₀ R) (Quotient.out O) :=
  rfl

variable (R K) in
/-- The `K`-invariant function `∑_O c(O) 1_O` attached to finitely supported coefficients on the
orbits. -/
def orbitSum (hK : ∀ y : X, (MulAction.orbit K y).Finite) :
    (MulAction.orbitRel.Quotient K X →₀ R) →ₗ[R] fixedVectors (permutation R G X R) K :=
  Finsupp.linearCombination R fun O => ⟨orbitIndicator R K hK O, orbitIndicator_mem hK O⟩

theorem orbitSum_apply (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (c : MulAction.orbitRel.Quotient K X →₀ R) (y : X) :
    (orbitSum R K hK c : X →₀ R) y = c (Quotient.mk'' y) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add, Submodule.coe_add, Finsupp.add_apply, hc, hd, Finsupp.add_apply]
  | single O r =>
    rw [orbitSum, Finsupp.linearCombination_single, Submodule.coe_smul, Finsupp.smul_apply,
      orbitIndicator_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : (Quotient.mk'' y : MulAction.orbitRel.Quotient K X) = O
    · rw [ite_eq_left h, ite_eq_left h.symm, mul_one]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.symm, mul_zero]

variable (R K) in
/-- `K`-invariant finitely supported functions on `X` are the finitely supported functions on the
`K`-orbits, when every orbit is finite. -/
def orbitEquiv (hK : ∀ y : X, (MulAction.orbit K y).Finite) :
    fixedVectors (permutation R G X R) K ≃ₗ[R] (MulAction.orbitRel.Quotient K X →₀ R) :=
  { orbitCoordinates R K with
    invFun := orbitSum R K hK
    left_inv := fun f => by
      apply Subtype.ext
      ext y
      change (orbitSum R K hK (orbitCoordinates R K f) : X →₀ R) y = _
      rw [orbitSum_apply, orbitCoordinates_apply]
      exact apply_eq_of_mem_orbit f.property (out_mk_mem_orbit y)
    right_inv := fun c => by
      ext O
      change orbitCoordinates R K (orbitSum R K hK c) O = c O
      rw [orbitCoordinates_apply, orbitSum_apply, Quotient.out_eq'] }

variable (R K) in
/-- The basis of the `K`-invariant finitely supported functions given by the orbit indicators. -/
def orbitBasis (hK : ∀ y : X, (MulAction.orbit K y).Finite) :
    Module.Basis (MulAction.orbitRel.Quotient K X) R (fixedVectors (permutation R G X R) K) :=
  Module.Basis.ofRepr (orbitEquiv R K hK)

theorem orbitBasis_coe (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (O : MulAction.orbitRel.Quotient K X) :
    (orbitBasis R K hK O : X →₀ R) = orbitIndicator R K hK O := by
  rw [orbitBasis, Module.Basis.coe_ofRepr]
  change ((orbitSum R K hK (Finsupp.single O 1) : _) : X →₀ R) = _
  rw [orbitSum, Finsupp.linearCombination_single, one_smul]

theorem orbitBasis_repr_apply (hK : ∀ y : X, (MulAction.orbit K y).Finite)
    (f : fixedVectors (permutation R G X R) K) (O : MulAction.orbitRel.Quotient K X) :
    (orbitBasis R K hK).repr f O = (f : X →₀ R) (Quotient.out O) :=
  orbitCoordinates_apply f O

end Orbits

/-! ## Orbits on cosets and double cosets -/

section DoubleCosets

variable {G : Type v} [Group G]

/-- `z ∈ K h L` exactly when the coset `z L` lies in the `K`-orbit of `h L`. -/
theorem mk_mem_orbit_iff (K L : Subgroup G) (h z : G) :
    ((z : G) : G ⧸ L) ∈ MulAction.orbit K ((h : G) : G ⧸ L) ↔
      z ∈ DoubleCoset.doubleCoset h (K : Set G) L := by
  rw [MulAction.mem_orbit_iff, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨k, hk⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul] at hk
    have hm : ((k : G) * h)⁻¹ * z ∈ L := QuotientGroup.eq.mp hk
    refine ⟨k, k.property, ((k : G) * h)⁻¹ * z, hm, ?_⟩
    group
  · rintro ⟨k, hk, l, hl, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul]
    apply QuotientGroup.eq.mpr
    have e : (k * h)⁻¹ * (k * h * l) = l := by group
    rw [Subgroup.coe_mk, e]
    exact hl

/-- The orbits of `K` on `G ⧸ L` are the double cosets `K \ G / L`. -/
def orbitDoubleCosetEquiv (K L : Subgroup G) :
    MulAction.orbitRel.Quotient K (G ⧸ L) ≃ DoubleCoset.Quotient (K : Set G) L where
  toFun := Quotient.lift
    (fun z : G ⧸ L => Quotient.liftOn' z (fun g => DoubleCoset.mk K L g)
      (fun a b hab => DoubleCoset.eq.mpr
        ⟨1, K.one_mem, a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩))
    (fun z w hzw => by
      induction z using QuotientGroup.induction_on with
      | H a =>
        induction w using QuotientGroup.induction_on with
        | H b =>
          have hab : ((a : G) : G ⧸ L) ∈ MulAction.orbit K ((b : G) : G ⧸ L) :=
            MulAction.orbitRel_apply.mp hzw
          rw [mk_mem_orbit_iff, DoubleCoset.mem_doubleCoset] at hab
          obtain ⟨k, hk, l, hl, rfl⟩ := hab
          exact (DoubleCoset.eq.mpr ⟨k, hk, l, hl, rfl⟩).symm)
  invFun := Quotient.lift
    (fun g : G => (Quotient.mk'' ((g : G) : G ⧸ L) : MulAction.orbitRel.Quotient K (G ⧸ L)))
    (fun a b hab => by
      obtain ⟨k, hk, l, hl, rfl⟩ := DoubleCoset.rel_iff.mp hab
      apply Quotient.eq''.mpr
      apply MulAction.orbitRel_apply.mpr
      exact (mk_mem_orbit_iff K L _ _).mpr (DoubleCoset.mem_doubleCoset.mpr
        ⟨k⁻¹, K.inv_mem hk, l⁻¹, L.inv_mem hl, by group⟩))
  left_inv O := by
    induction O using Quotient.inductionOn' with
    | h z =>
      induction z using QuotientGroup.induction_on with
      | H a => rfl
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => rfl

@[simp] theorem orbitDoubleCosetEquiv_mk (K L : Subgroup G) (g : G) :
    orbitDoubleCosetEquiv K L (Quotient.mk'' ((g : G) : G ⧸ L)) = DoubleCoset.mk K L g := rfl

@[simp] theorem orbitDoubleCosetEquiv_symm_mk (K L : Subgroup G) (g : G) :
    (orbitDoubleCosetEquiv K L).symm (DoubleCoset.mk K L g) =
      Quotient.mk'' ((g : G) : G ⧸ L) := rfl

/-- Membership `y⁻¹ x ∈ L h M` is unchanged when `y` is multiplied on the right by an element
of `L`. -/
theorem inv_mul_mem_doubleCoset_mul_right (L M : Subgroup G) (h x y : G) {l : G} (hl : l ∈ L) :
    (y * l)⁻¹ * x ∈ DoubleCoset.doubleCoset h (L : Set G) M ↔
      y⁻¹ * x ∈ DoubleCoset.doubleCoset h (L : Set G) M := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨l * a, L.mul_mem hl ha, b, hb, ?_⟩
    rw [show l * a * h * b = l * (a * h * b) by group, ← e]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨l⁻¹ * a, L.mul_mem (L.inv_mem hl) ha, b, hb, ?_⟩
    rw [show l⁻¹ * a * h * b = l⁻¹ * (a * h * b) by group, ← e]
    group

end DoubleCosets

/-! ## The double-coset basis of `R[G/L]^K` -/

section Levels

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type t) [CommRing R]

/-- Each `K`-orbit on `G ⧸ L` is finite: it is the image of `K / (K ∩ g L g⁻¹)`. -/
theorem finite_orbit (K L : CompactOpenLevel G) (z : G ⧸ L.subgroup) :
    (MulAction.orbit K.subgroup z).Finite := by
  induction z using QuotientGroup.induction_on with
  | H g =>
    have e : MulAction.orbit K.subgroup ((g : G) : G ⧸ L.subgroup) =
        Set.range (cosetPoint K L g) := by
      ext z
      exact (mem_range_cosetPoint K L g z).symm
    rw [e]
    exact Set.finite_range _

/-- The basis of `R[G/L]^K` indexed by the double cosets `K \ G / L`. -/
def heckeBasis (K L : CompactOpenLevel G) :
    Module.Basis (DoubleCoset.Quotient (K.subgroup : Set G) L.subgroup) R
      (HeckeSpace R K.subgroup L.subgroup) :=
  (orbitBasis R K.subgroup (finite_orbit K L)).reindex
    (orbitDoubleCosetEquiv K.subgroup L.subgroup)

/-- The basis vector attached to the double coset `K g L` is `[K g L] δ_L`. -/
theorem heckeBasis_mk (K L : CompactOpenLevel G) (g : G) :
    heckeBasis R K L (DoubleCoset.mk K.subgroup L.subgroup g) = heckeElement R K L g := by
  classical
  rw [heckeBasis, Module.Basis.reindex_apply, orbitDoubleCosetEquiv_symm_mk]
  apply Subtype.ext
  ext z
  rw [orbitBasis_coe, orbitIndicator_apply, heckeElement_apply]
  exact if_congr (Quotient.eq''.trans MulAction.orbitRel_apply) rfl rfl

/-- The coordinate of `a ∈ R[G/L]^K` at the double coset `K g L` is the value `a(g L)`. -/
theorem heckeBasis_repr_mk (K L : CompactOpenLevel G) (a : HeckeSpace R K.subgroup L.subgroup)
    (g : G) :
    (heckeBasis R K L).repr a (DoubleCoset.mk K.subgroup L.subgroup g) =
      (a : G ⧸ L.subgroup →₀ R) (g : G ⧸ L.subgroup) := by
  rw [heckeBasis, Module.Basis.repr_reindex_apply, orbitDoubleCosetEquiv_symm_mk,
    orbitBasis_repr_apply]
  exact apply_eq_of_mem_orbit a.property (out_mk_mem_orbit _)

/-- `[K g L] δ_L` depends only on the double coset `K g L`. -/
theorem heckeElement_eq_of_mk_eq (K L : CompactOpenLevel G) {g g' : G}
    (h : DoubleCoset.mk K.subgroup L.subgroup g = DoubleCoset.mk K.subgroup L.subgroup g') :
    heckeElement R K L g = heckeElement R K L g' := by
  rw [← heckeBasis_mk, h, heckeBasis_mk]

/-- Over a nontrivial ring, `[K g L] δ_L = [K g' L] δ_L` exactly when `K g L = K g' L`. -/
theorem heckeElement_eq_iff [Nontrivial R] (K L : CompactOpenLevel G) (g g' : G) :
    heckeElement R K L g = heckeElement R K L g' ↔
      DoubleCoset.mk K.subgroup L.subgroup g = DoubleCoset.mk K.subgroup L.subgroup g' := by
  rw [← heckeBasis_mk, ← heckeBasis_mk]
  exact (heckeBasis R K L).injective.eq_iff

theorem range_heckeElement (K L : CompactOpenLevel G) :
    Set.range (heckeElement R K L) = Set.range (heckeBasis R K L) := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, heckeBasis_mk R K L g⟩
  · rintro ⟨q, rfl⟩
    refine ⟨Quotient.out q, ?_⟩
    rw [← heckeBasis_mk, DoubleCoset.out_eq']

/-- The elements `[K g L] δ_L` span `R[G/L]^K`. -/
theorem span_heckeElement (K L : CompactOpenLevel G) :
    Submodule.span R (Set.range (heckeElement R K L)) = ⊤ := by
  rw [range_heckeElement]
  exact (heckeBasis R K L).span_eq

instance (K L : CompactOpenLevel G) : Module.Free R (HeckeSpace R K.subgroup L.subgroup) :=
  Module.Free.of_basis (heckeBasis R K L)

/-! ## Structure constants -/

open Classical in
/-- The structure constant `c(g, h; x)`: the number of cosets in `K / (K ∩ g L g⁻¹)`, that is of
cosets `y L ⊆ K g L` with `y = k g`, such that `y⁻¹ x ∈ L h M`. The chosen representative `k` of
each coset does not matter (`inv_mul_mem_doubleCoset_mul_right`). -/
def heckeStructureConstant (K L M : CompactOpenLevel G) (g h x : G) : ℕ :=
  (Finset.univ.filter fun q : HeckeCosets K L g =>
    (((Quotient.out q : K.subgroup) : G) * g)⁻¹ * x ∈
      DoubleCoset.doubleCoset h (L.subgroup : Set G) M.subgroup).card

/-- The convolution of `[K g L] δ_L` and `[L h M] δ_M` takes the value `c(g, h; x)` at `x M`. -/
theorem heckeMul_heckeElement_apply (K L M : CompactOpenLevel G) (g h x : G) :
    (heckeMul R K.subgroup L.subgroup M.subgroup (heckeElement R K L g) (heckeElement R L M h) :
        G ⧸ M.subgroup →₀ R) (x : G ⧸ M.subgroup) =
      (heckeStructureConstant K L M g h x : R) := by
  classical
  rw [heckeAct_coe, frobenius_apply, heckeElement_coe, map_sum, Finsupp.finsetSum_apply,
    heckeStructureConstant, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finsupp.linearCombination_single, one_smul]
  have hq : cosetPoint K L g q =
      ((((Quotient.out q : K.subgroup) : G) * g : G) : G ⧸ L.subgroup) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq, cosetVector_mk]
  change permutation R G (G ⧸ M.subgroup) R _ _ _ = _
  rw [permutation_apply, MulAction.Quotient.smul_mk, smul_eq_mul, heckeElement_apply]
  exact if_congr (mk_mem_orbit_iff L.subgroup M.subgroup h _) rfl rfl

/-- In the double-coset basis, the coordinates of `[K g L] δ_L * [L h M] δ_M` are the structure
constants. -/
theorem heckeBasis_repr_heckeMul (K L M : CompactOpenLevel G) (g h x : G) :
    (heckeBasis R K M).repr
        (heckeMul R K.subgroup L.subgroup M.subgroup (heckeElement R K L g)
          (heckeElement R L M h)) (DoubleCoset.mk K.subgroup M.subgroup x) =
      (heckeStructureConstant K L M g h x : R) := by
  rw [heckeBasis_repr_mk, heckeMul_heckeElement_apply]

/-- `[K g L] δ_L * [L h M] δ_M = ∑ c(g, h; x) [K x M] δ_M`, the finite sum running over the double
cosets `K x M` in the support of the product, with chosen representatives `x`. -/
theorem heckeMul_heckeElement (K L M : CompactOpenLevel G) (g h : G) :
    heckeMul R K.subgroup L.subgroup M.subgroup (heckeElement R K L g) (heckeElement R L M h) =
      ∑ q ∈ ((heckeBasis R K M).repr (heckeMul R K.subgroup L.subgroup M.subgroup
          (heckeElement R K L g) (heckeElement R L M h))).support,
        (heckeStructureConstant K L M g h (Quotient.out q) : R) •
          heckeElement R K M (Quotient.out q) := by
  conv_lhs => rw [← (heckeBasis R K M).linearCombination_repr (heckeMul R K.subgroup L.subgroup
    M.subgroup (heckeElement R K L g) (heckeElement R L M h))]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_lhs => rw [← DoubleCoset.out_eq' q]
  rw [heckeBasis_repr_heckeMul, heckeBasis_mk]

/-! ## The Hecke algebra of a level -/

/-- The basis of the Hecke algebra of `K` indexed by the double cosets `K \ G / K`. -/
def heckeAlgebraBasis (K : CompactOpenLevel G) :
    Module.Basis (DoubleCoset.Quotient (K.subgroup : Set G) K.subgroup) R
      (LevelHeckeAlgebra R K.subgroup) :=
  (heckeBasis R K K).map (LevelHeckeAlgebra.ofHeckeSpace K.subgroup)

theorem heckeAlgebraBasis_mk (K : CompactOpenLevel G) (g : G) :
    heckeAlgebraBasis R K (DoubleCoset.mk K.subgroup K.subgroup g) = doubleCoset K g := by
  rw [heckeAlgebraBasis, Module.Basis.map_apply, heckeBasis_mk]
  rfl

theorem doubleCoset_eq_of_mk_eq (K : CompactOpenLevel G) {g g' : G}
    (h : DoubleCoset.mk K.subgroup K.subgroup g = DoubleCoset.mk K.subgroup K.subgroup g') :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) = doubleCoset K g' :=
  heckeElement_eq_of_mk_eq R K K h

theorem doubleCoset_eq_iff [Nontrivial R] (K : CompactOpenLevel G) (g g' : G) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) = doubleCoset K g' ↔
      DoubleCoset.mk K.subgroup K.subgroup g = DoubleCoset.mk K.subgroup K.subgroup g' :=
  heckeElement_eq_iff R K K g g'

/-- The elements `[K g K]` span the Hecke algebra of `K`. -/
theorem span_doubleCoset (K : CompactOpenLevel G) :
    Submodule.span R (Set.range fun g : G => (doubleCoset K g : LevelHeckeAlgebra R K.subgroup)) =
      ⊤ := by
  have e : (Set.range fun g : G => (doubleCoset K g : LevelHeckeAlgebra R K.subgroup)) =
      Set.range (heckeAlgebraBasis R K) := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨_, heckeAlgebraBasis_mk R K g⟩
    · rintro ⟨q, rfl⟩
      refine ⟨Quotient.out q, ?_⟩
      dsimp only
      rw [← heckeAlgebraBasis_mk, DoubleCoset.out_eq']
  rw [e]
  exact (heckeAlgebraBasis R K).span_eq

/-- `[K g K] * [K h K] = ∑ c(g, h; x) [K x K]` over the double cosets in the support of the
product. -/
theorem doubleCoset_mul_doubleCoset (K : CompactOpenLevel G) (g h : G) :
    (doubleCoset K g * doubleCoset K h : LevelHeckeAlgebra R K.subgroup) =
      ∑ q ∈ ((heckeBasis R K K).repr (heckeMul R K.subgroup K.subgroup K.subgroup
          (heckeElement R K K g) (heckeElement R K K h))).support,
        (heckeStructureConstant K K K g h (Quotient.out q) : R) •
          doubleCoset K (Quotient.out q) :=
  heckeMul_heckeElement R K K K g h

end Levels

/-! ## Degrees -/

section Degree

variable {G : Type v} [Group G] (R : Type t) [CommRing R]

/-- The degree `deg a = ∑_{y L} a(y L)` of `a ∈ R[G/L]^K`. -/
def heckeDegree (K L : Subgroup G) : HeckeSpace R K L →ₗ[R] R :=
  (Finsupp.linearCombination R fun _ : G ⧸ L => (1 : R)).comp
    (fixedVectors (permRep R L) K).subtype

theorem heckeDegree_apply (K L : Subgroup G) (a : HeckeSpace R K L) :
    heckeDegree R K L a = (a : G ⧸ L →₀ R).sum fun _ r => r := by
  rw [heckeDegree, LinearMap.comp_apply, Submodule.subtype_apply,
    Finsupp.linearCombination_apply]
  simp only [smul_eq_mul, mul_one]

variable {R}

/-- On the trivial representation `R`, an element of `R[G/L]^K` acts by multiplication by its
degree. -/
theorem heckeAct_trivial (K L : Subgroup G) (a : HeckeSpace R K L)
    (r : fixedVectors (Representation.trivial R G R) L) :
    (heckeAct (Representation.trivial R G R) K L a r : R) = heckeDegree R K L a * r := by
  rw [heckeAct_coe, frobenius_apply, heckeDegree_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mul]
  refine Finsupp.sum_congr fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [cosetVector_mk, Representation.trivial_apply, smul_eq_mul]

/-- The degree is multiplicative for convolution. -/
theorem heckeDegree_heckeMul (K L M : Subgroup G) (a : HeckeSpace R K L) (b : HeckeSpace R L M) :
    heckeDegree R K M (heckeMul R K L M a b) = heckeDegree R K L a * heckeDegree R L M b := by
  let τ := Representation.trivial R G R
  have hone : ∀ H : Subgroup G, (1 : R) ∈ fixedVectors τ H := fun H h => rfl
  have h := congrArg Subtype.val (heckeAct_heckeAct τ K L M a b ⟨1, hone M⟩)
  have hb : heckeAct τ L M b ⟨1, hone M⟩ = heckeDegree R L M b • ⟨1, hone L⟩ := by
    apply Subtype.ext
    rw [heckeAct_trivial, Submodule.coe_smul, smul_eq_mul]
  rw [hb, map_smul, Submodule.coe_smul, heckeAct_trivial, heckeAct_trivial, smul_eq_mul] at h
  simp only [mul_one] at h
  rw [← h, mul_comm]

/-- The degree of `δ_L` is `1`. -/
theorem heckeDegree_unitElement (L : Subgroup G) : heckeDegree R L L (unitElement L) = 1 := by
  rw [heckeDegree, LinearMap.comp_apply, Submodule.subtype_apply, unitElement_coe,
    Finsupp.linearCombination_single, smul_eq_mul, mul_one]

section Levels

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The degree of `[K g L] δ_L` is the number of cosets `y L` in `K g L`, that is the number
of cosets of `K ∩ g L g⁻¹` in `K`. -/
theorem heckeDegree_heckeElement (K L : CompactOpenLevel G) (g : G) :
    heckeDegree R K.subgroup L.subgroup (heckeElement R K L g) =
      Fintype.card (HeckeCosets K L g) := by
  rw [heckeDegree, LinearMap.comp_apply, Submodule.subtype_apply, heckeElement_coe, map_sum]
  simp only [Finsupp.linearCombination_single, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

end Levels

namespace LevelHeckeAlgebra

variable (R) in
/-- The degree character `deg : H(G, K) → R` of the Hecke algebra,
`deg [K g K] = [K : K ∩ g K g⁻¹]`;
it is the action of the Hecke algebra on the `K`-fixed vectors of the trivial representation. -/
def degreeHom (K : Subgroup G) : LevelHeckeAlgebra R K →ₐ[R] R :=
  AlgHom.ofLinearMap ((heckeDegree R K K).comp (ofHeckeSpace K).symm.toLinearMap)
    (heckeDegree_unitElement K) (fun a b => heckeDegree_heckeMul K K K a b)

theorem degreeHom_apply (K : Subgroup G) (a : LevelHeckeAlgebra R K) :
    degreeHom R K a = heckeDegree R K K a := rfl

/-- The Hecke algebra of `K` acts on the `K`-fixed vectors of the trivial representation through
the degree character. -/
theorem smul_trivial (K : Subgroup G) (a : LevelHeckeAlgebra R K)
    (r : fixedVectors (Representation.trivial R G R) K) :
    ((a • r : fixedVectors (Representation.trivial R G R) K) : R) = degreeHom R K a * r :=
  heckeAct_trivial K K a r

theorem degreeHom_doubleCoset [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompactOpenLevel G) (g : G) :
    degreeHom R K.subgroup (doubleCoset K g) = Fintype.card (HeckeCosets K K g) :=
  heckeDegree_heckeElement K K g

end LevelHeckeAlgebra

end Degree

end Langlands.Shimura.LevelHecke
