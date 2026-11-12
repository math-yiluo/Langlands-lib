import Langlands.Cohomology.DivisibleSystem.ProPInvariants
import Langlands.Shimura.Levels
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Pro-`p` levels

Harris 1999, §4, p.310, chooses "an open normal pro-`p` subgroup `H_p` of `C_p` contained in
`K_p`". This module supplies such subgroups.

* A subgroup is topologically `p`-torsion if `h ^ (p ^ k) → 1` for each of its elements. A
  compact, totally disconnected, topologically `p`-torsion subgroup is pro-`p` in the sense of
  the published `Cohomology.IsProPSubgroup`.
* In a topological group with an open topologically `p`-torsion subgroup `P`, every compact open
  level `C` and every open subgroup `K` admit an open subgroup `H ≤ K`, normal in `C` and pro-`p`:
  the normal core in `C` of `K ⊓ P ⊓ C` (`NormalProPLevel`).
* In an ultrametric normed ring with `‖1‖ ≤ 1` and `‖p‖ < 1`, the principal units
  `{u | ‖u - 1‖ ≤ r}` (`0 < r < 1`) form an open topologically `p`-torsion subgroup, by the
  estimate `‖x ^ p - 1‖ ≤ max ‖p‖ ‖x - 1‖ * ‖x - 1‖`.
* A finite-dimensional algebra with its module topology over a complete ultrametric field embeds,
  through its left regular representation, into the continuous endomorphisms of a coordinate
  space with the operator norm; so its unit group is totally disconnected and has open
  topologically `p`-torsion subgroups when `‖p‖ < 1`.
-/

noncomputable section

open Filter Topology

set_option autoImplicit false

namespace Langlands.Shimura

section TopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A subgroup `H` is topologically `p`-torsion if `h ^ (p ^ k) → 1` as `k → ∞` for every
`h ∈ H`. -/
def IsTopologicallyPTorsion (p : ℕ) (H : Subgroup G) : Prop :=
  ∀ h ∈ H, Tendsto (fun k : ℕ => h ^ p ^ k) atTop (𝓝 1)

namespace IsTopologicallyPTorsion

variable {p : ℕ} {H : Subgroup G}

theorem mono (hH : IsTopologicallyPTorsion p H) {H' : Subgroup G} (h : H' ≤ H) :
    IsTopologicallyPTorsion p H' :=
  fun x hx => hH x (h hx)

/-- Topological `p`-torsion pulls back along inducing homomorphisms. -/
theorem comap {G' : Type*} [Group G'] [TopologicalSpace G'] {H' : Subgroup G'}
    (hH' : IsTopologicallyPTorsion p H') (f : G →* G') (hf : IsInducing f) :
    IsTopologicallyPTorsion p (H'.comap f) := by
  intro h hh
  rw [hf.tendsto_nhds_iff, map_one]
  simpa only [Function.comp_def, map_pow] using hH' (f h) hh

/-- A product of topologically `p`-torsion subgroups is topologically `p`-torsion. -/
theorem prod {G' : Type*} [Group G'] [TopologicalSpace G'] {H' : Subgroup G'}
    (hH : IsTopologicallyPTorsion p H) (hH' : IsTopologicallyPTorsion p H') :
    IsTopologicallyPTorsion p (H.prod H') := by
  intro h hh
  rw [Subgroup.mem_prod] at hh
  rw [Prod.one_eq_mk, nhds_prod_eq, tendsto_prod_iff']
  simpa only [Prod.pow_fst, Prod.pow_snd] using And.intro (hH h.1 hh.1) (hH' h.2 hh.2)

/-- The quotient of a topologically `p`-torsion subgroup by an open normal subgroup is a
`p`-group. -/
theorem isPGroup_quotient (hH : IsTopologicallyPTorsion p H) (N : OpenNormalSubgroup H) :
    IsPGroup p (H ⧸ N.toSubgroup) := by
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  have ht : Tendsto (fun k : ℕ => h ^ p ^ k) atTop (𝓝 (1 : H)) := by
    rw [tendsto_subtype_rng]
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using hH h h.2
  obtain ⟨k, hk⟩ := (ht.eventually (N.toOpenSubgroup.isOpen.mem_nhds N.one_mem)).exists
  exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

/-- A compact, totally disconnected, topologically `p`-torsion subgroup is pro-`p`. -/
theorem isProPSubgroup (hH : IsTopologicallyPTorsion p H) (hp : p.Prime) [CompactSpace H]
    [TotallyDisconnectedSpace H] : Cohomology.IsProPSubgroup p H :=
  ⟨hp, inferInstance, inferInstance, hH.isPGroup_quotient⟩

end IsTopologicallyPTorsion

variable [IsTopologicalGroup G]

namespace CompactOpenLevel

theorem isClosed_normalCore_subgroupOf (C : CompactOpenLevel G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) :
    IsClosed (((U.subgroupOf C.subgroup).normalCore : Subgroup C.subgroup) : Set C.subgroup) :=
  Subgroup.normalCore_isClosed _
    ((U.subgroupOf C.subgroup).isClosed_of_isOpen (hU.preimage continuous_subtype_val))

theorem isOpen_normalCore_subgroupOf (C : CompactOpenLevel G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) :
    IsOpen (((U.subgroupOf C.subgroup).normalCore : Subgroup C.subgroup) : Set C.subgroup) := by
  have : CompactSpace C.subgroup := isCompact_iff_compactSpace.mp C.isCompact
  have : Finite (C.subgroup ⧸ U.subgroupOf C.subgroup) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have : (U.subgroupOf C.subgroup).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (C.isClosed_normalCore_subgroupOf hU)

/-- The normal core in `C` of `U ⊓ C`, for an open subgroup `U`: the intersection of the
`C`-conjugates of `U ⊓ C`, a compact open level normal in `C`. -/
def normalCoreIn (C : CompactOpenLevel G) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    CompactOpenLevel G where
  openSubgroup :=
    { toSubgroup := (U.subgroupOf C.subgroup).normalCore.map C.subgroup.subtype
      isOpen' := by
        change IsOpen ((Subgroup.map C.subgroup.subtype _ : Subgroup G) : Set G)
        rw [Subgroup.coe_map]
        exact C.openSubgroup.isOpen.isOpenMap_subtype_val _
          (C.isOpen_normalCore_subgroupOf hU) }
  isCompact := by
    have : CompactSpace C.subgroup := isCompact_iff_compactSpace.mp C.isCompact
    change IsCompact ((U.subgroupOf C.subgroup).normalCore.map C.subgroup.subtype : Set G)
    rw [Subgroup.coe_map]
    exact (C.isClosed_normalCore_subgroupOf hU).isCompact.image continuous_subtype_val

theorem mem_normalCoreIn (C : CompactOpenLevel G) {U : Subgroup G} (hU : IsOpen (U : Set G))
    (g : G) :
    g ∈ (C.normalCoreIn U hU).subgroup ↔
      ∃ h : C.subgroup, h ∈ (U.subgroupOf C.subgroup).normalCore ∧ (h : G) = g :=
  Subgroup.mem_map

theorem normalCoreIn_le (C : CompactOpenLevel G) {U : Subgroup G} (hU : IsOpen (U : Set G)) :
    (C.normalCoreIn U hU).subgroup ≤ U := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := (C.mem_normalCoreIn hU g).mp hg
  exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hh)

theorem normalCoreIn_le_self (C : CompactOpenLevel G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) : (C.normalCoreIn U hU).subgroup ≤ C.subgroup := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := (C.mem_normalCoreIn hU g).mp hg
  exact h.2

theorem normalCoreIn_subgroupOf (C : CompactOpenLevel G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) :
    (C.normalCoreIn U hU).subgroup.subgroupOf C.subgroup =
      (U.subgroupOf C.subgroup).normalCore :=
  Subgroup.comap_map_eq_self_of_injective C.subgroup.subtype_injective _

instance normalCoreIn_normal (C : CompactOpenLevel G) {U : Subgroup G}
    (hU : IsOpen (U : Set G)) : ((C.normalCoreIn U hU).subgroup.subgroupOf C.subgroup).Normal := by
  rw [C.normalCoreIn_subgroupOf hU]
  infer_instance

end CompactOpenLevel

/-- Harris's `H_p` (1999, p.310): a compact open subgroup contained in `K`, normal in the compact
open level `C` and pro-`p`. -/
structure NormalProPLevel (p : ℕ) (C : CompactOpenLevel G) (K : Subgroup G) where
  /-- The subgroup `H_p`. -/
  level : CompactOpenLevel G
  le : level.subgroup ≤ K
  le_level : level.subgroup ≤ C.subgroup
  normal : (level.subgroup.subgroupOf C.subgroup).Normal
  isProP : Cohomology.IsProPSubgroup p level.subgroup

namespace NormalProPLevel

variable [TotallyDisconnectedSpace G] {p : ℕ}

/-- The normal core in `C` of `K ⊓ P`, for an open topologically `p`-torsion subgroup `P`, is an
open normal pro-`p` subgroup of `C` contained in `K`. -/
def ofNormalCore (hp : p.Prime) (C : CompactOpenLevel G) {K P : Subgroup G}
    (hK : IsOpen (K : Set G)) (hP : IsOpen (P : Set G)) (hPp : IsTopologicallyPTorsion p P) :
    NormalProPLevel p C K where
  level := C.normalCoreIn (K ⊓ P) (hK.inter hP)
  le := (C.normalCoreIn_le _).trans inf_le_left
  le_level := C.normalCoreIn_le_self _
  normal := CompactOpenLevel.normalCoreIn_normal C _
  isProP :=
    haveI : CompactSpace (C.normalCoreIn (K ⊓ P) (hK.inter hP)).subgroup :=
      isCompact_iff_compactSpace.mp (C.normalCoreIn (K ⊓ P) (hK.inter hP)).isCompact
    (hPp.mono ((C.normalCoreIn_le _).trans inf_le_right)).isProPSubgroup hp

theorem nonempty (hp : p.Prime) (C : CompactOpenLevel G) {K P : Subgroup G}
    (hK : IsOpen (K : Set G)) (hP : IsOpen (P : Set G)) (hPp : IsTopologicallyPTorsion p P) :
    Nonempty (NormalProPLevel p C K) :=
  ⟨ofNormalCore hp C hK hP hPp⟩

end NormalProPLevel

end TopologicalGroup

/-- A space with a continuous injection into a totally disconnected space is totally
disconnected. -/
theorem totallyDisconnectedSpace_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X :=
  (totallyDisconnectedSpace_iff X).mpr
    (isTotallyDisconnected_of_image hf.continuousOn hinj
      (isTotallyDisconnected_of_totallyDisconnectedSpace _))

/-- `Units.map` of an inducing monoid homomorphism is inducing for the units topologies. -/
theorem isInducing_units_map {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
    [TopologicalSpace N] (f : M →* N) (hf : IsInducing f) : IsInducing (Units.map f) := by
  refine (Units.isInducing_embedProduct (M := N)).of_comp_iff.mp ?_
  have hop : IsInducing (MulOpposite.op ∘ f ∘ MulOpposite.unop : Mᵐᵒᵖ → Nᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isInducing.comp (hf.comp MulOpposite.opHomeomorph.symm.isInducing)
  have : Units.embedProduct N ∘ Units.map f =
      Prod.map f (MulOpposite.op ∘ f ∘ MulOpposite.unop) ∘ Units.embedProduct M := by
    ext u <;> simp
  rw [this]
  exact (hf.prodMap hop).comp Units.isInducing_embedProduct

section NormedRing

variable {S : Type*} [NormedRing S] [IsUltrametricDist S]

namespace PrincipalUnits

variable (h1 : ‖(1 : S)‖ ≤ 1) {x : S}
include h1

theorem norm_le_one (hx : ‖x - 1‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - 1) 1
  rw [sub_add_cancel] at this
  exact this.trans (max_le hx h1)

theorem norm_pow_le_one (hx : ‖x - 1‖ ≤ 1) (n : ℕ) : ‖x ^ n‖ ≤ 1 := by
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul ih (norm_le_one h1 hx) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem norm_geom_sum_le_one (hx : ‖x - 1‖ ≤ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, x ^ i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    fun i _ => norm_pow_le_one h1 hx i

theorem norm_pow_sub_one_le (hx : ‖x - 1‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_geom_sum_le_one h1 hx n))

/-- The basic estimate `‖x ^ p - 1‖ ≤ max ‖p‖ ‖x - 1‖ * ‖x - 1‖`, from
`x ^ p - 1 = (p + ∑_{i < p} (x ^ i - 1)) * (x - 1)`. -/
theorem norm_pow_sub_one_le_max_mul (hx : ‖x - 1‖ ≤ 1) (p : ℕ) :
    ‖x ^ p - 1‖ ≤ max ‖(p : S)‖ ‖x - 1‖ * ‖x - 1‖ := by
  have hsum : ∑ i ∈ Finset.range p, x ^ i = (p : S) + ∑ i ∈ Finset.range p, (x ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_one]
    abel
  rw [← geom_sum_mul, hsum]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    fun i _ => norm_pow_sub_one_le h1 hx i

theorem norm_pow_pow_sub_one_le {r : ℝ} (hr : r ≤ 1) (hx : ‖x - 1‖ ≤ r) (p k : ℕ) :
    ‖x ^ p ^ k - 1‖ ≤ max ‖(p : S)‖ r ^ k * ‖x - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ‖x ^ p ^ k - 1‖ ≤ r := (norm_pow_sub_one_le h1 (hx.trans hr) _).trans hx
    rw [pow_succ, pow_mul, pow_succ', mul_assoc]
    calc ‖(x ^ p ^ k) ^ p - 1‖ ≤ max ‖(p : S)‖ ‖x ^ p ^ k - 1‖ * ‖x ^ p ^ k - 1‖ :=
          norm_pow_sub_one_le_max_mul h1 (hk.trans hr) p
      _ ≤ max ‖(p : S)‖ r * (max ‖(p : S)‖ r ^ k * ‖x - 1‖) :=
          mul_le_mul (max_le_max le_rfl hk) ih (norm_nonneg _)
            (le_max_of_le_left (norm_nonneg _))

/-- If `‖p‖ < 1` and `‖x - 1‖ < 1` then `x ^ (p ^ k) → 1`. -/
theorem tendsto_pow_pow {p : ℕ} (hp : ‖(p : S)‖ < 1) (hx : ‖x - 1‖ < 1) :
    Tendsto (fun k : ℕ => x ^ p ^ k) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k : ℕ => max ‖(p : S)‖ ‖x - 1‖ ^ k * ‖x - 1‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_of_le_left (norm_nonneg _))
      (max_lt hp hx)).mul_const ‖x - 1‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => norm_pow_pow_sub_one_le h1 hx.le le_rfl p k) h0

end PrincipalUnits

/-- The principal units `{u ∈ Sˣ | ‖u - 1‖ ≤ r}` of an ultrametric normed ring with `‖1‖ ≤ 1`,
for `0 ≤ r < 1`. -/
def principalUnits (h1 : ‖(1 : S)‖ ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) : Subgroup Sˣ where
  carrier := {u | ‖(u : S) - 1‖ ≤ r}
  one_mem' := by simp [hr0]
  mul_mem' {a b} ha hb := by
    replace ha : ‖(a : S) - 1‖ ≤ r := ha
    replace hb : ‖(b : S) - 1‖ ≤ r := hb
    change ‖(a : S) * b - 1‖ ≤ r
    have e : (a : S) * b - 1 = ((a : S) - 1) * ((b : S) - 1) + (((a : S) - 1) + ((b : S) - 1)) := by
      noncomm_ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)))
    refine (norm_mul_le _ _).trans ((mul_le_mul ha hb (norm_nonneg _) hr0).trans ?_)
    nlinarith
  inv_mem' {a} ha := by
    replace ha : ‖(a : S) - 1‖ ≤ r := ha
    change ‖((a⁻¹ : Sˣ) : S) - 1‖ ≤ r
    have e : ((a⁻¹ : Sˣ) : S) = 1 - ((a⁻¹ : Sˣ) : S) * ((a : S) - 1) := by
      rw [mul_sub, Units.inv_mul, mul_one]
      abel
    have hinv : ‖((a⁻¹ : Sˣ) : S)‖ ≤ 1 := by
      by_contra hcon
      replace hcon := not_le.mp hcon
      have h2 : ‖((a⁻¹ : Sˣ) : S) * ((a : S) - 1)‖ < ‖((a⁻¹ : Sˣ) : S)‖ :=
        (norm_mul_le _ _).trans_lt (by nlinarith [norm_nonneg ((a : S) - 1)])
      have h3 := IsUltrametricDist.norm_add_le_max (1 : S) (-(((a⁻¹ : Sˣ) : S) * ((a : S) - 1)))
      rw [← sub_eq_add_neg, ← e, norm_neg] at h3
      rcases le_max_iff.mp h3 with h | h <;> linarith
    have e' : ((a⁻¹ : Sˣ) : S) - 1 = -(((a⁻¹ : Sˣ) : S) * ((a : S) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]
      abel
    rw [e', norm_neg]
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hinv).trans ha)

theorem mem_principalUnits (h1 : ‖(1 : S)‖ ≤ 1) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (u : Sˣ) :
    u ∈ principalUnits h1 r hr0 hr ↔ ‖(u : S) - 1‖ ≤ r :=
  Iff.rfl

theorem isOpen_principalUnits (h1 : ‖(1 : S)‖ ≤ 1) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    IsOpen ((principalUnits h1 r hr0.le hr : Subgroup Sˣ) : Set Sˣ) := by
  have e : ((principalUnits h1 r hr0.le hr : Subgroup Sˣ) : Set Sˣ) =
      Units.val ⁻¹' Metric.closedBall 1 r := by
    ext u
    simp [principalUnits, dist_eq_norm]
  rw [e]
  exact (IsUltrametricDist.isOpen_closedBall _ hr0.ne').preimage Units.continuous_val

theorem isTopologicallyPTorsion_principalUnits (h1 : ‖(1 : S)‖ ≤ 1) {p : ℕ}
    (hp : ‖(p : S)‖ < 1) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    IsTopologicallyPTorsion p (principalUnits h1 r hr0 hr) := by
  intro u hu
  have hu' := (principalUnits h1 r hr0 hr).inv_mem hu
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff, map_one, Prod.one_eq_mk, nhds_prod_eq,
    tendsto_prod_iff']
  constructor
  · simpa [Function.comp_def] using PrincipalUnits.tendsto_pow_pow h1 hp (hu.trans_lt hr)
  · have := PrincipalUnits.tendsto_pow_pow h1 hp (hu'.trans_lt hr)
    simpa [Function.comp_def, ← inv_pow] using (MulOpposite.continuous_op.tendsto 1).comp this

end NormedRing

section ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

theorem norm_one_continuousLinearMap_le : ‖(1 : E →L[𝕜] E)‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

theorem norm_natCast_continuousLinearMap_le (n : ℕ) :
    ‖(n : E →L[𝕜] E)‖ ≤ ‖(n : 𝕜)‖ := by
  rw [← nsmul_one, ← Nat.cast_smul_eq_nsmul 𝕜]
  exact (norm_smul_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) norm_one_continuousLinearMap_le)

/-- The operator norm on continuous endomorphisms of an ultrametric normed space is
ultrametric. -/
theorem isUltrametricDist_continuousLinearMap [IsUltrametricDist E] :
    IsUltrametricDist (E →L[𝕜] E) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g =>
    ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => by
      change ‖f x + g x‖ ≤ max ‖f‖ ‖g‖ * ‖x‖
      rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (f.le_opNorm x) (g.le_opNorm x))

end ContinuousLinearMap

section FiniteDimensional

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (R : Type*) [Ring R] [Algebra 𝕜 R] [FiniteDimensional 𝕜 R]

/-- The coordinate space `𝕜ⁿ`, `n = dim_𝕜 R`, with the sup norm. -/
abbrev RegularCoordinates : Type _ := Fin (Module.finrank 𝕜 R) → 𝕜

/-- The continuous endomorphisms of `RegularCoordinates 𝕜 R`, with the operator norm. -/
abbrev RegularEndomorphisms : Type _ := RegularCoordinates 𝕜 R →L[𝕜] RegularCoordinates 𝕜 R

/-- The left regular representation of `R` on `𝕜ⁿ` through the coordinates of
`Module.finBasis`, with values in continuous endomorphisms. -/
def regularRepresentation : R →ₐ[𝕜] RegularEndomorphisms 𝕜 R :=
  (Module.End.toContinuousLinearMap (RegularCoordinates 𝕜 R)).toAlgHom.comp
    (((Module.finBasis 𝕜 R).equivFun.conjAlgEquiv 𝕜).toAlgHom.comp (Algebra.lmul 𝕜 R))

theorem regularRepresentation_apply (x : R) (c : RegularCoordinates 𝕜 R) :
    regularRepresentation 𝕜 R x c =
      (Module.finBasis 𝕜 R).equivFun (x * (Module.finBasis 𝕜 R).equivFun.symm c) :=
  rfl

theorem regularRepresentation_injective : Function.Injective (regularRepresentation 𝕜 R) := by
  intro x y h
  have := congrArg (fun f : RegularEndomorphisms 𝕜 R =>
    (Module.finBasis 𝕜 R).equivFun.symm (f ((Module.finBasis 𝕜 R).equivFun 1))) h
  simpa only [regularRepresentation_apply, LinearEquiv.symm_apply_apply, mul_one] using this

section Ultrametric

variable [IsUltrametricDist 𝕜]

instance : IsUltrametricDist (RegularEndomorphisms 𝕜 R) :=
  isUltrametricDist_continuousLinearMap

/-- The principal units of `R` of radius `r` with respect to the operator norm of the left regular
representation: the units `u` with `‖ρ(u) - 1‖ ≤ r`. -/
def regularPrincipalUnits (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) : Subgroup Rˣ :=
  (principalUnits (S := RegularEndomorphisms 𝕜 R) norm_one_continuousLinearMap_le r hr0 hr).comap
    (Units.map (regularRepresentation 𝕜 R).toMonoidHom)

theorem mem_regularPrincipalUnits (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (u : Rˣ) :
    u ∈ regularPrincipalUnits 𝕜 R r hr0 hr ↔
      ‖regularRepresentation 𝕜 R (u : R) - 1‖ ≤ r :=
  Iff.rfl

end Ultrametric

variable [TopologicalSpace R] [IsModuleTopology 𝕜 R]

theorem continuous_regularRepresentation : Continuous (regularRepresentation 𝕜 R) :=
  haveI := IsModuleTopology.toContinuousAdd 𝕜 R
  IsModuleTopology.continuous_of_linearMap (regularRepresentation 𝕜 R).toLinearMap

include 𝕜 in
/-- `R` with its module topology is Hausdorff. -/
theorem t2Space_of_isModuleTopology : T2Space R :=
  .of_injective_continuous (regularRepresentation_injective 𝕜 R)
    (continuous_regularRepresentation 𝕜 R)

/-- The left regular representation is a topological embedding. -/
theorem isInducing_regularRepresentation :
    IsInducing (regularRepresentation 𝕜 R) := by
  have := t2Space_of_isModuleTopology 𝕜 R
  have := IsModuleTopology.isTopologicalAddGroup 𝕜 R
  exact (LinearMap.isClosedEmbedding_of_injective (f := (regularRepresentation 𝕜 R).toLinearMap)
    (LinearMap.ker_eq_bot.mpr (regularRepresentation_injective 𝕜 R))).isInducing

variable [IsUltrametricDist 𝕜]

include 𝕜 in
/-- The units of `R` are totally disconnected. -/
theorem totallyDisconnectedSpace_units : TotallyDisconnectedSpace Rˣ :=
  totallyDisconnectedSpace_of_continuous_injective
    ((continuous_regularRepresentation 𝕜 R).comp Units.continuous_val)
    ((regularRepresentation_injective 𝕜 R).comp Units.val_injective)

theorem isOpen_regularPrincipalUnits {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    IsOpen ((regularPrincipalUnits 𝕜 R r hr0.le hr : Subgroup Rˣ) : Set Rˣ) :=
  (isOpen_principalUnits (S := RegularEndomorphisms 𝕜 R) norm_one_continuousLinearMap_le
    hr0 hr).preimage (Continuous.units_map _ (continuous_regularRepresentation 𝕜 R))

theorem isTopologicallyPTorsion_regularPrincipalUnits {p : ℕ}
    (hp : ‖(p : 𝕜)‖ < 1) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    IsTopologicallyPTorsion p (regularPrincipalUnits 𝕜 R r hr0 hr) :=
  (isTopologicallyPTorsion_principalUnits (S := RegularEndomorphisms 𝕜 R)
      norm_one_continuousLinearMap_le ((norm_natCast_continuousLinearMap_le p).trans_lt hp)
      r hr0 hr).comap _
    (isInducing_units_map _ (isInducing_regularRepresentation 𝕜 R))

end FiniteDimensional

end Langlands.Shimura
