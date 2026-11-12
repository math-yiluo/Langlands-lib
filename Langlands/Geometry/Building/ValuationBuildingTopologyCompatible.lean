import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.QuasiSplitApartmentOpposite
import Langlands.Geometry.Building.KPFiltrationTopology
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.BruhatTits.SpecialCompact.RootDepthWeakContraction
import Langlands.BruhatTits.Unipotent.CocharacterEscape

/-! # Axiom V 7 for building data

For every `B : ValuationBuildingData G` over a nonarchimedean local field `F`, this module proves
KP axiom V 7 (Definition 6.1.2): for every valuation `x` of the class `A(S)` and every root `a`,
the sets `U_{a,x,r}` are open in `U_a(F)`, algebraically bounded in `G(F)`, and form a
neighbourhood base of `1` in `U_a(F)`. It states this as
`ValuationBuildingTopologyCompatibleStatement` and proves it as
`valuationBuildingTopologyCompatible`.

The proof uses V 0, V 1, V 6 and the group structure, not descent:

* `eventually_val_eq`: `x_a` is locally constant on `U_a(F) ∖ {1}`, by the opposite open cell
  and the open norm kernel `Z(F)^1`;
* `exists_contracting_element`: a point `b` of `S(F)` shifts `x_a` by a positive constant and
  contracts `U_a(F)` to `1`;
* `contracting_isOpen`, `contracting_isCompact`, `contracting_hasBasis`: a general criterion
  for such filtrations of a topological group with a compact open identity neighbourhood.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

/-! ### Filtrations of a topological group contracted by an automorphism

Let `f : U → ℝ ∪ {∞}` on a topological group `U` with `f⁻¹(∞) = {1}`, whose superlevel sets
`filt r = {f ≥ r}` are subgroups, which is locally constant on `U ∖ {1}`, and which an
automorphism `σ` of `U` shifts by a constant `c > 0`, with `σⁿ(g) → 1` for every `g`. If `U`
has a compact open identity neighbourhood and a point `≠ 1`, then every `filt r` is a compact
open subgroup and they form a neighbourhood base of `1`. -/

section ContractingFiltration

variable {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
  {f : U → WithTop ℝ} {filt : ℝ → Subgroup U} {σ : U ≃ₜ* U} {c : ℝ}

omit [IsTopologicalGroup U] in
/-- `f(σⁿ g) = f(g) + n c`. -/
theorem contracting_iterate_shift (hshift : ∀ g, f (σ g) = f g + (c : WithTop ℝ))
    (n : ℕ) (g : U) : f (σ^[n] g) = f g + ((n * c : ℝ) : WithTop ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', hshift, ih, add_assoc, ← WithTop.coe_add]
    congr 2
    push_cast
    ring

variable (hfilt : ∀ r g, g ∈ filt r ↔ (r : WithTop ℝ) ≤ f g)
  (htop : ∀ g, f g = ⊤ ↔ g = 1)
  (hlc : ∀ g, g ≠ 1 → ∀ᶠ v in 𝓝 g, f v = f g)
  (hshift : ∀ g, f (σ g) = f g + (c : WithTop ℝ)) (hc : 0 < c)
  (htend : ∀ g, Tendsto (fun n : ℕ => σ^[n] g) atTop (𝓝 1))
  (hne : ∃ g : U, g ≠ 1)

omit [IsTopologicalGroup U] in
include hfilt htop hshift hc hne in
/-- Every `filt r` contains a point `≠ 1`. -/
theorem contracting_exists_mem_ne_one (r : ℝ) : ∃ g ∈ filt r, g ≠ 1 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hg₀ ((htop g₀).mp h))
  obtain ⟨n, hn⟩ := exists_nat_gt ((r - s) / c)
  have hn' : r ≤ s + n * c := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have hval : f (σ^[n] g₀) = ((s + n * c : ℝ) : WithTop ℝ) := by
    rw [contracting_iterate_shift hshift, ← hs, WithTop.coe_add]
  refine ⟨σ^[n] g₀, (hfilt r _).mpr ?_, fun h => ?_⟩
  · rw [hval]
    exact WithTop.coe_le_coe.mpr hn'
  · rw [(htop _).mpr h] at hval
    exact WithTop.top_ne_coe hval

include hfilt htop hlc hshift hc hne in
/-- Every `filt r` is open. -/
theorem contracting_isOpen (r : ℝ) : IsOpen (filt r : Set U) := by
  obtain ⟨g, hg, hg1⟩ := contracting_exists_mem_ne_one hfilt htop hshift hc hne r
  apply Subgroup.isOpen_of_mem_nhds (filt r) (g := g)
  filter_upwards [hlc g hg1] with v hv
  rw [SetLike.mem_coe, hfilt, hv]
  exact (hfilt r g).mp hg

omit [IsTopologicalGroup U] in
include htop hlc hshift hc htend in
/-- Outside a compact open identity neighbourhood `K`, `f` is bounded above. -/
theorem contracting_exists_bound {K : Set U} (hKo : IsOpen K) (hKc : IsCompact K)
    (hK1 : (1 : U) ∈ K) : ∃ M : ℝ, ∀ u, (M : WithTop ℝ) < f u → u ∈ K := by
  classical
  set A : Set U := K \ (σ.symm ⁻¹' K) with hA_def
  have hA : IsCompact A := hKc.diff (hKo.preimage σ.symm.continuous)
  have hA1 : ∀ y ∈ A, y ≠ 1 := by
    rintro y ⟨-, hy⟩ rfl
    exact hy (by simpa only [Set.mem_preimage, map_one] using hK1)
  obtain ⟨t, htA, hcover⟩ := hA.elim_nhds_subcover (fun a => {v | f v = f a})
    (fun a ha => hlc a (hA1 a ha))
  refine ⟨∑ a ∈ t, |(f a).untopD 0|, fun u hu => ?_⟩
  by_contra huK
  have hbound : ∀ y ∈ A, f y ≤ ((∑ a ∈ t, |(f a).untopD 0| : ℝ) : WithTop ℝ) := by
    intro y hy
    obtain ⟨a, hat, hya⟩ := Set.mem_iUnion₂.mp (hcover hy)
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
      (fun h => hA1 a (htA a hat) ((htop a).mp h))
    have hya' : f y = f a := hya
    rw [hya', ← hs, WithTop.coe_le_coe]
    have h1 : (f a).untopD 0 = s := by rw [← hs, WithTop.untopD_coe]
    calc s ≤ |s| := le_abs_self s
      _ = |(f a).untopD 0| := by rw [h1]
      _ ≤ ∑ a ∈ t, |(f a).untopD 0| :=
        Finset.single_le_sum (f := fun a => |(f a).untopD 0|) (fun _ _ => abs_nonneg _) hat
  have hex : ∃ n : ℕ, σ^[n] u ∈ K := ((htend u).eventually (hKo.mem_nhds hK1)).exists
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, Function.iterate_zero, id] at this
    exact huK this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hmK : σ^[m] u ∉ K := Nat.find_min hex (by omega)
  have hyK : σ^[m + 1] u ∈ K := by
    have h := Nat.find_spec hex
    rwa [hm] at h
  have hyA : σ^[m + 1] u ∈ A := by
    refine ⟨hyK, ?_⟩
    rw [Set.mem_preimage, Function.iterate_succ_apply', ContinuousMulEquiv.symm_apply_apply]
    exact hmK
  have hle := hbound _ hyA
  rw [contracting_iterate_shift hshift] at hle
  have hfu : f u ≠ ⊤ := by
    intro h
    rw [h, WithTop.top_add] at hle
    exact WithTop.not_top_le_coe _ hle
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hfu
  rw [← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
  rw [← hs, WithTop.coe_lt_coe] at hu
  have : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * c := by positivity
  linarith

include hfilt htop hlc hshift hc htend hne in
/-- Every `filt r` is compact, given a compact open identity neighbourhood. -/
theorem contracting_isCompact {K : Set U} (hKo : IsOpen K) (hKc : IsCompact K)
    (hK1 : (1 : U) ∈ K) (r : ℝ) : IsCompact (filt r : Set U) := by
  obtain ⟨M, hM⟩ := contracting_exists_bound htop hlc hshift hc htend hKo hKc hK1
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - r) / c)
  have hn' : M < r + n * c := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have hsub : (filt r : Set U) ⊆ σ.symm^[n] '' K := by
    intro u hu
    refine ⟨σ^[n] u, hM _ ?_, ?_⟩
    · rw [contracting_iterate_shift hshift]
      have hu' := (hfilt r u).mp hu
      by_cases hfu : f u = ⊤
      · rw [hfu, WithTop.top_add]
        exact WithTop.coe_lt_top M
      · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hfu
        rw [← hs, ← WithTop.coe_add, WithTop.coe_lt_coe]
        rw [← hs, WithTop.coe_le_coe] at hu'
        linarith
    · exact (Function.LeftInverse.iterate (fun g => σ.symm_apply_apply g) n) u
  exact (hKc.image (σ.symm.continuous.iterate n)).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (contracting_isOpen hfilt htop hlc hshift hc hne r)) hsub

include hfilt htop hlc hshift hc htend hne in
/-- The `filt r` form a neighbourhood base of `1`. -/
theorem contracting_hasBasis [T2Space U] {K : Set U} (hKo : IsOpen K) (hKc : IsCompact K)
    (hK1 : (1 : U) ∈ K) :
    (𝓝 (1 : U)).HasBasis (fun _ : ℝ => True) (fun r => (filt r : Set U)) := by
  refine ⟨fun W => ⟨fun hW => ?_, fun ⟨r, _, hr⟩ => Filter.mem_of_superset
    ((contracting_isOpen hfilt htop hlc hshift hc hne r).mem_nhds (one_mem _)) hr⟩⟩
  have hanti : Antitone (fun n : ℕ => (filt n : Set U)) := by
    intro m n hmn u hu
    rw [SetLike.mem_coe, hfilt] at hu ⊢
    exact (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr hmn)).trans hu
  have hinter : (⋂ n : ℕ, (filt n : Set U)) = {1} := by
    ext u
    simp only [Set.mem_iInter, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · intro hu
      apply (htop u).mp
      by_contra hne'
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hne'
      obtain ⟨n, hn⟩ := exists_nat_gt s
      have := (hfilt n u).mp (hu n)
      rw [← hs, WithTop.coe_le_coe] at this
      linarith
    · rintro rfl n
      exact one_mem _
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hanti.directed_ge
    (fun n => contracting_isCompact hfilt htop hlc hshift hc htend hne hKo hKc hK1 n)
    (by rw [hinter, nhdsSet_singleton]; exact hW)
  exact ⟨n, trivial, hn⟩

end ContractingFiltration

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

local instance v7AmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance v7AmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- An open identity neighbourhood of `G(F)` whose points in `Z(F)` lie in `Z(F)^1`. -/
theorem exists_isOpen_centralizer_normKernel :
    ∃ W : Set (rationalPoints G), IsOpen W ∧ (1 : rationalPoints G) ∈ W ∧
      ∀ z : rationalPoints B.centralizer.Z, rationalPoints.map B.centralizer.j z ∈ W →
        z ∈ rationalCommonNormKernel B.centralizer.Z := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : IsClosedImmersion B.centralizer.j.hom.hom.left := B.centralizer.isClosedSubgroup
  have : IsAffine B.centralizer.Z.X.left :=
    isAffine_of_isAffineHom B.centralizer.j.hom.hom.left
  have : LocallyOfFiniteType B.centralizer.Z.X.hom := by
    rw [← Over.w B.centralizer.j.hom.hom]
    infer_instance
  let : TopologicalSpace (rationalPoints B.centralizer.Z) :=
    rationalPointTopology F B.centralizer.Z.X
  obtain ⟨W, hW, heq⟩ :=
    (isEmbedding_rationalPointMap F B.centralizer.j.hom.hom).isInducing.isOpen_iff.mp
      (isOpen_rationalCommonNormKernel B.centralizer.Z)
  refine ⟨W, hW, ?_, fun z hz => ?_⟩
  · have h1 : (1 : rationalPoints B.centralizer.Z) ∈
        (fun p => p ≫ B.centralizer.j.hom.hom) ⁻¹' W := by
      rw [heq]
      exact one_mem _
    simpa only [Set.mem_preimage, MonObj.one_comp] using h1
  · have hz' : z ∈ (fun p => p ≫ B.centralizer.j.hom.hom) ⁻¹' W := hz
    rw [heq] at hz'
    exact hz'

/-- **Local constancy of root values.** For `u ∈ U_a(F) ∖ {1}`, every `v ∈ U_a(F) ∖ {1}` near
`u` satisfies `x_a(v) = x_a(u)` at every apartment point `x`. The element `m(u)⁻¹ m(v)` is the
`Z`-factor of a point of the opposite cell near `1`, so it lies in `Z(F)^1` and fixes the
apartment; then `m(u)` and `m(v)` act by the same reflection. -/
theorem eventually_val_eq {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) :
    ∀ᶠ v in 𝓝 u, v ∈ B.rootGroup α → v ≠ 1 →
      ∀ x : B.Apartment, x.val α v = x.val α u := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hα0 : (α : characterLattice B.S) ≠ 0 := α.property.1
  obtain ⟨p, hp⟩ := B.exists_isOppositeFactorPair rootRankOneFactorization hu h1
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα0
  have hpos : 0 < latticePairing B.S (α : characterLattice B.S) ν := by omega
  have hneg : 0 < latticePairing B.S (-(α : characterLattice B.S)) (-ν) := by simpa using hpos
  let χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G := CommGroupScheme.groupHom (-ν) ≫ B.i
  have hχinv : CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ =
      CommGroupScheme.groupHom ν ≫ B.i := by
    have h := groupHom_neg_comp_eq_oppositeCocharacter B.i (-ν)
    rw [neg_neg] at h
    exact h.symm
  have hO : ∀ g ∈ B.rootGroup α, g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).carrier
        (Over.mk (𝟙 _)) := by
    intro g hg
    rw [hχinv]
    exact RelativeRoot.subgroup_le_dynamicUnipotent B.i ν hpos _ hg
  have hN : ∀ g ∈ B.rootGroup (-(α : characterLattice B.S)),
      g ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :=
    fun g hg => RelativeRoot.subgroup_le_dynamicUnipotent B.i (-ν) hneg _ hg
  have hM : ∀ g ∈ centralizerPoints B.i,
      g ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    intro g hg
    rw [← torusCentralizer_carrier_base] at hg
    exact torusCentralizer_le_dynamicCentralizer B.i (CommGroupScheme.groupHom (-ν)) _ hg
  obtain ⟨W, hW, hW1, hWZ⟩ := B.exists_isOpen_centralizer_normKernel
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsOpenUnits F := inferInstance
  have hcell := Dynamic.opposite_cell_mem_nhds_one F G χ
  rw [← rationalPointTopology_eq_rationalSchemeTopology F G.X] at hcell
  have hC := hcell Set.univ Filter.univ_mem W (hW.mem_nhds hW1) Set.univ Filter.univ_mem
  have hcont : Continuous
      (fun v : rationalPoints G => (p.1 * u * p.2)⁻¹ * p.1 * v * p.2) := by
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hwu : (p.1 * u * p.2)⁻¹ * p.1 * u * p.2 = 1 := by group
  have hev := hcont.continuousAt.preimage_mem_nhds (x := u) (by rw [hwu]; exact hC)
  filter_upwards [hev] with v hv hvα hv1 x
  obtain ⟨a, ⟨-, ha⟩, b, ⟨hbW, hb⟩, c, ⟨-, hc⟩, habc⟩ := hv
  obtain ⟨q, hq⟩ := B.exists_isOppositeFactorPair rootRankOneFactorization hvα hv1
  have h1' : (p.1 * u * p.2)⁻¹ * (p.1 * q.1⁻¹) * (p.1 * u * p.2) ∈ B.rootGroup α :=
    Langlands.Geometry.Building.IsOppositeFactorPair.inv_conj_mem B.i hS hα0 hu h1 hp
      (mul_mem hp.1 (inv_mem hq.1))
  have h2' : (p.1 * u * p.2)⁻¹ * (q.1 * v * q.2) ∈ centralizerPoints B.i :=
    B.reflectionElement_inv_mul_mem_centralizer hu h1 hvα hv1 hp hq
  have h3' : q.2⁻¹ * p.2 ∈ B.rootGroup (-(α : characterLattice B.S)) :=
    mul_mem (inv_mem hq.2.1) hp.2.1
  have hdec : (p.1 * u * p.2)⁻¹ * p.1 * v * p.2 =
      ((p.1 * u * p.2)⁻¹ * (p.1 * q.1⁻¹) * (p.1 * u * p.2)) *
        ((p.1 * u * p.2)⁻¹ * (q.1 * v * q.2)) * (q.2⁻¹ * p.2) := by
    group
  obtain ⟨-, hbm, -⟩ :=
    Aubert.General.RationalPointFamily.dynamic_opposite_factorization_unique χ
      a ha b hb c hc _ (hO _ h1') _ (hM _ h2') _ (hN _ h3') (habc.symm.trans hdec)
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at h2'
  obtain ⟨z, hz⟩ := h2'
  change z ≫ B.centralizer.j.hom.hom = _ at hz
  have hzK : z ∈ rationalCommonNormKernel B.centralizer.Z := by
    apply hWZ z
    change z ≫ B.centralizer.j.hom.hom ∈ W
    rw [hz, ← hbm]
    exact hbW
  have hfix := B.isOmegaCompatible.smul_eq_self hzK x
  have hzeq : B.centralizer.toNormalizer z =
      (B.reflectionElement hp)⁻¹ * B.reflectionElement hq :=
    Subtype.ext hz
  rw [hzeq, mul_smul, inv_smul_eq_iff] at hfix
  have key : ∀ {g : rationalPoints G} {r : rationalPoints G × rationalPoints G}
      (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
      (hr : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g r),
      rootForm B.i α (B.reflectionElement hr • x -ᵥ x) =
        -2 * B.reflectionFunctional α g x := by
    intro g r hg hg1 hr
    have h := DFunLike.congr_fun (B.normalizerAffineEquiv_reflectionElement hg hg1 hr) x
    change B.reflectionElement hr • x = _ at h
    rw [h]
    change rootForm B.i α
      (((-B.reflectionFunctional α g x) • B.reflectionCoroot hg hg1 hr +ᵥ x) -ᵥ x) = _
    rw [vadd_vsub, map_smul, B.rootForm_reflectionCoroot hg hg1 hr, smul_eq_mul]
    ring
  have hval : B.reflectionFunctional α v x = B.reflectionFunctional α u x := by
    have h := key hvα hv1 hq
    rw [hfix, key hu h1 hp] at h
    linarith
  rw [← B.coe_reflectionFunctional_apply hvα hv1, ← B.coe_reflectionFunctional_apply hu h1, hval]

/-- **Contraction by a split-torus point.** For a root `a` there are `b = ν(π) ∈ S(F)` (with
`⟨a, ν⟩ > 0`) and `c = ⟨a, ν⟩ > 0` such that conjugation by `b` preserves `U_a(F)`, adds `c` to
every `x_a` (axiom V 6 on `S(F)`), and contracts every point of `U_a(F)` to `1`. -/
theorem exists_contracting_element (α : relativeRoots B.i) :
    ∃ (b : rationalPoints G) (c : ℝ), 0 < c ∧
      (∀ g ∈ B.rootGroup α, b * g * b⁻¹ ∈ B.rootGroup α) ∧
      (∀ g ∈ B.rootGroup α, b⁻¹ * g * b ∈ B.rootGroup α) ∧
      (∀ x : B.Apartment, ∀ g ∈ B.rootGroup α,
        x.val α (b * g * b⁻¹) = x.val α g + (c : WithTop ℝ)) ∧
      (∀ g ∈ B.rootGroup α,
        Tendsto (fun n : ℕ => b ^ n * g * (b ^ n)⁻¹) atTop (𝓝 1)) := by
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos α.property.1
  have hpos : 0 < latticePairing B.S (α : characterLattice B.S) ν := by omega
  let t : rationalPoints B.S.toGrp :=
    CocharacterUniformizer.latticeSection F B.S (Multiplicative.ofAdd ν)
  have hbcent : rationalPoints.map B.i t ∈ centralizerPoints B.i := by
    rw [← torusCentralizer_carrier_base]
    intro U b y
    change ((b ≫ t) ≫ B.i.hom.hom) * (y ≫ B.i.hom.hom) =
      (y ≫ B.i.hom.hom) * ((b ≫ t) ≫ B.i.hom.hom)
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  have hconj : ∀ n ∈ centralizerPoints B.i, ∀ g ∈ B.rootGroup α,
      n * g * n⁻¹ ∈ B.rootGroup α := by
    intro n hn g hg
    let m : normalizerPoints B.i := ⟨n, centralizerPoints_le_normalizerPoints B.i hn⟩
    have hm : weylAction B.i m = 1 := weylAction_eq_one_of_mem_centralizerPoints B.i (n := m) hn
    have h := conj_mem_rootGroupPoints m hg
    simpa only [hm, LinearEquiv.coe_one, id_eq] using h
  have hord : localFieldOrder F
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice B.S).symm α) t) =
        (D : ℝ) := by
    rw [BruhatTits.SpecialCompact.localFieldOrder_latticeSection, hν]
    norm_cast
  refine ⟨rationalPoints.map B.i t, D, by exact_mod_cast hD, hconj _ hbcent, ?_, ?_, ?_⟩
  · intro g hg
    simpa only [inv_inv] using hconj _ (inv_mem hbcent) g hg
  · intro x g hg
    have hval := x.isSplitTorusCompatible α α.2 t⁻¹ g hg
    simp only [map_inv, inv_inv] at hval
    have horder : -localFieldOrder F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice B.S).symm α) t)⁻¹ =
          (D : ℝ) := by
      rw [← hord]
      simp only [localFieldOrder, map_inv, toAdd_inv, Int.cast_neg, neg_neg]
    rw [horder] at hval
    exact hval
  · intro g hg
    have : T2Space F := Langlands.BruhatTits.localField_t2Space F
    have hU : g ∈ BruhatTits.DynamicUnipotentContainment.unipotentPoints
        (CommGroupScheme.groupHom ν ≫ B.i) :=
      RelativeRoot.subgroup_le_dynamicUnipotent B.i ν hpos _ hg
    have hb : BruhatTits.DynamicUnipotentContainment.cocharPoint (CommGroupScheme.groupHom ν ≫ B.i)
        (SplitTorusValuation.uniformizerUnit F) = rationalPoints.map B.i t :=
      BruhatTits.DynamicUnipotentContainment.cocharPoint_comp_eq_map_cocharacterPoints B.i ν _
    rw [Filter.tendsto_def]
    intro W hW
    have h := BruhatTits.DynamicUnipotentContainment.eventually_cocharPoint_pow_conj_mem_ambient
      (CommGroupScheme.groupHom ν ≫ B.i) (SplitTorusValuation.uniformizerUnit F)
      (SplitTorusValuation.tendsto_uniformizerUnit_pow_zero F) {g} isCompact_singleton
      (Set.singleton_subset_iff.mpr hU) W hW
    rw [hb] at h
    filter_upwards [h] with n hn using hn g rfl

/-- For an apartment point `x` and a root `a`, every `U_{a,x,r}` is open in `U_a(F)` and compact in
`G(F)`, and these sets form a neighbourhood base of `1` in `U_a(F)`. -/
theorem rootFiltration_topology (x : B.Apartment) (α : relativeRoots B.i) :
    (𝓝 (1 : B.rootGroup α)).HasBasis (fun _ : ℝ => True)
        (fun r => ((↑) : B.rootGroup α → rationalPoints G) ⁻¹' rootFiltration B.i x.val α r) ∧
      ∀ r : ℝ,
        IsOpen (((↑) : B.rootGroup α → rationalPoints G) ⁻¹' rootFiltration B.i x.val α r) ∧
          IsCompact (rootFiltration B.i x.val α r) := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  obtain ⟨b, c, hc, hb1, hb2, hshift, htend⟩ := B.exists_contracting_element α
  let filt : ℝ → Subgroup (B.rootGroup α) := fun r =>
    { carrier := {g | (r : WithTop ℝ) ≤ x.val α g}
      mul_mem' := fun {g h} hg hh =>
        (x.isValuation.mul_mem α α.2 r g h ⟨g.2, hg⟩ ⟨h.2, hh⟩).2
      one_mem' := (x.isValuation.one_mem α α.2 r).2
      inv_mem' := fun {g} hg => (x.isValuation.inv_mem α α.2 r g ⟨g.2, hg⟩).2 }
  have hfilt : ∀ r (g : B.rootGroup α), g ∈ filt r ↔ (r : WithTop ℝ) ≤ x.val α g :=
    fun _ _ => Iff.rfl
  have hpre : (fun r => ((↑) : B.rootGroup α → rationalPoints G) ⁻¹'
      rootFiltration B.i x.val α r) = fun r => (filt r : Set (B.rootGroup α)) :=
    funext fun r => Set.ext fun g => ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  have himage : ∀ r, rootFiltration B.i x.val α r =
      ((↑) : B.rootGroup α → rationalPoints G) '' (filt r : Set (B.rootGroup α)) := by
    intro r
    ext g
    exact ⟨fun h => ⟨⟨g, h.1⟩, h.2, rfl⟩, by rintro ⟨g, hg, rfl⟩; exact ⟨g.2, hg⟩⟩
  have htop : ∀ g : B.rootGroup α, x.val α g = ⊤ ↔ g = 1 := fun g =>
    (x.isValuation.eq_top_iff α α.2 g g.2).trans
      ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hlc : ∀ g : B.rootGroup α, g ≠ 1 →
      ∀ᶠ v : B.rootGroup α in 𝓝 g, x.val α v = x.val α g := by
    intro g hg1
    have hg1' : (g : rationalPoints G) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hA := (continuous_subtype_val.tendsto g).eventually (B.eventually_val_eq g.2 hg1')
    filter_upwards [hA, eventually_ne_nhds hg1] with v hv hv1
    exact hv v.2 (fun h => hv1 (Subtype.ext h)) x
  let σ : B.rootGroup α ≃ₜ* B.rootGroup α :=
    { toFun := fun g => ⟨b * g * b⁻¹, hb1 g g.2⟩
      invFun := fun g => ⟨b⁻¹ * g * b, hb2 g g.2⟩
      left_inv := fun g => Subtype.ext (show b⁻¹ * (b * g * b⁻¹) * b = g by group)
      right_inv := fun g => Subtype.ext (show b * (b⁻¹ * g * b) * b⁻¹ = g by group)
      map_mul' := fun g h => Subtype.ext
        (show b * (g * h) * b⁻¹ = (b * g * b⁻¹) * (b * h * b⁻¹) by group)
      continuous_toFun :=
        ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun :=
        ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hσ : ∀ g : B.rootGroup α, ((σ g : B.rootGroup α) : rationalPoints G) = b * g * b⁻¹ :=
    fun _ => rfl
  have hσshift : ∀ g : B.rootGroup α, x.val α (σ g) = x.val α g + (c : WithTop ℝ) :=
    fun g => hshift x g g.2
  have hiter : ∀ (n : ℕ) (g : B.rootGroup α),
      ((σ^[n] g : B.rootGroup α) : rationalPoints G) = b ^ n * g * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply', hσ, ih, pow_succ']
      group
  have hσtend : ∀ g : B.rootGroup α, Tendsto (fun n : ℕ => σ^[n] g) atTop (𝓝 1) := by
    intro g
    rw [tendsto_subtype_rng]
    simp only [hiter, OneMemClass.coe_one]
    exact htend g g.2
  have hne : ∃ g : B.rootGroup α, g ≠ 1 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have hsub : x.val α '' (B.rootGroup α : Set (rationalPoints G)) ⊆ {x.val α 1} := by
      rintro _ ⟨g, hg, rfl⟩
      rw [show g = 1 from congrArg Subtype.val (h ⟨g, hg⟩)]
      rfl
    have h3 := x.isValuation.three_le_encard α α.2
    have h1 := (Set.encard_le_encard hsub).trans (Set.encard_singleton _).le
    have := h3.trans h1
    norm_num at this
  obtain ⟨L, hLc, -⟩ := rationalPoint_subgroup_compactOpenCofinal F G (B.rootGroup α)
    (B.isClosed_rootGroup α) ⊤
  have hLo : IsOpen (L : Set (B.rootGroup α)) := L.isOpen
  have hL1 : (1 : B.rootGroup α) ∈ (L : Set (B.rootGroup α)) := L.one_mem
  refine ⟨?_, fun r => ⟨?_, ?_⟩⟩
  · rw [hpre]
    exact contracting_hasBasis (f := fun g : B.rootGroup α => x.val α g) hfilt htop hlc
      hσshift hc hσtend hne hLo hLc hL1
  · rw [congrFun hpre r]
    exact contracting_isOpen (f := fun g : B.rootGroup α => x.val α g) hfilt htop hlc
      hσshift hc hne r
  · rw [himage]
    exact (contracting_isCompact (f := fun g : B.rootGroup α => x.val α g) hfilt htop hlc
      hσshift hc hσtend hne hLo hLc hL1 r).image continuous_subtype_val

/-- **Axiom V 7** (KP Definition 6.1.2) for every building datum: for every valuation of the
class `A(S)` and every root `a`, the sets `U_{a,x,r}` are open in `U_a(F)`, algebraically
bounded in `G(F)`, and form a neighbourhood base of `1` in `U_a(F)`. -/
theorem isTopologyCompatible : B.IsTopologyCompatible := by
  intro φ hφ a ha
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  obtain ⟨hbasis, hr⟩ := B.rootFiltration_topology ⟨φ, hφ⟩ ⟨a, ha⟩
  refine ⟨hbasis, fun r => ⟨(hr r).1, ?_⟩⟩
  exact (localFieldAffineBoundedCompactness_proof F G.X _ (hr r).2.isClosed).mpr (hr r).2

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.Geometry.Building

/-- **Axiom V 7 for every building datum** (KP Definition 6.1.2, V 7). For every
nonarchimedean local field `F`, every `G` over `Spec F` and every `B : ValuationBuildingData G`,
every valuation of the class `A(S)` of `B` is compatible with the topology of `G(F)`: for every
root `a`, the sets `U_{a,x,r}` are open in `U_a(F)`, algebraically bounded in `G(F)`, and form a
neighbourhood base of `1` in `U_a(F)`. -/
def ValuationBuildingTopologyCompatibleStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G), B.IsTopologyCompatible

/-- Proof of `ValuationBuildingTopologyCompatibleStatement`. -/
theorem valuationBuildingTopologyCompatible :
    ValuationBuildingTopologyCompatibleStatement.{u} :=
  fun _ _ _ _ _ _ _ B => B.isTopologyCompatible

end Langlands.Geometry.Building
