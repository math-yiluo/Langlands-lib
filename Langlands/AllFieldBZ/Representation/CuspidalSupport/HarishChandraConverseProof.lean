import Langlands.AllFieldBZ.Group.GL.BlockIwahoriBasis
import Langlands.AllFieldBZ.Representation.CuspidalSupport.HarishChandraConverseStatement
import Langlands.AllFieldBZ.Representation.Geometric.RefinementDefinitions
import Langlands.AllFieldBZ.Representation.Jacquet.BlockPowerKernelProof
import Langlands.Representation.CuspidalSupport.HarishChandraConverseProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.HarishChandraConverseProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.HarishChandraConverseProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open Filter
open Topology
open scoped NNReal
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding LeviHarishChandraConverseTheorem LeviHarishChandraTheorem continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
universe uF uV

namespace HarishChandra
open Langlands.CuspidalSupport.HarishChandra hiding compressedAction_blockScalar_pow eventually_blockScalar_pow_notMem exists_strictlyContracting_determinantNorm_eq_one isLeviQuasicuspidal_of_hasCompactSmoothDualCoefficients mulSingle_mem_determinantUnitSubgroup
open Langlands.GeneralLinear
open Langlands.Geometric
section LinearAlgebra
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end LinearAlgebra
section Averaging
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Averaging
section Product
variable {ι : Type*} [DecidableEq ι] {G : ι → Type*} [∀ i, Group (G i)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Product
section Refinement
variable {R : Type*} [CommRing R] {n : ℕ} (B : BlockShape n)

end Refinement
section Scalars
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A strictly contracting block-scalar tuple whose block scalar has
determinant of normalized absolute value one. -/
theorem exists_strictlyContracting_determinantNorm_eq_one {m : ℕ} (C : BlockShape m) :
    ∃ a : Fin C.length → F.Carrierˣ, C.IsStrictlyContracting_allFieldBZ T a ∧
      T.determinantNorm m (C.blockScalar F.Carrier a) = 1 := by
  obtain ⟨b, hb⟩ := C.deepChamberNonempty_allFieldBZ T 1 one_pos
  have hbs := Langlands.GeneralLinear.BlockShape.IsDeeplyContracting_allFieldBZ.strict C T hb le_rfl
  let d : F.Carrierˣ := GeneralLinear.determinant (C.blockScalar F.Carrier b)
  refine ⟨b ^ m * (fun _ => d⁻¹), ?_, ?_⟩
  · intro i j hij
    have hm : 0 < m := by
      rw [← C.sum_eq]
      exact lt_of_lt_of_le (C.positive i)
        (Finset.single_le_sum (fun k _ => Nat.zero_le (C.size k)) (Finset.mem_univ i))
    have hc : C.blockScalarRatio_allFieldBZ T i j (fun _ => d⁻¹) = 1 := by
      simp
    rw [map_mul, map_pow, hc, mul_one, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    exact pow_lt_one₀ (by positivity) (hbs i j hij) hm.ne'
  · rw [C.blockScalar_mul, map_pow, map_mul, map_pow, blockScalar_const,
      T.determinantNorm_scalar]
    change T.normalizedAbsUnits d ^ m * T.normalizedAbsUnits d⁻¹ ^ m = 1
    rw [← mul_pow, ← map_mul, mul_inv_cancel, map_one, one_pow]

/-- Powers of a strictly contracting block scalar with at least two blocks
eventually leave every compact subset of the general linear group. -/
theorem eventually_blockScalar_pow_notMem {m : ℕ} (C : BlockShape m) (hC : 2 ≤ C.length)
    (a : Fin C.length → F.Carrierˣ) (ha : C.IsStrictlyContracting_allFieldBZ T a) :
    letI := T.topology
    ∀ Kc : Set (GeneralLinear m F.Carrier), IsCompact Kc →
      ∀ᶠ r : ℕ in atTop, (C.blockScalar F.Carrier a) ^ r ∉ Kc := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  intro Kc hKc
  let i0 : Fin C.length := ⟨0, by omega⟩
  let i1 : Fin C.length := ⟨1, by omega⟩
  have h01 : i0 < i1 := by
    change (0 : ℕ) < 1
    exact Nat.zero_lt_one
  let φ : GeneralLinear m F.Carrier → ℝ := fun g =>
    T.normalizedAbs (g (C.index i1 ⟨0, C.positive i1⟩) (C.index i1 ⟨0, C.positive i1⟩)) *
      T.normalizedAbs ((g⁻¹ : GeneralLinear m F.Carrier)
        (C.index i0 ⟨0, C.positive i0⟩) (C.index i0 ⟨0, C.positive i0⟩))
  have hφ : Continuous φ := by
    have hn : Continuous (fun z : F.Carrier => T.normalizedAbs z) :=
      NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
    exact (hn.comp (GeneralLinear.entry _ _).continuous).mul
      (hn.comp ((GeneralLinear.entry _ _).continuous.comp continuous_inv))
  obtain ⟨M, hM⟩ := (hKc.image hφ).bddAbove
  let u : ℝ≥0ˣ := T.normalizedAbsUnits (a i1 * (a i0)⁻¹)
  have hc : 1 < ((u : ℝ≥0) : ℝ) := by
    have h := ha i0 i1 h01
    rw [C.blockScalarRatio_apply_allFieldBZ] at h
    have e : a i0 * (a i1)⁻¹ = (a i1 * (a i0)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [e, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv] at h
    have hpos : 0 < ((u : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr u.ne_zero)
    exact (inv_lt_one₀ hpos).mp h
  have hval : ∀ r : ℕ, φ ((C.blockScalar F.Carrier a) ^ r) = ((u : ℝ≥0) : ℝ) ^ r := by
    intro r
    have e1 : ((C.blockScalar F.Carrier a) ^ r : GeneralLinear m F.Carrier)
        (C.index i1 ⟨0, C.positive i1⟩) (C.index i1 ⟨0, C.positive i1⟩) =
          ((a i1 ^ r : F.Carrierˣ) : F.Carrier) := by
      rw [← map_pow, C.blockScalar_apply_same]
      simp
    have e2 : (((C.blockScalar F.Carrier a) ^ r)⁻¹ : GeneralLinear m F.Carrier)
        (C.index i0 ⟨0, C.positive i0⟩) (C.index i0 ⟨0, C.positive i0⟩) =
          (((a i0 ^ r)⁻¹ : F.Carrierˣ) : F.Carrier) := by
      rw [← map_pow, ← map_inv, C.blockScalar_apply_same]
      simp
    simp only [φ, e1, e2]
    rw [← T.normalizedAbsUnits_coe, ← T.normalizedAbsUnits_coe, ← NNReal.coe_mul,
      ← Units.val_mul, ← map_mul, ← inv_pow, ← mul_pow, map_pow, Units.val_pow_eq_pow_val,
      NNReal.coe_pow]
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hc).eventually_gt_atTop M] with r hr hmem
  have hle := hM ⟨_, hmem, rfl⟩
  rw [hval] at hle
  linarith

/-- Powers of a weakly contracting block scalar compress multiplicatively. -/
theorem compressedAction_blockScalar_pow {m : ℕ} (C : BlockShape m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup m
    ∀ (ρ : Representation ℂ (GeneralLinear m F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear m F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear m F.Carrier))),
      C.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ a : Fin C.length → F.Carrierˣ, C.IsWeaklyContracting_allFieldBZ T a → ∀ r : ℕ,
        Jacquet.compressedAction ρ hρ K hK (C.blockScalar F.Carrier a) ^ r =
          Jacquet.compressedAction ρ hρ K hK (C.blockScalar F.Carrier (a ^ r)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup m
  intro ρ hρ K hK hfac a ha
  have hweak (r : ℕ) : C.IsWeaklyContracting_allFieldBZ T (a ^ r) := by
    induction r with
    | zero => simpa only [pow_zero] using C.isWeaklyContracting_one_allFieldBZ T
    | succ r hr => simpa only [pow_succ] using Langlands.GeneralLinear.BlockShape.IsWeaklyContracting_allFieldBZ.mul C T hr ha
  intro r
  induction r with
  | zero => simp only [pow_zero, map_one, Jacquet.compressedAction_one]; rfl
  | succ r hr =>
    rw [pow_succ, hr, pow_succ,
      Jacquet.blockCompressedAction_mul F T m C V ρ hρ K hK hfac _ _ (hweak r) ha]

end Scalars
section Main
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- A tuple supported on one block lies in `G°` when that block does. -/
theorem mulSingle_mem_determinantUnitSubgroup {n : ℕ} (B : BlockShape n) (i₀ : Fin B.length)
    (g : GeneralLinear (B.size i₀) F.Carrier) (hg : T.determinantNorm (B.size i₀) g = 1) :
    (Pi.mulSingle i₀ g : B.Levi F.Carrier) ∈ determinantUnitSubgroup T B := by
  rw [mem_determinantUnitSubgroup]
  intro i
  by_cases h : i = i₀
  · subst h
    simpa using hg
  · rw [Pi.mulSingle_eq_of_ne h, map_one]

/-- BZ76 Theorem 3.21, (4) ⇒ (1): if every coefficient of the restriction to `G°`
against a smooth dual vector has compact support, the representation is
quasicuspidal on the product Levi. -/
theorem isLeviQuasicuspidal_of_hasCompactSmoothDualCoefficients {n : ℕ} (B : BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ ρ : Representation ℂ (B.Levi F.Carrier) V, IsSmooth ρ →
      HasCompactSmoothDualCoefficients (determinantUnitRestriction T B ρ) →
        IsLeviQuasicuspidal B ρ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hρ hcc S hS
  obtain ⟨i₀, hi₀⟩ := exists_two_le_length_of_refinedParabolic_ne_top B S hS
  let := T.generalLinearTopologicalGroup (B.size i₀)
  let ρ₀ : Representation ℂ (GeneralLinear (B.size i₀) F.Carrier) V :=
    ρ.comp (MonoidHom.mulSingle (fun i => GeneralLinear (B.size i) F.Carrier) i₀)
  have hρ₀ : IsSmooth ρ₀ := isSmooth_comp _ (continuous_mulSingle i₀) hρ
  suffices hrel : ∀ v : V, v ∈ Jacquet.relations ρ₀ ((S i₀).unipotentSubgroup F.Carrier) by
    refine ⟨fun x y => ?_⟩
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ _ x
    obtain ⟨w, rfl⟩ := Jacquet.mk_surjective ρ _ y
    rw [← sub_eq_zero, ← map_sub, Jacquet.mk_eq_zero]
    exact relations_mulSingle_le B ρ S i₀ (hrel _)
  intro v
  -- A product of compact open subgroups with block Iwahori factorizations fixing `v`.
  obtain ⟨H, hH⟩ := hρ v
  have hH1 : (H : Set (B.Levi F.Carrier)) ∈ 𝓝 (1 : B.Levi F.Carrier) := H.mem_nhds_one
  rw [nhds_pi, Filter.mem_pi'] at hH1
  obtain ⟨I, O, hO, hOH⟩ := hH1
  choose K hKc hKO hfac using fun j => (S j).blockIwahoriBasis_allFieldBZ T (O j) (hO j)
  let N : OpenSubgroup (B.Levi F.Carrier) :=
    { toSubgroup := Subgroup.pi Set.univ fun j => (K j).toSubgroup
      isOpen' := by
        change IsOpen ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
          Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
        rw [Subgroup.coe_pi]
        exact isOpen_set_pi Set.finite_univ fun j _ => (K j).isOpen }
  have hNc : IsCompact (N : Set (B.Levi F.Carrier)) := by
    change IsCompact ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
      Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
    rw [Subgroup.coe_pi]
    exact isCompact_univ_pi fun j => hKc j
  have hvN : ∀ g ∈ Subgroup.pi Set.univ (fun j => (K j).toSubgroup), ρ g v = v := by
    intro g hg
    have hgH : g ∈ (H : Set (B.Levi F.Carrier)) := by
      apply hOH
      intro j _
      exact hKO j (hg j (Set.mem_univ j))
    exact hH ⟨g, hgH⟩
  have hv₀ : v ∈ fixedVectors ρ₀ (K i₀).toSubgroup := by
    intro k
    exact hvN _ ((Subgroup.mulSingle_mem_pi (I := Set.univ)
      (H := fun j => (K j).toSubgroup) i₀ k.val).mpr fun _ => k.property)
  -- A strictly contracting block scalar in `G°`.
  obtain ⟨a, ha, hdet⟩ := exists_strictlyContracting_determinantNorm_eq_one T (S i₀)
  have hker := Jacquet.blockPowerKernel_eq_jacquetKernel F T (S i₀) V ρ₀ hρ₀ (K i₀) (hKc i₀)
    (hfac i₀) a ha
  suffices hsup : (⟨v, hv₀⟩ : fixedVectors ρ₀ (K i₀).toSubgroup) ∈
      Jacquet.powerKernelSup ρ₀ hρ₀ (K i₀) (hKc i₀) ((S i₀).blockScalar F.Carrier a) by
    rw [hker, LinearMap.mem_ker] at hsup
    rw [← Jacquet.mk_eq_zero]
    exact Subtype.ext_iff.mp hsup
  suffices hex : ∃ r : ℕ, Compact.averageMap ρ₀ hρ₀ (K i₀) (hKc i₀)
      (ρ₀ (((S i₀).blockScalar F.Carrier a) ^ r) v) = 0 by
    obtain ⟨r, hr⟩ := hex
    apply le_iSup (fun s : ℕ => LinearMap.ker
      (Jacquet.compressedAction ρ₀ hρ₀ (K i₀) (hKc i₀) ((S i₀).blockScalar F.Carrier a) ^ s)) r
    rw [LinearMap.mem_ker, compressedAction_blockScalar_pow T (S i₀) ρ₀ hρ₀ (K i₀) (hKc i₀)
      (hfac i₀) a ha.weak r]
    apply Subtype.ext
    change Compact.averageMap ρ₀ hρ₀ (K i₀) (hKc i₀)
      (ρ₀ ((S i₀).blockScalar F.Carrier (a ^ r)) v) = 0
    rw [map_pow]
    exact hr
  apply exists_eq_zero_of_eventually_dual
  intro ℓ
  -- Average the functional over `N`; the result is smooth for `G°`.
  let ℓ' : Module.Dual ℂ V := ℓ ∘ₗ Compact.averageMap ρ hρ N hNc
  have hℓ' : IsSmoothVector (determinantUnitRestriction T B ρ).dual ℓ' := by
    refine ⟨OpenSubgroup.comap (determinantUnitInclusion T B)
      (continuous_determinantUnitInclusion T B) N, ?_⟩
    intro g
    apply LinearMap.ext
    intro x
    change ℓ (Compact.averageMap ρ hρ N hNc (ρ (g.val.val)⁻¹ x)) =
      ℓ (Compact.averageMap ρ hρ N hNc x)
    rw [averageMap_apply_mem ρ hρ N hNc (k := (g.val.val)⁻¹) (N.inv_mem g.property)]
  have hcs := hcc v ℓ' hℓ'
  let φ : determinantUnitSubgroup T B → GeneralLinear (B.size i₀) F.Carrier :=
    fun g => g.val i₀
  have hφ : Continuous φ := (continuous_apply i₀).comp continuous_subtype_val
  filter_upwards [eventually_blockScalar_pow_notMem T (S i₀) hi₀ a ha _
    (hcs.isCompact.image hφ)] with r hr
  have hmem : (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r) : B.Levi F.Carrier) ∈
      determinantUnitSubgroup T B :=
    mulSingle_mem_determinantUnitSubgroup T B i₀ _ (by rw [map_pow, hdet, one_pow])
  have hns : (⟨_, hmem⟩ : determinantUnitSubgroup T B) ∉
      tsupport (matrixCoefficient (determinantUnitRestriction T B ρ) ℓ' v) := by
    intro h
    exact hr ⟨_, h, Pi.mulSingle_eq_same i₀ _⟩
  have hz := image_eq_zero_of_notMem_tsupport hns
  have havg : Compact.averageMap ρ hρ N hNc
      (ρ (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r)) v) =
        Compact.averageMap ρ₀ hρ₀ (K i₀) (hKc i₀)
          (ρ (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r)) v) := by
    change Compact.orbitMean (ρ.comp (Subgroup.pi Set.univ fun j => (K j).toSubgroup).subtype)
        (ρ (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r)) v) =
      Compact.orbitMean ((ρ.comp (MonoidHom.mulSingle
        (fun i => GeneralLinear (B.size i) F.Carrier) i₀)).comp (K i₀).toSubgroup.subtype)
        (ρ (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r)) v)
    unfold Compact.orbitMean
    rw [orbit_pi_eq_orbit_single ρ (fun j => (K j).toSubgroup) i₀ v hvN]
  change ℓ (Compact.averageMap ρ₀ hρ₀ (K i₀) (hKc i₀)
    (ρ (Pi.mulSingle i₀ (((S i₀).blockScalar F.Carrier a) ^ r)) v)) = 0
  rw [← havg]
  exact hz

end Main
end HarishChandra
/-- BZ76 Theorem 3.21, (4) implies (1), on actual p-adic product Levis. -/
theorem leviHarishChandraConverseTheorem : LeviHarishChandraConverseTheorem.{uF, uV} := by
  intro F T n B
  let := T.topology
  intro A
  exact HarishChandra.isLeviQuasicuspidal_of_hasCompactSmoothDualCoefficients T B
    A.representation A.isSmooth

end Langlands.AllFieldBZ.CuspidalSupport
