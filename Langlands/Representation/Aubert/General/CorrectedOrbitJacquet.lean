import Langlands.Representation.Aubert.General.CorrectedGradedInterface
import Langlands.Representation.Induction.SplitKernelValueIntegral
import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Representation.Jacquet.LocalizationExactnessStatement

/-!
# The orbit Jacquet maps of the corrected Aubert complex

For a semidirect decomposition `P_I = M_I ⋉ U_I`, an element `m` with
`m⁻¹ M_I m = M_K`, and a parabolic `P_J ⊇ P_K` normalizing `U_J ≤ U_K`, this
file builds the map

`Θ : c-Ind_{P_I ∩ m P_J m⁻¹}^{P_I}(E_{U_J} ∘ Ad(m⁻¹)) → E_{U_K}`,
`Θ φ = ∫_{(U_I ∩ m U_K m⁻¹) \ U_I} [φ(n)]_{U_K} dn`,

by specializing the split-kernel value integral to the Levi projection
`P_I →* M_I` and the orbit stabilizer `P_I ∩ m P_J m⁻¹`.
-/

noncomputable section

open CategoryTheory MeasureTheory MeasureTheory.Measure
open Langlands.QuotientIntegration
open scoped NNReal

namespace Langlands.Aubert.General.CorrectedFiltration

universe uG uV

section Scalar

/-- The scalar identity behind the normalized `M_I`-equivariance:
`a b = c ^ 2` gives `a^{-1/2} (c⁻¹ / a⁻¹) = b^{-1/2}`. -/
theorem inv_sqrt_mul_ratio_eq {a b c : ℝ≥0} (hc : c ≠ 0) (h : a * b = c ^ 2) :
    (NNReal.sqrt a)⁻¹ * (c⁻¹ / a⁻¹) = (NNReal.sqrt b)⁻¹ := by
  have hsb : NNReal.sqrt a * NNReal.sqrt b = c := by
    rw [← NNReal.sqrt_mul, h, NNReal.sqrt_sq]
  have hs : NNReal.sqrt a ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hsb
    exact hc hsb.symm
  have ha : a = NNReal.sqrt a * NNReal.sqrt a := (NNReal.mul_self_sqrt a).symm
  generalize NNReal.sqrt a = x at ha hsb hs ⊢
  generalize NNReal.sqrt b = y at hsb ⊢
  subst ha hsb
  rw [inv_div_inv, mul_div_mul_left _ _ hs, div_eq_mul_inv, inv_mul_cancel_left₀ hs]

end Scalar

section Subgroups

variable {G : Type uG} [Group G]

/-- The kernel intersection `{n ∈ U_I : m⁻¹ n m ∈ U_K}`, as a subgroup of the
kernel of the actual Levi projection `P_I →* M_I`. -/
def orbitKernelIntersection {PI MI UI : Subgroup G} (hdI : IsSemidirectDecomposition PI MI UI)
    (UK : Subgroup G) (m : G) : Subgroup hdI.projection.ker :=
  UK.comap ((MulAut.conj m⁻¹).toMonoidHom.comp (PI.subtype.comp hdI.projection.ker.subtype))

theorem mem_orbitKernelIntersection {PI MI UI : Subgroup G}
    (hdI : IsSemidirectDecomposition PI MI UI) (UK : Subgroup G) (m : G)
    (n : hdI.projection.ker) :
    n ∈ orbitKernelIntersection hdI UK m ↔ m⁻¹ * ((n : PI) : G) * m ∈ UK := by
  simp [orbitKernelIntersection]

/-- The ambient intersection `U_I ∩ m U_K m⁻¹`. -/
def orbitUnipotentIntersection (UI UK : Subgroup G) (m : G) : Subgroup G :=
  UI ⊓ UK.comap (MulAut.conj m⁻¹).toMonoidHom

theorem mem_orbitUnipotentIntersection (UI UK : Subgroup G) (m : G) (x : G) :
    x ∈ orbitUnipotentIntersection UI UK m ↔ x ∈ UI ∧ m⁻¹ * x * m ∈ UK := by
  simp [orbitUnipotentIntersection]

theorem mem_orbitStabilizer [TopologicalSpace G] [IsTopologicalGroup G] (PJ PI : Subgroup G)
    (m : G) (q : PI) :
    q ∈ Geometric.orbitStabilizer PJ PI m ↔ m⁻¹ * (q : G) * m ∈ PJ := by
  simp [Geometric.orbitStabilizer]

theorem mem_projection_ker {PI MI UI : Subgroup G} (hdI : IsSemidirectDecomposition PI MI UI)
    (p : PI) : p ∈ hdI.projection.ker ↔ (p : G) ∈ UI :=
  hdI.projection_eq_one_iff p

/-- A Levi `M_I` with `m⁻¹ M_I m = M_K` normalizes `U_I ∩ m U_K m⁻¹`. -/
theorem levi_le_normalizer_orbitUnipotentIntersection {PI MI UI PK MK UK : Subgroup G}
    (hdI : IsSemidirectDecomposition PI MI UI) (hdK : IsSemidirectDecomposition PK MK UK)
    (m : G) (hconj : ∀ x : G, x ∈ MI ↔ m⁻¹ * x * m ∈ MK) :
    MI ≤ Subgroup.normalizer (orbitUnipotentIntersection UI UK m : Set G) := by
  have key : ∀ l ∈ MI, ∀ u ∈ orbitUnipotentIntersection UI UK m,
      l * u * l⁻¹ ∈ orbitUnipotentIntersection UI UK m := by
    intro l hl u hu
    rw [mem_orbitUnipotentIntersection] at hu ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hdI.levi_le_normalizer hl) u).mp hu.1, ?_⟩
    have hl' := (hconj l).mp hl
    have h := (Subgroup.mem_normalizer_iff.mp (hdK.levi_le_normalizer hl') _).mp hu.2
    simpa [mul_assoc] using h
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key l hl u, fun hu => ?_⟩
  have h := key l⁻¹ (MI.inv_mem hl) _ hu
  simpa [mul_assoc] using h

end Subgroups

section Topology

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- A topological group inducing into a nonarchimedean group is nonarchimedean. -/
theorem nonarchimedeanGroup_of_isInducing [NonarchimedeanGroup G] {X : Type*} [Group X]
    [TopologicalSpace X] [IsTopologicalGroup X] (f : X →* G) (hf : Topology.IsInducing f) :
    NonarchimedeanGroup X where
  is_nonarchimedean O hO := by
    rw [hf.nhds_eq_comap, map_one] at hO
    obtain ⟨O', hO', hsub⟩ := hO
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean O' hO'
    exact ⟨OpenSubgroup.comap f hf.continuous V, fun x hx => hsub (hV hx)⟩

/-- Haar moduli transported through a topological isomorphism onto a closed
subgroup: if `e : X ≃ₜ* Z` carries `φ` to conjugation by `g`, then the Haar
modulus of `φ` is the normalizer character of `Z` at `g`. -/
theorem mulEquivHaarChar_eq_closedNormalizerCharacter [LocallyCompactSpace G]
    {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Z : Subgroup G) (hZ : IsClosed (Z : Set G))
    (g : Subgroup.normalizer (Z : Set G)) (e : X ≃ₜ* Z) (φ : X ≃ₜ* X)
    (hφ : ∀ x, ((e (φ x) : Z) : G) = g * (e x : G) * (g : G)⁻¹) :
    mulEquivHaarChar φ = (HaarModulus.closedNormalizerCharacter Z hZ g : ℝ≥0) := by
  have : LocallyCompactSpace Z := hZ.locallyCompactSpace
  let : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  have hφ' : φ = (e.trans (HaarModulus.normalizerConj Z g)).trans e.symm := by
    apply ContinuousMulEquiv.ext
    intro x
    apply e.injective
    apply Subtype.ext
    simp only [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply]
    rw [hφ x, HaarModulus.normalizerConj_apply]
  rw [hφ', mulEquivHaarChar_trans_symm]
  rfl

theorem continuous_stabilizerToInducing (PJ PI : Subgroup G) (m : G) :
    Continuous (Geometric.stabilizerToInducing PJ PI m) := by
  apply Continuous.subtype_mk
  change Continuous fun q : Geometric.orbitStabilizer PJ PI m => m⁻¹ * ((q : PI) : G) * m⁻¹⁻¹
  fun_prop

theorem isClosed_orbitUnipotentIntersection {UI UK : Subgroup G} (hUIc : IsClosed (UI : Set G))
    (hUKc : IsClosed (UK : Set G)) (m : G) :
    IsClosed (orbitUnipotentIntersection UI UK m : Set G) := by
  apply hUIc.inter
  apply hUKc.preimage
  change Continuous fun x : G => m⁻¹ * x * m⁻¹⁻¹
  fun_prop

theorem isClosed_orbitStabilizer (PJ PI : Subgroup G) (hPJc : IsClosed (PJ : Set G)) (m : G) :
    IsClosed (Geometric.orbitStabilizer PJ PI m : Set PI) := by
  apply hPJc.preimage
  change Continuous fun q : PI => m⁻¹ * (q : G) * m⁻¹⁻¹
  fun_prop

variable {PI MI UI : Subgroup G} (hdI : IsSemidirectDecomposition PI MI UI)

omit [IsTopologicalGroup G] in
theorem isClosed_projection_ker (hUIc : IsClosed (UI : Set G)) :
    IsClosed (hdI.projection.ker : Set PI) := by
  have h : (hdI.projection.ker : Set PI) = Subtype.val ⁻¹' (UI : Set G) :=
    Set.ext fun p => mem_projection_ker hdI p
  rw [h]
  exact hUIc.preimage continuous_subtype_val

theorem isClosed_orbitKernelIntersection (UK : Subgroup G) (hUKc : IsClosed (UK : Set G))
    (m : G) : IsClosed (orbitKernelIntersection hdI UK m : Set hdI.projection.ker) := by
  apply hUKc.preimage
  change Continuous fun n : hdI.projection.ker => m⁻¹ * ((n : PI) : G) * m⁻¹⁻¹
  fun_prop

omit [IsTopologicalGroup G] in
theorem continuous_levi_inclusion : Continuous (Subgroup.inclusion hdI.levi_le) :=
  continuous_subtype_val.subtype_mk _

/-- `U_K ≤ P_J` and `(S1)` identify `U_I ∩ m U_K m⁻¹` with `U_I ∩ m P_J m⁻¹`. -/
theorem orbitKernelIntersection_iff {PJ UK : Subgroup G} (m : G) (hUKPJ : UK ≤ PJ)
    (hS1 : ∀ x ∈ UI, m⁻¹ * x * m ∈ PJ → m⁻¹ * x * m ∈ UK) (n : hdI.projection.ker) :
    n ∈ orbitKernelIntersection hdI UK m ↔ (n : PI) ∈ Geometric.orbitStabilizer PJ PI m := by
  rw [mem_orbitKernelIntersection, mem_orbitStabilizer]
  exact ⟨fun h => hUKPJ h, hS1 _ ((mem_projection_ker hdI n).mp n.2)⟩

/-- The Levi `M_I` lies in the orbit stabilizer when `m⁻¹ M_I m ≤ P_J`. -/
theorem orbitLevi_mem {PJ : Subgroup G} (m : G) (hlevi : ∀ x ∈ MI, m⁻¹ * x * m ∈ PJ) (l : MI) :
    Subgroup.inclusion hdI.levi_le l ∈ Geometric.orbitStabilizer PJ PI m :=
  (mem_orbitStabilizer PJ PI m _).mpr (hlevi l l.2)

omit [IsTopologicalGroup G] in
/-- The kernel of the Levi projection `P_I →* M_I` is `U_I`, as a topological group. -/
def projectionKerEquiv : hdI.projection.ker ≃ₜ* UI where
  toFun n := ⟨((n : PI) : G), (mem_projection_ker hdI n).mp n.2⟩
  invFun u := ⟨⟨u, hdI.unipotent_le u.2⟩, (mem_projection_ker hdI _).mpr u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [IsTopologicalGroup G] in
@[simp] theorem projectionKerEquiv_apply (n : hdI.projection.ker) :
    ((projectionKerEquiv hdI n : UI) : G) = ((n : PI) : G) := rfl

omit [IsTopologicalGroup G] in
/-- The kernel intersection is `U_I ∩ m U_K m⁻¹`, as a topological group. -/
def orbitKernelIntersectionEquiv (UK : Subgroup G) (m : G) :
    orbitKernelIntersection hdI UK m ≃ₜ* orbitUnipotentIntersection UI UK m where
  toFun n := ⟨(((n : hdI.projection.ker) : PI) : G),
    ⟨(mem_projection_ker hdI _).mp (n : hdI.projection.ker).2, n.2⟩⟩
  invFun x := ⟨⟨⟨x, hdI.unipotent_le x.2.1⟩, (mem_projection_ker hdI _).mpr x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _).subtype_mk _

omit [IsTopologicalGroup G] in
@[simp] theorem orbitKernelIntersectionEquiv_apply (UK : Subgroup G) (m : G)
    (n : orbitKernelIntersection hdI UK m) :
    ((orbitKernelIntersectionEquiv hdI UK m n : orbitUnipotentIntersection UI UK m) : G) =
      (((n : hdI.projection.ker) : PI) : G) := rfl

omit [IsTopologicalGroup G] in
/-- For `U_I ≤ P_I`, the subgroup `U_I` of `P_I` is `U_I`, as a topological group. -/
def subgroupOfEquiv (hle : UI ≤ PI) : UI.subgroupOf PI ≃ₜ* UI where
  toFun x := ⟨((x : PI) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun u := ⟨⟨u, hle u.2⟩, Subgroup.mem_subgroupOf.mpr u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [IsTopologicalGroup G] in
/-- In a nonarchimedean, weakly locally compact subgroup `V` in which every
compact set lies in a compact subgroup, every element lies in a compact open
subgroup: a compact open subgroup `C₀` together with the element lies in a
compact subgroup, which is open because it contains `C₀`. -/
theorem exists_compactOpen_mem_of_isLimitOfCompactSubgroups (V : Subgroup G)
    [NonarchimedeanGroup V] [WeaklyLocallyCompactSpace V]
    (hV : Jacquet.Localization.IsLimitOfCompactSubgroups V) (v : V) :
    ∃ C : OpenSubgroup V, IsCompact (C : Set V) ∧ v ∈ C := by
  obtain ⟨C₀, hC₀, -⟩ := compactOpenSubgroupBasis V Set.univ Filter.univ_mem
  obtain ⟨K, hK, hsub⟩ := hV ((C₀ : Set V) ∪ {v}) (hC₀.union isCompact_singleton)
  exact ⟨⟨K, Subgroup.isOpen_mono (fun x hx => hsub (Set.mem_union_left _ hx)) C₀.isOpen⟩, hK,
    hsub (Set.mem_union_right _ (Set.mem_singleton v))⟩

end Topology

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The unnormalized inducing representation `p · [v] = [p v]` of `P_J` on the
actual coinvariants `E_{U_J}`. -/
abbrev orbitInducing {PJ UJ : Subgroup G} (hPJ : PJ ≤ Subgroup.normalizer (UJ : Set G))
    (E : SmoothRep.{0, uG, uV} ℂ G) : Induction.SmoothRep.{0, uG, uV} ℂ PJ :=
  Jacquet.Localization.smoothObject UJ 1 PJ hPJ
    (Jacquet.Localization.isInvariant_one UJ PJ hPJ) E

/-- Its conjugated restriction to the orbit stabilizer `P_I ∩ m P_J m⁻¹`:
`q · [v] = [(m⁻¹ q m) v]`. -/
abbrev orbitCoefficient (PI : Subgroup G) {PJ UJ : Subgroup G}
    (hPJ : PJ ≤ Subgroup.normalizer (UJ : Set G)) (m : G) (E : SmoothRep.{0, uG, uV} ℂ G) :
    Representation ℂ (Geometric.orbitStabilizer PJ PI m)
      (Jacquet.Localization.Coinvariants E.representation UJ 1) :=
  (orbitInducing hPJ E).representation.comp (Geometric.stabilizerToInducing PJ PI m)

/-- The coinvariant transition `E_{U_J} → E_{U_K}`, `[v] ↦ [v]`. -/
abbrev orbitTransition {UJ UK : Subgroup G} (hUJK : UJ ≤ UK) (E : SmoothRep.{0, uG, uV} ℂ G) :
    Jacquet.Localization.Coinvariants E.representation UJ 1 →ₗ[ℂ]
      Jacquet.Localization.Coinvariants E.representation UK 1 :=
  Jacquet.Localization.transitionLinear UJ UK hUJK 1 1 (fun _ => rfl) E.representation

omit [LocallyCompactSpace G] in
theorem orbitCoefficient_isSmooth (PI : Subgroup G) {PJ UJ : Subgroup G}
    (hPJ : PJ ≤ Subgroup.normalizer (UJ : Set G)) (m : G) (E : SmoothRep.{0, uG, uV} ℂ G) :
    IsSmooth (orbitCoefficient PI hPJ m E) :=
  isSmooth_comp _ (continuous_stabilizerToInducing PJ PI m) (orbitInducing hPJ E).isSmooth

variable {PI MI UI : Subgroup G} (hdI : IsSemidirectDecomposition PI MI UI)
variable {PJ UJ UK : Subgroup G} (hPJ : PJ ≤ Subgroup.normalizer (UJ : Set G))
  (hUJK : UJ ≤ UK) (m : G) (E : SmoothRep.{0, uG, uV} ℂ G)

omit [LocallyCompactSpace G] in
include hdI in
/-- Under `(S1)`, the transition kills the action of `U_I ∩ m P_J m⁻¹`. -/
theorem orbitTransition_invariant
    (hS1 : ∀ x ∈ UI, m⁻¹ * x * m ∈ PJ → m⁻¹ * x * m ∈ UK)
    (x : Geometric.orbitStabilizer PJ PI m) (hx : (x : PI) ∈ hdI.projection.ker)
    (v : Jacquet.Localization.Coinvariants E.representation UJ 1) :
    orbitTransition hUJK E (orbitCoefficient PI hPJ m E x v) = orbitTransition hUJK E v := by
  obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective E.representation UJ 1 v
  have hxU : ((x : PI) : G) ∈ UI := (mem_projection_ker hdI x).mp hx
  have hxP : m⁻¹ * ((x : PI) : G) * m ∈ PJ := (mem_orbitStabilizer PJ PI m x).mp x.2
  have hK : ((Geometric.stabilizerToInducing PJ PI m x : PJ) : G) ∈ UK := by
    rw [Geometric.stabilizerToInducing_apply]
    exact hS1 _ hxU hxP
  change Jacquet.Localization.mk E.representation UK 1
      (E.representation ((Geometric.stabilizerToInducing PJ PI m x : PJ) : G) w) =
    Jacquet.Localization.mk E.representation UK 1 w
  rw [show ((Geometric.stabilizerToInducing PJ PI m x : PJ) : G) = ((⟨_, hK⟩ : UK) : G) from rfl,
    Jacquet.Localization.mk_apply_subgroup]
  simp

/-- Compact open subgroups form a neighborhood basis of the identity in the
kernel `U_I` of the Levi projection. -/
theorem projection_ker_compactOpenBasis (hPIc : IsClosed (PI : Set G))
    (hUIc : IsClosed (UI : Set G)) :
    ∀ O : Set hdI.projection.ker, IsOpen O → (1 : hdI.projection.ker) ∈ O →
      ∃ K : OpenSubgroup hdI.projection.ker,
        IsCompact (K : Set hdI.projection.ker) ∧ (K : Set hdI.projection.ker) ⊆ O := by
  have : NonarchimedeanGroup hdI.projection.ker :=
    nonarchimedeanGroup_of_isInducing (PI.subtype.comp hdI.projection.ker.subtype)
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have : LocallyCompactSpace PI := hPIc.locallyCompactSpace
  have : LocallyCompactSpace hdI.projection.ker :=
    (isClosed_projection_ker hdI hUIc).locallyCompactSpace
  intro O hO h1
  exact compactOpenSubgroupBasis _ O (hO.mem_nhds h1)

omit [LocallyCompactSpace G] in
include hdI in
/-- Under `(S2)`, the transition descends to an injective map
`(E_{U_J})_{U_I ∩ m U_K m⁻¹} → E_{U_K}`: its left inverse is
`[v]_{U_K} ↦ [[v]_{U_J}]`. -/
theorem orbitTransition_descent_injective {MJ : Subgroup G}
    (hdJ : IsSemidirectDecomposition PJ MJ UJ) (hUKPJ : UK ≤ PJ)
    (hS1 : ∀ x ∈ UI, m⁻¹ * x * m ∈ PJ → m⁻¹ * x * m ∈ UK)
    (hS2 : ∀ x ∈ MJ, x ∈ UK → m * x * m⁻¹ ∈ UI) :
    Function.Injective (Induction.splitKernelValueDescent hdI.projection
      (Geometric.orbitStabilizer PJ PI m) (orbitCoefficient PI hPJ m E) (orbitTransition hUJK E)
      (orbitTransition_invariant hdI hPJ hUJK m E hS1)) := by
  set σI := (orbitCoefficient PI hPJ m E).comp
    (hdI.projection.ker.subtype.subgroupComap (Geometric.orbitStabilizer PJ PI m))
  have hlift : ∀ (u : UK) (v : E),
      (Representation.Coinvariants.mk σI ∘ₗ Jacquet.Localization.mk E.representation UJ 1)
          (E.representation u v) =
        ((1 : UK →* ℂˣ) u : ℂ) •
          (Representation.Coinvariants.mk σI ∘ₗ Jacquet.Localization.mk E.representation UJ 1) v := by
    intro u v
    rw [MonoidHom.one_apply, Units.val_one, one_smul, LinearMap.comp_apply, LinearMap.comp_apply]
    set a : MJ := hdJ.projection ⟨u, hUKPJ u.2⟩
    have hn : ((a : MJ) : G)⁻¹ * (u : G) ∈ UJ := hdJ.projection_inv_mul_mem ⟨u, hUKPJ u.2⟩
    have hu : (u : G) = (a : G) * ((a : G)⁻¹ * (u : G)) := by group
    have haK : (a : G) ∈ UK := by
      have ha : (a : G) = (u : G) * ((a : G)⁻¹ * (u : G))⁻¹ := by group
      rw [ha]
      exact UK.mul_mem u.2 (UK.inv_mem (hUJK hn))
    have hx : m * (a : G) * m⁻¹ ∈ UI := hS2 a a.2 haK
    have hxH : m⁻¹ * (m * (a : G) * m⁻¹) * m⁻¹⁻¹ ∈ PJ := by
      simpa [mul_assoc] using hdJ.levi_le a.2
    let x : (Geometric.orbitStabilizer PJ PI m).comap hdI.projection.ker.subtype :=
      ⟨⟨⟨m * (a : G) * m⁻¹, hdI.unipotent_le hx⟩, (mem_projection_ker hdI _).mpr hx⟩, hxH⟩
    have h1 : Jacquet.Localization.mk E.representation UJ 1 (E.representation u v) =
        Jacquet.Localization.mk E.representation UJ 1 (E.representation a v) := by
      have hJ := Jacquet.Localization.mk_apply_subgroup E.representation UJ 1 ⟨_, hn⟩ v
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at hJ
      calc Jacquet.Localization.mk E.representation UJ 1 (E.representation u v)
          = Jacquet.Localization.mk E.representation UJ 1
              (E.representation a (E.representation ((a : G)⁻¹ * u) v)) := by
            rw [← Module.End.mul_apply, ← map_mul, ← hu]
        _ = Jacquet.Localization.action E.representation UJ 1 PJ hPJ
              (Jacquet.Localization.isInvariant_one UJ PJ hPJ) ⟨a, hdJ.levi_le a.2⟩
              (Jacquet.Localization.mk E.representation UJ 1
                (E.representation ((a : G)⁻¹ * u) v)) := rfl
        _ = Jacquet.Localization.action E.representation UJ 1 PJ hPJ
              (Jacquet.Localization.isInvariant_one UJ PJ hPJ) ⟨a, hdJ.levi_le a.2⟩
              (Jacquet.Localization.mk E.representation UJ 1 v) := congrArg _ hJ
        _ = Jacquet.Localization.mk E.representation UJ 1 (E.representation a v) := rfl
    have hxa : ((Geometric.stabilizerToInducing PJ PI m
        (hdI.projection.ker.subtype.subgroupComap (Geometric.orbitStabilizer PJ PI m) x) :
          PJ) : G) = a := by
      rw [Geometric.stabilizerToInducing_apply]
      change m⁻¹ * (m * (a : G) * m⁻¹) * m = a
      group
    have h2 : σI x (Jacquet.Localization.mk E.representation UJ 1 v) =
        Jacquet.Localization.mk E.representation UJ 1 (E.representation a v) := by
      change Jacquet.Localization.mk E.representation UJ 1
          (E.representation ((Geometric.stabilizerToInducing PJ PI m
            (hdI.projection.ker.subtype.subgroupComap (Geometric.orbitStabilizer PJ PI m) x) :
              PJ) : G) v) = _
      rw [hxa]
    rw [h1, ← h2, Representation.Coinvariants.mk_self_apply]
  let inv := Jacquet.Localization.lift E.representation UK 1 _ hlift
  have hleft : Function.LeftInverse inv (Induction.splitKernelValueDescent hdI.projection
      (Geometric.orbitStabilizer PJ PI m) (orbitCoefficient PI hPJ m E) (orbitTransition hUJK E)
      (orbitTransition_invariant hdI hPJ hUJK m E hS1)) := by
    intro z
    obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective σI z
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective E.representation UJ 1 y
    rfl
  exact hleft.injective

variable (hUKPJ : UK ≤ PJ) (hS1 : ∀ x ∈ UI, m⁻¹ * x * m ∈ PJ → m⁻¹ * x * m ∈ UK)
  (hlevi : ∀ x ∈ MI, m⁻¹ * x * m ∈ PJ) (hr : Continuous hdI.projection)
  [MeasurableSpace (LeftQuotient (orbitKernelIntersection hdI UK m))]
  [BorelSpace (LeftQuotient (orbitKernelIntersection hdI UK m))]
  (ν : Measure (LeftQuotient (orbitKernelIntersection hdI UK m))) [IsFiniteMeasureOnCompacts ν]

/-- The orbit Jacquet map `Θ φ = ∫_{(U_I ∩ m U_K m⁻¹) \ U_I} [φ(n)]_{U_K} dν`,
from the actual orbit piece of `E_{U_J}` to the actual coinvariants `E_{U_K}`. -/
def orbitJacquetMap :
    ((Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)) →ₗ[ℂ]
      Jacquet.Localization.Coinvariants E.representation UK 1 :=
  Induction.splitKernelValueIntegral hdI.projection (Geometric.orbitStabilizer PJ PI m)
    (orbitKernelIntersection hdI UK m) (orbitKernelIntersection_iff hdI m hUKPJ hS1)
    (orbitCoefficient PI hPJ m E) (orbitTransition hUJK E)
    (orbitTransition_invariant hdI hPJ hUJK m E hS1)
    (Subgroup.inclusion hdI.levi_le) hdI.projection_levi hr (continuous_levi_inclusion hdI)
    (orbitLevi_mem hdI m hlevi) ν

omit [LocallyCompactSpace G] in
/-- `U_I`-invariance, from the right invariance of the quotient measure. -/
theorem orbitJacquetMap_unipotent
    (hν : ∀ n : hdI.projection.ker,
      MeasurePreserving (rightTranslate (orbitKernelIntersection hdI UK m) n) ν ν)
    (u : UI) (φ : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)) :
    orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν
        (((Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)).ρ
          ⟨u, hdI.unipotent_le u.2⟩ φ) =
      orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ :=
  Induction.splitKernelValueIntegral_translate _ _ _ _ _ _
    (orbitTransition_invariant hdI hPJ hUJK m E hS1) _ _ _ _ _ _ hν
    ⟨⟨u, hdI.unipotent_le u.2⟩, (mem_projection_ker hdI _).mpr u.2⟩ φ

omit [LocallyCompactSpace G] in
/-- Functions related by the pointwise transition `E_{U_J} → E_{U_J'}` have the
same image. -/
theorem orbitJacquetMap_transition {PJ' UJ' : Subgroup G}
    (hPJ' : PJ' ≤ Subgroup.normalizer (UJ' : Set G)) (hUJJ' : UJ ≤ UJ') (hUJ'K : UJ' ≤ UK)
    (hUKPJ' : UK ≤ PJ') (hS1' : ∀ x ∈ UI, m⁻¹ * x * m ∈ PJ' → m⁻¹ * x * m ∈ UK)
    (hlevi' : ∀ x ∈ MI, m⁻¹ * x * m ∈ PJ')
    (φ : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E))
    (ψ : (Geometric.orbitPiece.{0, uG, uV} PJ' PI m).obj (orbitInducing hPJ' E))
    (hφψ : ∀ q : PI, Induction.eval _ _ ψ.val q =
      Jacquet.Localization.transitionLinear UJ UJ' hUJJ' 1 1 (fun _ => rfl) E.representation
        (Induction.eval _ _ φ.val q)) :
    orbitJacquetMap hdI hPJ' hUJ'K m E hUKPJ' hS1' hlevi' hr ν ψ =
      orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ := by
  refine Induction.splitKernelValueIntegral_eq_of_eval _ _ _ _ _ _
    (orbitTransition_invariant hdI hPJ hUJK m E hS1) _ _ _ _ _ ν _ _ _
    (orbitTransition_invariant hdI hPJ' hUJ'K m E hS1') _ φ ψ fun n => ?_
  refine (congrArg (orbitTransition hUJ'K E) (hφψ (n : PI))).trans ?_
  exact LinearMap.congr_fun (Jacquet.Localization.transitionLinear_comp UJ UJ' UK hUJJ' hUJ'K
    1 1 1 (fun _ => rfl) (fun _ => rfl) E.representation) _

omit [LocallyCompactSpace G] in
/-- Naturality in `E`: functions related pointwise by `E_{U_J}(f)` have images
related by `E_{U_K}(f)`. -/
theorem orbitJacquetMap_natural {E' : SmoothRep.{0, uG, uV} ℂ G} (f : E ⟶ E')
    (φ : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E))
    (φ' : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E'))
    (hφφ' : ∀ q : PI, Induction.eval _ _ φ'.val q =
      Jacquet.Localization.mapLinear UJ 1 (SmoothRep.hom f) (Induction.eval _ _ φ.val q)) :
    orbitJacquetMap hdI hPJ hUJK m E' hUKPJ hS1 hlevi hr ν φ' =
      Jacquet.Localization.mapLinear UK 1 (SmoothRep.hom f)
        (orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ) := by
  refine Induction.splitKernelValueIntegral_map_of_eval _ _ _ _ _ _
    (orbitTransition_invariant hdI hPJ hUJK m E hS1) _ _ _ _ _ ν _ _ _
    (orbitTransition_invariant hdI hPJ hUJK m E' hS1) _ _ φ φ' fun n => ?_
  refine (congrArg (orbitTransition hUJK E') (hφφ' (n : PI))).trans ?_
  exact LinearMap.congr_fun (Jacquet.Localization.transitionLinear_natural UJ UK hUJK 1 1
    (fun _ => rfl) (SmoothRep.hom f)) _

/-- Surjectivity, from the surjective transition `E_{U_J} → E_{U_K}`. -/
theorem orbitJacquetMap_surjective [T2Space G] (hPIc : IsClosed (PI : Set G))
    (hUIc : IsClosed (UI : Set G)) (hPJc : IsClosed (PJ : Set G))
    [MeasurableSpace hdI.projection.ker] [BorelSpace hdI.projection.ker]
    [MeasurableSpace (orbitKernelIntersection hdI UK m)]
    [BorelSpace (orbitKernelIntersection hdI UK m)]
    (μN : Measure hdI.projection.ker) (μI : Measure (orbitKernelIntersection hdI UK m))
    [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hCompatible : IsCompatible (orbitKernelIntersection hdI UK m) μN μI ν) :
    Function.Surjective (orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν) := by
  have : LocallyCompactSpace PI := hPIc.locallyCompactSpace
  have : LocallyCompactSpace hdI.projection.ker :=
    (isClosed_projection_ker hdI hUIc).locallyCompactSpace
  exact Induction.splitKernelValueIntegral_surjective _ _ _ _ _ _ _ _ _ _ _ _
    (isClosed_orbitStabilizer PJ PI hPJc m) (orbitCoefficient_isSmooth PI hPJ m E) ν
    (projection_ker_compactOpenBasis hdI hPIc hUIc) μN μI hCompatible
    (Jacquet.Localization.transitionLinear_surjective _ _ _ _ _ _ _)

/-- Kernel: under `(S2)`, `Θ φ = 0` puts `φ` in the actual `U_I`-relations. -/
theorem orbitJacquetMap_ker_le [T2Space G] (hPIc : IsClosed (PI : Set G))
    (hUIc : IsClosed (UI : Set G)) (hPJc : IsClosed (PJ : Set G)) {MJ : Subgroup G}
    (hdJ : IsSemidirectDecomposition PJ MJ UJ)
    (hS2 : ∀ x ∈ MJ, x ∈ UK → m * x * m⁻¹ ∈ UI)
    [MeasurableSpace hdI.projection.ker] [BorelSpace hdI.projection.ker]
    [MeasurableSpace (orbitKernelIntersection hdI UK m)]
    [BorelSpace (orbitKernelIntersection hdI UK m)]
    (μN : Measure hdI.projection.ker) (μI : Measure (orbitKernelIntersection hdI UK m))
    [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hCompatible : IsCompatible (orbitKernelIntersection hdI UK m) μN μI ν)
    (φ : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E))
    (hφ : orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ = 0) :
    φ ∈ Jacquet.Localization.relations
      ((Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)).ρ
      (UI.subgroupOf PI) 1 := by
  have : LocallyCompactSpace PI := hPIc.locallyCompactSpace
  have : LocallyCompactSpace hdI.projection.ker :=
    (isClosed_projection_ker hdI hUIc).locallyCompactSpace
  have hmem := Induction.splitKernelValueIntegral_mem_ker _ _ _ _ _ _ _ _ _ _ _ _
    (isClosed_orbitStabilizer PJ PI hPJc m) (orbitCoefficient_isSmooth PI hPJ m E) ν
    (projection_ker_compactOpenBasis hdI hPIc hUIc) μN μI hCompatible
    (orbitTransition_descent_injective hdI hPJ hUJK m E hdJ hUKPJ hS1 hS2) φ hφ
  refine (Submodule.span_le.mpr ?_) hmem
  rintro _ ⟨⟨n, x⟩, rfl⟩
  let y : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E) := x
  have h := Jacquet.Localization.sub_mem_relations
    ((Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)).ρ
    (UI.subgroupOf PI) 1
    ⟨(n : PI), Subgroup.mem_subgroupOf.mpr ((mem_projection_ker hdI n).mp n.2)⟩ y
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h

/-- `M_I`-equivariance for the normalized actions, from the section law and the
modulus identity `δ_{U_I}(l) δ_{U_K}(m⁻¹ l m) = δ_{U_I ∩ m U_K m⁻¹}(l) ^ 2`. -/
theorem orbitJacquetMap_levi [T2Space G] (hPIc : IsClosed (PI : Set G))
    (hUIc : IsClosed (UI : Set G)) (hUKc : IsClosed (UK : Set G))
    (hPJc : IsClosed (PJ : Set G)) {PK MK : Subgroup G}
    (hdK : IsSemidirectDecomposition PK MK UK) (hK : ∀ x : G, x ∈ MI ↔ m⁻¹ * x * m ∈ MK)
    (hD07 : ∀ l : MI,
      (HaarModulus.closedRestrictCharacter UI hUIc MI hdI.levi_le_normalizer l : ℝ≥0) *
          (HaarModulus.closedRestrictCharacter UK hUKc MK hdK.levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection UI UK m)
            (isClosed_orbitUnipotentIntersection hUIc hUKc m) MI
            (levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK) l : ℝ≥0) ^ 2)
    [MeasurableSpace hdI.projection.ker] [BorelSpace hdI.projection.ker]
    [MeasurableSpace (orbitKernelIntersection hdI UK m)]
    [BorelSpace (orbitKernelIntersection hdI UK m)]
    {μN : Measure hdI.projection.ker} {μI : Measure (orbitKernelIntersection hdI UK m)}
    [IsHaarMeasure μN] [μN.Regular] [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (hCompatible : IsCompatible (orbitKernelIntersection hdI UK m) μN μI ν) (l : MI)
    (φ : (Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)) :
    ((HaarModulus.closedInverseHalfCharacter UI hUIc MI hdI.levi_le_normalizer l : ℂˣ) : ℂ) •
        orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν
          (((Geometric.orbitPiece.{0, uG, uV} PJ PI m).obj (orbitInducing hPJ E)).ρ
            ⟨l, hdI.levi_le l.2⟩ φ) =
      ((conjugationFunctor m hK).obj ((jacquetFunctor.{uG, uV} hdK hUKc).obj E)).representation
        l (orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ) := by
  have : LocallyCompactSpace PI := hPIc.locallyCompactSpace
  have : LocallyCompactSpace hdI.projection.ker :=
    (isClosed_projection_ker hdI hUIc).locallyCompactSpace
  have : LocallyCompactSpace (orbitKernelIntersection hdI UK m) :=
    (isClosed_orbitKernelIntersection hdI UK hUKc m).locallyCompactSpace
  let τ : Representation ℂ MI (Jacquet.Localization.Coinvariants E.representation UK 1) :=
    (Jacquet.Localization.action E.representation UK 1 MK hdK.levi_le_normalizer
      (Jacquet.Localization.isInvariant_one UK MK hdK.levi_le_normalizer)).comp
      (conjugationEquiv m hK).toMonoidHom
  have hTτ : ∀ (k : MI) (v : Jacquet.Localization.Coinvariants E.representation UJ 1),
      orbitTransition hUJK E (orbitCoefficient PI hPJ m E
        (Induction.splitKernelSection (Subgroup.inclusion hdI.levi_le)
          (Geometric.orbitStabilizer PJ PI m) (orbitLevi_mem hdI m hlevi) k) v) =
        τ k (orbitTransition hUJK E v) := by
    intro k v
    obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective E.representation UJ 1 v
    change Jacquet.Localization.mk E.representation UK 1
        (E.representation ((Geometric.stabilizerToInducing PJ PI m
          (Induction.splitKernelSection (Subgroup.inclusion hdI.levi_le)
            (Geometric.orbitStabilizer PJ PI m) (orbitLevi_mem hdI m hlevi) k) : PJ) : G) w) =
      Jacquet.Localization.mk E.representation UK 1
        (E.representation ((conjugationEquiv m hK k : MK) : G) w)
    rw [Geometric.stabilizerToInducing_apply, conjugationEquiv_apply]
    rfl
  have hsec := Induction.splitKernelValueIntegral_section hdI.projection
    (Geometric.orbitStabilizer PJ PI m) (orbitKernelIntersection hdI UK m)
    (orbitKernelIntersection_iff hdI m hUKPJ hS1) (orbitCoefficient PI hPJ m E)
    (orbitTransition hUJK E) (orbitTransition_invariant hdI hPJ hUJK m E hS1)
    (Subgroup.inclusion hdI.levi_le) (orbitLevi_mem hdI m hlevi) hdI.projection_levi hr
    (continuous_levi_inclusion hdI) (isClosed_orbitStabilizer PJ PI hPJc m)
    (orbitCoefficient_isSmooth PI hPJ m E) ν hCompatible hTτ l φ
  refine (congrArg (fun x => ((HaarModulus.closedInverseHalfCharacter UI hUIc MI
    hdI.levi_le_normalizer l : ℂˣ) : ℂ) • x) hsec).trans ?_
  have hZc := isClosed_orbitUnipotentIntersection hUIc hUKc m
  have hMZ := levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK
  have hN : mulEquivHaarChar (Induction.splitKernelConjugation hdI.projection
      (Subgroup.inclusion hdI.levi_le) l) =
      (HaarModulus.closedRestrictCharacter UI hUIc MI hdI.levi_le_normalizer l : ℝ≥0)⁻¹ := by
    rw [mulEquivHaarChar_eq_closedNormalizerCharacter UI hUIc
      ⟨(l : G)⁻¹, hdI.levi_le_normalizer (MI.inv_mem l.2)⟩ (projectionKerEquiv hdI) _
      (fun x => by simp)]
    rw [← Units.val_inv_eq_inv_val, ← map_inv]
    rfl
  have h0 : mulEquivHaarChar (subgroupAutomorphism (orbitKernelIntersection hdI UK m)
      (Induction.splitKernelConjugation hdI.projection (Subgroup.inclusion hdI.levi_le) l)
      (Induction.splitKernelValue_conjugation_mem hdI.projection
        (Geometric.orbitStabilizer PJ PI m) (orbitKernelIntersection hdI UK m)
        (orbitKernelIntersection_iff hdI m hUKPJ hS1) (Subgroup.inclusion hdI.levi_le)
        (orbitLevi_mem hdI m hlevi) l)) =
      (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection UI UK m) hZc MI hMZ l :
        ℝ≥0)⁻¹ := by
    rw [mulEquivHaarChar_eq_closedNormalizerCharacter _ hZc
      ⟨(l : G)⁻¹, hMZ (MI.inv_mem l.2)⟩ (orbitKernelIntersectionEquiv hdI UK m) _
      (fun x => by simp)]
    rw [← Units.val_inv_eq_inv_val, ← map_inv]
    rfl
  have hratio : Induction.splitKernelValueRatio hdI.projection
      (Geometric.orbitStabilizer PJ PI m) (orbitKernelIntersection hdI UK m)
      (orbitKernelIntersection_iff hdI m hUKPJ hS1) (Subgroup.inclusion hdI.levi_le)
      (orbitLevi_mem hdI m hlevi) l =
      (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection UI UK m) hZc MI hMZ l :
        ℝ≥0)⁻¹ /
        (HaarModulus.closedRestrictCharacter UI hUIc MI hdI.levi_le_normalizer l : ℝ≥0)⁻¹ := by
    rw [Induction.splitKernelValueRatio, h0, hN]
  change _ = ((HaarModulus.closedInverseHalfCharacter UK hUKc MK hdK.levi_le_normalizer
    (conjugationEquiv m hK l) : ℂˣ) : ℂ) •
      τ l (orbitJacquetMap hdI hPJ hUJK m E hUKPJ hS1 hlevi hr ν φ)
  rw [smul_smul, hratio]
  congr 1
  have hkey := congrArg (fun x : ℝ≥0 => ((x : ℝ) : ℂ))
    (inv_sqrt_mul_ratio_eq (Units.ne_zero _) (hD07 l))
  simp only [HaarModulus.closedInverseHalfCharacter, Jacquet.inverseHalfCharacter_apply]
  push_cast at hkey ⊢
  exact hkey

end Orbit

section Data

universe uI

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [T2Space G]
variable {P M U : Finset ι → Subgroup G}
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G)) (hU : Antitone U)
  (hP : Monotone P) (hPc : ∀ J, IsClosed (P J : Set G))
variable (T : Subgroup G) {Mx : CoxeterMatrix ι}
  (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
variable (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G)
  (w : Group.RelativeWeyl.Weyl T) (m : G) (K : Finset ι)
  (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)

/-- The orbit Jacquet data, built from the orbit Jacquet maps of all surviving
`J = S \ s`, for supplied Haar measures and a compatible quotient measure on
`(U_I ∩ m U_K m⁻¹) \ U_I`. -/
def orbitJacquetData
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    [MeasurableSpace (h I).projection.ker] [BorelSpace (h I).projection.ker]
    [MeasurableSpace (orbitKernelIntersection (h I) (U K) m)]
    [BorelSpace (orbitKernelIntersection (h I) (U K) m)]
    [MeasurableSpace (LeftQuotient (orbitKernelIntersection (h I) (U K) m))]
    [BorelSpace (LeftQuotient (orbitKernelIntersection (h I) (U K) m))]
    (μN : Measure (h I).projection.ker) (μI : Measure (orbitKernelIntersection (h I) (U K) m))
    [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
    [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
    (ν : Measure (LeftQuotient (orbitKernelIntersection (h I) (U K) m)))
    [IsFiniteMeasureOnCompacts ν]
    (hCompatible : IsCompatible (orbitKernelIntersection (h I) (U K) m) μN μI ν) :
    OrbitJacquetData P M U h hclosed hU T cs I E w m K hK where
  Θ s hKs hs := orbitJacquetMap (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
    ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
    (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν
  unipotent_invariant s hKs hs u φ :=
    orbitJacquetMap_unipotent (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν hCompatible.right_invariant u φ
  levi_equivariant s hKs hs l φ :=
    orbitJacquetMap_levi (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν (hPc I) (hclosed I) (hclosed K)
      (hPc _) (h K) hK hD07 hCompatible l φ
  surjective s hKs hs :=
    orbitJacquetMap_surjective (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν (hPc I) (hclosed I) (hPc _)
      μN μI hCompatible
  ker_le s hKs hs φ hφ :=
    orbitJacquetMap_ker_le (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν (hPc I) (hclosed I) (hPc _)
      (h _) (hS2 s hKs hs) μN μI hCompatible φ hφ
  transition s t hst hKs hs hKt ht φ ψ hφψ :=
    orbitJacquetMap_transition (h I) (h (Finset.univ \ s)).le_normalizer (hU hKs) m E
      ((h K).unipotent_le.trans (hP hKs)) (hS1 s hKs hs)
      (fun x hx => hP hKs ((h K).levi_le ((hK x).mp hx))) hr ν
      (h (Finset.univ \ t)).le_normalizer (hU (Finset.sdiff_subset_sdiff_right Finset.univ hst))
      (hU hKt) ((h K).unipotent_le.trans (hP hKt)) (hS1 t hKt ht)
      (fun x hx => hP hKt ((h K).levi_le ((hK x).mp hx))) φ ψ hφψ

include hP hPc in
/-- Orbit Jacquet data exist once every element of `U_I` lies in a compact open
subgroup: the Haar measures of `U_I` and `U_I ∩ m U_K m⁻¹` are then two-sided and
admit a compatible quotient measure. -/
theorem nonempty_orbitJacquetData
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    (hcover : ∀ u : U I, ∃ C : OpenSubgroup (U I), IsCompact (C : Set (U I)) ∧ u ∈ C) :
    Nonempty (OrbitJacquetData P M U h hclosed hU T cs I E w m K hK) := by
  let N := (h I).projection.ker
  let I₀ := orbitKernelIntersection (h I) (U K) m
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace I₀ := borel I₀
  have : BorelSpace I₀ := ⟨rfl⟩
  let : MeasurableSpace (LeftQuotient I₀) := borel (LeftQuotient I₀)
  have : BorelSpace (LeftQuotient I₀) := ⟨rfl⟩
  have : LocallyCompactSpace (P I) := (hPc I).locallyCompactSpace
  have : LocallyCompactSpace N := (isClosed_projection_ker (h I) (hclosed I)).locallyCompactSpace
  have hI₀ := isClosed_orbitKernelIntersection (h I) (U K) (hclosed K) m
  have : LocallyCompactSpace I₀ := hI₀.locallyCompactSpace
  let e := projectionKerEquiv (h I)
  have hcoverN : ∀ x : N, ∃ C : OpenSubgroup N, IsCompact (C : Set N) ∧ x ∈ C := by
    intro x
    obtain ⟨C, hC, hx⟩ := hcover (e x)
    exact ⟨OpenSubgroup.comap e.toMonoidHom e.continuous C,
      e.toHomeomorph.isClosedEmbedding.isCompact_preimage hC, hx⟩
  have hu := Haar.compactOpenCoverUnimodularity hcoverN
  let μN : Measure N := haar
  let μI : Measure I₀ := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 I₀ hI₀ μI
  obtain ⟨ν, hν⟩ := compatibleMeasureExists I₀ hI₀ μN μI
  have : ν.Regular := hν.regular
  exact ⟨orbitJacquetData h hclosed hU hP hPc T cs I E w m K hK hS1 hS2 hr hD07 μN μI ν hν⟩

include hP hPc in
/-- Orbit Jacquet data exist when `U_I`, as a subgroup of `P_I`, is a limit of
compact subgroups (every compact subset lies in a compact subgroup). -/
theorem nonempty_orbitJacquetData_of_isLimitOfCompactSubgroups
    (hS1 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ U I, m⁻¹ * x * m ∈ P (Finset.univ \ s) → m⁻¹ * x * m ∈ U K)
    (hS2 : ∀ s, K ⊆ Finset.univ \ s →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
      ∀ x ∈ M (Finset.univ \ s), x ∈ U K → m * x * m⁻¹ ∈ U I)
    (hr : Continuous (h I).projection)
    (hD07 : ∀ l : M I,
      (HaarModulus.closedRestrictCharacter (U I) (hclosed I) (M I) (h I).levi_le_normalizer l :
          ℝ≥0) *
          (HaarModulus.closedRestrictCharacter (U K) (hclosed K) (M K) (h K).levi_le_normalizer
            (conjugationEquiv m hK l) : ℝ≥0) =
        (HaarModulus.closedRestrictCharacter (orbitUnipotentIntersection (U I) (U K) m)
            (isClosed_orbitUnipotentIntersection (hclosed I) (hclosed K) m) (M I)
            (levi_le_normalizer_orbitUnipotentIntersection (h I) (h K) m hK) l : ℝ≥0) ^ 2)
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I))) :
    Nonempty (OrbitJacquetData P M U h hclosed hU T cs I E w m K hK) := by
  let V := (U I).subgroupOf (P I)
  have : NonarchimedeanGroup V :=
    nonarchimedeanGroup_of_isInducing ((P I).subtype.comp V.subtype)
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have : LocallyCompactSpace (P I) := (hPc I).locallyCompactSpace
  have hVc : IsClosed (V : Set (P I)) := (hclosed I).preimage continuous_subtype_val
  have : LocallyCompactSpace V := hVc.locallyCompactSpace
  let e := subgroupOfEquiv (h I).unipotent_le
  refine nonempty_orbitJacquetData h hclosed hU hP hPc T cs I E w m K hK hS1 hS2 hr hD07 ?_
  intro u
  obtain ⟨C, hC, hu⟩ := exists_compactOpen_mem_of_isLimitOfCompactSubgroups V hNc (e.symm u)
  exact ⟨OpenSubgroup.comap e.symm.toMonoidHom e.symm.continuous C,
    e.symm.toHomeomorph.isClosedEmbedding.isCompact_preimage hC, hu⟩

end Data

end Langlands.Aubert.General.CorrectedFiltration
