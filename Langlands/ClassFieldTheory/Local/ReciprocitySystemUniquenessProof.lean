import Langlands.ClassFieldTheory.Local.ReciprocitySystemStatement
import Langlands.ClassFieldTheory.Local.UnramifiedExtensionDegreeProof
import Langlands.Weil.Local.AssemblyProof
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.Uniformizer
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.ZMod

/-!
# Uniqueness of the actual common-closure reciprocity family

Two families satisfying the norm and normalization relations have the same
Galois homomorphism at every finite intermediate field: open subgroups of the
Galois abelianization are read off from norm groups, and degrees modulo every
`N` from absolute values. The Weil-to-Galois abelianization map is injective,
so the inverse Weil maps agree. The transfer, conjugation, density and
completion relations are not used.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

namespace ReciprocitySystemUniqueness

section Abstract

variable {A : Type*} [CommGroup A] [TopologicalSpace A]
  [CompactSpace A] [T2Space A] [NonarchimedeanGroup A]

/-- In a compact Hausdorff nonarchimedean abelian group, two elements are
equal if every open subgroup containing the first contains the second, and
every reduction modulo `N` with open kernel sends both to the same nonzero
integer `d`. -/
theorem eq_of_forall_openSubgroup {a₁ a₂ : A}
    (hsub : ∀ H : Subgroup A, IsOpen (H : Set A) → a₁ ∈ H → a₂ ∈ H)
    (d : ℤ) (hd : d ≠ 0)
    (hdeg : ∀ N : ℕ, N ≠ 0 → ∃ δ : A →* Multiplicative (ZMod N),
      IsOpen (δ.ker : Set A) ∧ δ a₁ = Multiplicative.ofAdd (d : ZMod N) ∧
        δ a₂ = Multiplicative.ofAdd (d : ZMod N)) :
    a₁ = a₂ := by
  by_contra hne
  have hne' : a₂ * a₁⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h).symm
  obtain ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean ({a₂ * a₁⁻¹}ᶜ : Set A)
    (isOpen_compl_singleton.mem_nhds (Ne.symm hne'))
  have hUfin : Finite (A ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  have hn0 : U.toSubgroup.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hN0 : U.toSubgroup.index * d.natAbs ≠ 0 :=
    Nat.mul_ne_zero hn0 (Int.natAbs_ne_zero.mpr hd)
  obtain ⟨δ, hδopen, hδ₁, hδ₂⟩ := hdeg _ hN0
  let D : Subgroup A := U.toSubgroup ⊓ δ.ker
  have hDopen : IsOpen (D : Set A) := U.isOpen.inter hδopen
  let H : Subgroup A := D ⊔ Subgroup.zpowers a₁
  have hHopen : IsOpen (H : Set A) := Subgroup.isOpen_mono le_sup_left hDopen
  have h₂ : a₂ ∈ H := hsub H hHopen (Subgroup.mem_sup_right (Subgroup.mem_zpowers a₁))
  obtain ⟨v, hv, z, hz, hvz⟩ := Subgroup.mem_sup.mp h₂
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hδv : δ v = 1 := hv.2
  have hcast : (((k * d - d : ℤ)) : ZMod (U.toSubgroup.index * d.natAbs)) = 0 := by
    have h := congrArg δ hvz
    rw [map_mul, map_zpow, hδv, hδ₁, hδ₂, one_mul, ← ofAdd_zsmul] at h
    have h' := Multiplicative.ofAdd.injective h
    rw [zsmul_eq_mul] at h'
    push_cast
    rw [h', sub_self]
  have hdvdN := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  have hdvd : ((U.toSubgroup.index : ℤ) * d) ∣ (k - 1) * d := by
    have h1 : ((U.toSubgroup.index * d.natAbs : ℕ) : ℤ) = |(U.toSubgroup.index : ℤ) * d| := by
      rw [abs_mul, Nat.abs_cast, Nat.cast_mul, Int.natCast_natAbs]
    rw [h1, abs_dvd] at hdvdN
    rw [sub_one_mul]
    exact hdvdN
  obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_right hd).mp hdvd
  have hmem : a₂ * a₁⁻¹ ∈ U := by
    rw [← hvz, mul_assoc, ← zpow_sub_one, hj, zpow_mul, zpow_natCast]
    exact U.toSubgroup.mul_mem hv.1
      (U.toSubgroup.zpow_mem (U.toSubgroup.pow_index_mem a₁) j)
  exact hU hmem rfl

end Abstract

section Fields

variable {K : Type u} [Field K] [PerfectField K]

/-- Every open subgroup of the abelianized fixing subgroup of `E` is cut out,
on the fixing subgroup, by the fixing subgroup of a finite extension `M ⊇ E`. -/
theorem exists_field_of_isOpen (E : FiniteIntermediateExtension K)
    (H : Subgroup (TopologicalAbelianization E.field.fixingSubgroup))
    (hH : IsOpen (H : Set (TopologicalAbelianization E.field.fixingSubgroup))) :
    ∃ (M : FiniteIntermediateExtension K) (_ : E.field ≤ M.field),
      ∀ s : E.field.fixingSubgroup,
        (QuotientGroup.mk s : TopologicalAbelianization E.field.fixingSubgroup) ∈ H ↔
          (s : Gal(AlgebraicClosure K/K)) ∈ M.field.fixingSubgroup := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let H' : Subgroup E.field.fixingSubgroup := H.comap (QuotientGroup.mk' _)
  have hH' : IsOpen (H' : Set E.field.fixingSubgroup) :=
    hH.preimage QuotientGroup.continuous_mk
  let V : Subgroup Gal(AlgebraicClosure K/K) := H'.map E.field.fixingSubgroup.subtype
  have hVopen : IsOpen (V : Set Gal(AlgebraicClosure K/K)) := by
    have h := E.field.fixingSubgroup_isOpen.isOpenMap_subtype_val _ hH'
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact h
  have hVclosed : IsClosed (V : Set Gal(AlgebraicClosure K/K)) :=
    Subgroup.isClosed_of_isOpen V hVopen
  let L := IntermediateField.fixedField V
  have hfix : L.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, hVclosed⟩
  have hfin : FiniteDimensional K L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hVopen)
  refine ⟨⟨L, hfin⟩, ?_, ?_⟩
  · change E.field ≤ IntermediateField.fixedField V
    rw [IntermediateField.le_iff_le]
    exact Subgroup.map_subtype_le H'
  · intro s
    change _ ↔ (s : Gal(AlgebraicClosure K/K)) ∈ L.fixingSubgroup
    rw [hfix]
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨t, ht, hts⟩
      have hts' : t = s := Subtype.ext hts
      subst hts'
      exact ht

omit [PerfectField K] in
/-- Fixing subgroups inherit the nonarchimedean Krull topology. -/
theorem fixingSubgroup_nonarchimedean (E : IntermediateField K (AlgebraicClosure K)) :
    NonarchimedeanGroup E.fixingSubgroup where
  is_nonarchimedean U hU := by
    rw [mem_nhds_subtype] at hU
    obtain ⟨u, hu, huU⟩ := hU
    obtain ⟨W, hW⟩ := (absoluteGaloisNonarchimedean K).is_nonarchimedean u hu
    exact ⟨W.comap E.fixingSubgroup.subtype continuous_subtype_val,
      fun x hx => huU (hW hx)⟩

/-- Fixing subgroups are closed in the compact absolute Galois group. -/
theorem fixingSubgroup_compact (E : IntermediateField K (AlgebraicClosure K)) :
    CompactSpace E.fixingSubgroup := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  exact isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed E).isCompact

variable (φ : Field.absoluteGaloisGroup K →ₜ* Weil.ProfiniteIntegers)

omit [PerfectField K] in
/-- If an open subgroup corresponds to `M`, the Galois image of an abelianized
Weil element lies in it exactly when the element comes from the Weil
abelianization of `M`. -/
theorem weilGaloisAbelianProjection_mem_iff (E M : FiniteIntermediateExtension K)
    (h : E.field ≤ M.field) (H : Subgroup (TopologicalAbelianization E.field.fixingSubgroup))
    (hM : ∀ s : E.field.fixingSubgroup,
      (QuotientGroup.mk s : TopologicalAbelianization E.field.fixingSubgroup) ∈ H ↔
        (s : Gal(AlgebraicClosure K/K)) ∈ M.field.fixingSubgroup)
    (w : TopologicalAbelianization (pullbackFixingSubgroup K E.field φ)) :
    E.weilGaloisAbelianProjection φ w ∈ H ↔
      w ∈ (E.weilAbelianInclusion M h φ).toMonoidHom.range := by
  induction w using QuotientGroup.induction_on with
  | H w₀ =>
  constructor
  · intro hw
    have hw' : Weil.projection φ w₀.1 ∈ M.field.fixingSubgroup :=
      (hM (E.weilGaloisProjection φ w₀)).mp hw
    exact ⟨QuotientGroup.mk ⟨w₀.1, hw'⟩, rfl⟩
  · rintro ⟨w', hw'⟩
    rw [← hw']
    induction w' using QuotientGroup.induction_on with
    | H w₁ => exact (hM ⟨Weil.projection φ w₁.1, IntermediateField.fixingSubgroup_antitone h w₁.2⟩).mpr w₁.2

end Fields

section Injectivity

open Topology Weil.Local
open scoped commutatorElement

/-- A dense injective continuous map with compact closed commutator remains
injective after passing to the topological abelianizations. -/
theorem abelianizationMap_injective_of_compact_commutator
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (f : G →ₜ* H) (hf : Function.Injective f) (hd : DenseRange f)
    (hc : IsCompact ((commutator G).topologicalClosure : Set G)) :
    Function.Injective (abelianizationMap f) := by
  let C := (commutator G).topologicalClosure
  let D := C.map f.toMonoidHom
  have hD : IsClosed (D : Set H) := (hc.image f.continuous).isClosed
  have hcomm : commutator H ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    apply hd.induction_on₂
      (p := fun x y : H => ⁅x, y⁆ ∈ D)
      (hD.preimage
        (((continuous_fst.mul continuous_snd).mul continuous_fst.inv).mul
          continuous_snd.inv))
    intro x y
    refine ⟨⁅x, y⁆, Subgroup.le_topologicalClosure _ ?_, ?_⟩
    · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    · exact map_commutatorElement f.toMonoidHom x y
  have hclosure : (commutator H).topologicalClosure ≤ D :=
    Subgroup.topologicalClosure_minimal _ hcomm hD
  apply (injective_iff_map_eq_one (abelianizationMap f)).mpr
  intro a
  refine QuotientGroup.induction_on a ?_
  intro x hx
  have hx' : f x ∈ (commutator H).topologicalClosure :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨y, hy, hxy⟩ := hclosure hx'
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hf hxy ▸ hy


/-- The dense local Weil projection is dense after restriction to any of
the actual open finite-intermediate-field fixing subgroups. -/
theorem weilGaloisProjection_denseRange
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) :
    DenseRange (E.weilGaloisProjection (localResidueDegree F)) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have h := (localProjection_denseRange F).preimage
    E.field.fixingSubgroup_isOpen.isOpenMap_subtype_val
  have hr : Set.range (E.weilGaloisProjection (localResidueDegree F)) =
      Subtype.val ⁻¹' Set.range (localProjection F) := by
    ext g
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, rfl⟩
    · rintro ⟨w, hw⟩
      refine ⟨⟨w, ?_⟩, ?_⟩
      · change localProjection F w ∈ E.field.fixingSubgroup
        rw [hw]
        exact g.property
      · exact Subtype.ext hw
  change Dense (Set.range (E.weilGaloisProjection (localResidueDegree F)))
  rw [hr]
  exact h

/-- The closed commutator of an actual Weil fixing subgroup is compact:
its degree is zero and it is a closed subset of the compact local inertia. -/
theorem weilFixing_closedCommutator_isCompact
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) :
    IsCompact ((commutator
      (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F))).topologicalClosure :
      Set (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F))) := by
  let W := pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)
  let i : W →ₜ* localWeilGroup F :=
    { toMonoidHom := W.subtype
      continuous_toFun := continuous_subtype_val }
  let d := (localDegree F).comp i
  have hW : IsClosed (W : Set (localWeilGroup F)) :=
    E.field.fixingSubgroup_isClosed.preimage (localProjection F).continuous
  have hc : IsCompact (d.toMonoidHom.ker : Set W) :=
    hW.isClosedEmbedding_subtypeVal.isCompact_preimage (localInertia_isCompact F)
  have hle : (commutator W).topologicalClosure ≤ d.toMonoidHom.ker :=
    Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker d.toMonoidHom)
      (isClosed_singleton.preimage d.continuous)
  exact hc.of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) hle

/-- The actual map from each Weil fixing subgroup's topological
abelianization to its Galois counterpart is injective. -/
theorem weilGaloisAbelianProjection_injective
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (E : FiniteIntermediateExtension F.Carrier) :
    Function.Injective (E.weilGaloisAbelianProjection (localResidueDegree F)) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  apply abelianizationMap_injective_of_compact_commutator
    (E.weilGaloisProjection (localResidueDegree F))
  · intro a b h
    apply Subtype.ext
    exact localProjection_injective F (congrArg Subtype.val h)
  · exact weilGaloisProjection_denseRange F E
  · exact weilFixing_closedCommutator_isCompact F E

end Injectivity

section Degree

open CategoryTheory ProfiniteGrp Langlands.ClassFieldTheory.Local

/-- Reduction of a profinite integer modulo a positive `N`, as a continuous
homomorphism to the discrete group `ℤ / N ℤ` written multiplicatively. -/
def profiniteIntegerMod (N : ℕ) [NeZero N] :
    Weil.ProfiniteIntegers →ₜ* Multiplicative (ZMod N) where
  toFun x := QuotientGroup.lift (degreeModSubgroup N).toSubgroup (degreeModHom N)
    (fun _ hx => hx) (x.val (degreeModSubgroup N))
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  continuous_toFun := by
    let Q := (ProfiniteCompletion.diagram (GrpCat.of Weil.Degree)).obj (degreeModSubgroup N)
    have : Finite Q := by
      change Finite (Weil.Degree ⧸ (degreeModHom N).ker)
      infer_instance
    have : DiscreteTopology Q := inferInstance
    exact (continuous_of_discreteTopology (f := fun q : Q =>
      QuotientGroup.lift (degreeModSubgroup N).toSubgroup (degreeModHom N)
        (fun _ hx => hx) q)).comp (profiniteModProjection N).continuous

/-- On integer Frobenius powers the reduction is reduction of the exponent. -/
theorem profiniteIntegerMod_frobenius (N : ℕ) [NeZero N] (m : Weil.Degree) :
    profiniteIntegerMod N (Weil.frobenius m) =
      Multiplicative.ofAdd ((Multiplicative.toAdd m : ℤ) : ZMod N) := rfl

variable {K : Type u} [Field K] (φ : Field.absoluteGaloisGroup K →ₜ* Weil.ProfiniteIntegers)

/-- The degree modulo `N` on the abelianized fixing subgroup of `E`, read
through `φ` on the absolute Galois group. -/
def galoisDegreeMod (E : FiniteIntermediateExtension K) (N : ℕ) [NeZero N] :
    TopologicalAbelianization E.field.fixingSubgroup →ₜ* Multiplicative (ZMod N) :=
  abelianizationLift ((profiniteIntegerMod N).comp
    (φ.comp ⟨E.field.fixingSubgroup.subtype, continuous_subtype_val⟩))

/-- On the image of the Weil abelianization, the Galois degree modulo `N`
is the reduction of the integer Weil degree. -/
theorem galoisDegreeMod_weilGaloisAbelianProjection (E : FiniteIntermediateExtension K)
    (N : ℕ) [NeZero N] (w : TopologicalAbelianization (pullbackFixingSubgroup K E.field φ)) :
    galoisDegreeMod φ E N (E.weilGaloisAbelianProjection φ w) =
      Multiplicative.ofAdd ((Multiplicative.toAdd (E.weilDegree φ w) : ℤ) : ZMod N) := by
  induction w using QuotientGroup.induction_on with
  | H w₀ =>
  obtain ⟨⟨⟨g, d⟩, hgd⟩, hE⟩ := w₀
  change profiniteIntegerMod N (φ g) = _
  rw [show φ g = Weil.frobenius d from hgd]
  rfl

end Degree

section Family

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
  {S : ∀ E : FiniteIntermediateExtension F.Carrier, (E.asPadicField (p := p)).TopologicalData}
  {φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers}

/-- Under the norm relation, the inverse candidate sends `x` into the image of
the Weil abelianization of `M` exactly when `x` is a norm from `M`. -/
theorem symm_mem_range_iff {e : CommonClosure.CandidateFamily F S φ}
    (he : CommonClosure.NormRelation F S φ e) (E M : FiniteIntermediateExtension F.Carrier)
    (h : E.field ≤ M.field) (x : E.fieldˣ) :
    letI := (S E).topology
    (e E).symm x ∈ (E.weilAbelianInclusion M h φ).toMonoidHom.range ↔
      x ∈ (E.unitsNorm M h).range := by
  let := (S E).topology
  let := (S M).topology
  have hEM := he E M h
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e M w, ?_⟩
    have h1 := DFunLike.congr_fun hEM w
    change e E ((E.weilAbelianInclusion M h φ).toMonoidHom w) =
      E.unitsNorm M h (e M w) at h1
    rw [hw, ContinuousMulEquiv.apply_symm_apply] at h1
    exact h1.symm
  · rintro ⟨y, rfl⟩
    refine ⟨(e M).symm y, ?_⟩
    have h1 := DFunLike.congr_fun hEM ((e M).symm y)
    change e E ((E.weilAbelianInclusion M h φ).toMonoidHom ((e M).symm y)) =
      E.unitsNorm M h (e M ((e M).symm y)) at h1
    rw [ContinuousMulEquiv.apply_symm_apply] at h1
    rw [← h1, ContinuousMulEquiv.symm_apply_apply]

variable (T : F.TopologicalData)

/-- Two normalized families have the same Galois image at every element whose
normalized absolute value is not `1`. -/
theorem galoisHom_eq_of_normalizedAbs_ne_one
    {e₁ e₂ : CommonClosure.CandidateFamily F S φ}
    (hN₁ : CommonClosure.NormRelation F S φ e₁) (hN₂ : CommonClosure.NormRelation F S φ e₂)
    (hA₁ : CommonClosure.NormalizationRelation F S φ T e₁)
    (hA₂ : CommonClosure.NormalizationRelation F S φ T e₂)
    (E : FiniteIntermediateExtension F.Carrier) (x : E.fieldˣ)
    (hx : (S E).normalizedAbs (x : E.field) ≠ 1) :
    CommonClosure.galoisHom F S φ e₁ E x = CommonClosure.galoisHom F S φ e₂ E x := by
  let := (S E).topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have : CompactSpace E.field.fixingSubgroup := fixingSubgroup_compact E.field
  have : NonarchimedeanGroup E.field.fixingSubgroup := fixingSubgroup_nonarchimedean E.field
  have : T2Space (TopologicalAbelianization E.field.fixingSubgroup) :=
    abelianizationHausdorff _
  have : NonarchimedeanGroup (TopologicalAbelianization E.field.fixingSubgroup) :=
    quotientNonarchimedean _
  let w₁ := (e₁ E).symm x
  let w₂ := (e₂ E).symm x
  change E.weilGaloisAbelianProjection φ w₁ = E.weilGaloisAbelianProjection φ w₂
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  have habs₁ : (S E).normalizedAbs (x : E.field) =
      (T.residueCardinality : ℝ) ^ (-Multiplicative.toAdd (E.weilDegree φ w₁)) := by
    have h := hA₁ E w₁
    rwa [ContinuousMulEquiv.apply_symm_apply] at h
  have habs₂ : (S E).normalizedAbs (x : E.field) =
      (T.residueCardinality : ℝ) ^ (-Multiplicative.toAdd (E.weilDegree φ w₂)) := by
    have h := hA₂ E w₂
    rwa [ContinuousMulEquiv.apply_symm_apply] at h
  have hd : Multiplicative.toAdd (E.weilDegree φ w₂) =
      Multiplicative.toAdd (E.weilDegree φ w₁) :=
    neg_injective (zpow_right_injective₀ (by positivity) hq.ne' (habs₂.symm.trans habs₁))
  have hd0 : Multiplicative.toAdd (E.weilDegree φ w₁) ≠ 0 := by
    intro h0
    rw [h0, neg_zero, zpow_zero] at habs₁
    exact hx habs₁
  refine eq_of_forall_openSubgroup ?_ _ hd0 ?_
  · intro H hH h₁
    obtain ⟨M, hEM, hM⟩ := exists_field_of_isOpen E H hH
    have h₁' := (weilGaloisAbelianProjection_mem_iff φ E M hEM H hM w₁).mp h₁
    exact (weilGaloisAbelianProjection_mem_iff φ E M hEM H hM w₂).mpr
      ((symm_mem_range_iff hN₂ E M hEM x).mpr ((symm_mem_range_iff hN₁ E M hEM x).mp h₁'))
  · intro N hN
    have : NeZero N := ⟨hN⟩
    refine ⟨(galoisDegreeMod φ E N).toMonoidHom, ?_, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod N)))).preimage
        (galoisDegreeMod φ E N).continuous
    · exact galoisDegreeMod_weilGaloisAbelianProjection φ E N w₁
    · rw [← hd]
      exact galoisDegreeMod_weilGaloisAbelianProjection φ E N w₂

/-- Two families satisfying the norm and normalization relations coincide as
soon as every restricted Weil-to-Galois abelianization map is injective. -/
theorem eq_of_norm_normalization
    {e₁ e₂ : CommonClosure.CandidateFamily F S φ}
    (hN₁ : CommonClosure.NormRelation F S φ e₁) (hN₂ : CommonClosure.NormRelation F S φ e₂)
    (hA₁ : CommonClosure.NormalizationRelation F S φ T e₁)
    (hA₂ : CommonClosure.NormalizationRelation F S φ T e₂)
    (hinj : ∀ E : FiniteIntermediateExtension F.Carrier,
      Function.Injective (E.weilGaloisAbelianProjection φ)) :
    e₁ = e₂ := by
  funext E
  let := (S E).topology
  have hπ : (S E).normalizedAbs
      ((LocalFactor.PadicAbelian.uniformizerUnit (S E) : E.fieldˣ) : E.field) ≠ 1 := by
    rw [LocalFactor.PadicAbelian.uniformizerUnit_coe, (S E).normalizedAbs_uniformizer]
    have hq : (1 : ℝ) < (S E).residueCardinality := by
      exact_mod_cast (S E).residueCardinality_gt_one
    intro h
    exact absurd (zpow_right_injective₀ (by positivity) hq.ne' (h.trans (zpow_zero _).symm))
      (by norm_num)
  have hgal : ∀ x : E.fieldˣ,
      CommonClosure.galoisHom F S φ e₁ E x = CommonClosure.galoisHom F S φ e₂ E x := by
    intro x
    by_cases hx : (S E).normalizedAbs (x : E.field) = 1
    · have hxπ : (S E).normalizedAbs
          ((x * LocalFactor.PadicAbelian.uniformizerUnit (S E) : E.fieldˣ) : E.field) ≠ 1 := by
        rw [Units.val_mul, (S E).normalizedAbs_mul, hx, one_mul]
        exact hπ
      have h1 := galoisHom_eq_of_normalizedAbs_ne_one T hN₁ hN₂ hA₁ hA₂ E _ hxπ
      have h2 := galoisHom_eq_of_normalizedAbs_ne_one T hN₁ hN₂ hA₁ hA₂ E _ hπ
      rw [map_mul, map_mul, h2] at h1
      exact mul_right_cancel h1
    · exact galoisHom_eq_of_normalizedAbs_ne_one T hN₁ hN₂ hA₁ hA₂ E x hx
  have hsymm : ∀ x : E.fieldˣ, (e₁ E).symm x = (e₂ E).symm x := fun x => hinj E (hgal x)
  refine ContinuousMulEquiv.ext fun w => ?_
  calc e₁ E w = e₁ E ((e₂ E).symm (e₂ E w)) := by rw [ContinuousMulEquiv.symm_apply_apply]
    _ = e₁ E ((e₁ E).symm (e₂ E w)) := by rw [hsymm]
    _ = e₂ E w := ContinuousMulEquiv.apply_symm_apply _ _

end Family

end ReciprocitySystemUniqueness

open ReciprocitySystemUniqueness in
/-- Uniqueness of the geometrically normalized reciprocity family on the actual
Weil fixing subgroups of every finite intermediate field of the common closure. -/
theorem commonClosureReciprocityUniqueness : CommonClosureReciprocityUniqueness.{u} := by
  intro p _ F T e₁ e₂ h₁ h₂
  exact eq_of_norm_normalization T h₁.1.1 h₂.1.1 h₁.2 h₂.2
    (weilGaloisAbelianProjection_injective F)

end Langlands.LocalClassField
