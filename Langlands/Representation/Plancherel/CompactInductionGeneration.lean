import Langlands.Representation.Plancherel.CompactIntertwiningCompression
import Langlands.Representation.Induction.CompactLocalSectionSpanningProof
import Langlands.Representation.Smooth.IntertwinerFiniteness
import Langlands.Representation.Jacquet.IwahoriStablePairingData

/-! # Regular generation of the unramified compact picture by translates -/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining UnramifiedOperatorFamily

universe uG uI uV

section FiniteGeneration

variable {M : Type uG} [Group M] [TopologicalSpace M]

/-- A finite-length representation is the linear span of the orbits of finitely
many vectors. -/
theorem exists_orbit_generators (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
    (hfin : A.HasFiniteLength) :
    ∃ (n : ℕ) (v : Fin n → A), ∀ u : A, u ∈ Submodule.span ℂ
      (Set.range fun x : M × Fin n => A.representation x.1 (v x.2)) := by
  have : IsNoetherian (MonoidAlgebra ℂ M) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := MonoidAlgebra ℂ M)
    (M := A.representation.asModule)
  refine ⟨n, fun i => A.representation.asModuleEquiv (v i), fun u => ?_⟩
  set S := Submodule.span ℂ
    (Set.range fun x : M × Fin n => A.representation x.1 (A.representation.asModuleEquiv (v x.2)))
  have hstable : ∀ m : M, ∀ w ∈ S, A.representation m w ∈ S := by
    intro m w hw
    have hle : S ≤ S.comap (A.representation m) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨m', i⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨m * m', i⟩, ?_⟩
      change A.representation (m * m') _ = A.representation m (A.representation m' _)
      rw [map_mul, Module.End.mul_apply]
    exact hle hw
  have halg : ∀ a : MonoidAlgebra ℂ M, ∀ w ∈ S, A.representation.asAlgebraHom a w ∈ S := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of m =>
      intro w hw
      rw [Representation.asAlgebraHom_of]
      exact hstable m w hw
    | add a b ha hb =>
      intro w hw
      rw [map_add, LinearMap.add_apply]
      exact S.add_mem (ha w hw) (hb w hw)
    | smul r a ha =>
      intro w hw
      rw [map_smul, LinearMap.smul_apply]
      exact S.smul_mem r (ha w hw)
  have key : ∀ x : A.representation.asModule, x ∈ Submodule.span (MonoidAlgebra ℂ M)
      (Set.range v) → A.representation.asModuleEquiv x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨⟨1, i⟩, by simp⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [Representation.asModuleEquiv_map_smul]
      exact halg a _ hx
  have := key (A.representation.asModuleEquiv.symm u) (by rw [hv]; exact Submodule.mem_top)
  simpa using this

end FiniteGeneration

section Translates

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- Right translation of the actual unramified induction, read on the fixed
compact picture. -/
def compactTranslate (χ : unramifiedCharacters ν) (g : G) :
    Module.End ℂ (CompactInductionPicture h K A) :=
  (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).toLinearMap ∘ₗ
    (UnramifiedLeviInduction h hU ν χ A).representation g ∘ₗ
      (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm.toLinearMap

theorem compactTranslate_mul (χ : unramifiedCharacters ν) (g g' : G) :
    compactTranslate h hU hδ K hP hK hPK ν hν hr A χ (g * g') =
      compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g *
        compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g' := by
  apply LinearMap.ext
  intro f
  simp only [compactTranslate, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.mul_apply,
    LinearEquiv.symm_apply_apply, map_mul]

theorem compactTranslate_of_mem (χ : unramifiedCharacters ν) (k : K) :
    compactTranslate h hU hδ K hP hK hPK ν hν hr A χ (k : G) = compactPictureAction h K A k := by
  apply LinearMap.ext
  intro f
  simp only [compactTranslate, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [unramifiedLeviInductionCompactEquiv_translate, LinearEquiv.apply_symm_apply]

theorem eval_compactTranslate (χ : unramifiedCharacters ν) (g : G)
    (f : CompactInductionPicture h K A) (k : K) :
    eval _ _ (compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g f) k =
      eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)
        ((k : G) * g) := by
  simp only [compactTranslate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    unramifiedLeviInductionCompactEquiv_eval]
  rfl

/-- Compact sections with one finite expansion, valid at every unramified
parameter, in parameter translates of supplied generators with coefficients in
the concrete regular algebra. -/
def regularTranslateSpan {ι : Type*} (φ : ι → CompactInductionPicture h K A) :
    Submodule ℂ (CompactInductionPicture h K A) where
  carrier := {f | ∃ (n : ℕ) (c : Fin n → unramifiedRegularFunctions ν) (g : Fin n → G)
    (j : Fin n → ι), ∀ χ : unramifiedCharacters ν,
      f = ∑ i, (c i).val χ • compactTranslate h hU hδ K hP hK hPK ν hν hr A χ (g i) (φ (j i))}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun _ => by simp⟩
  add_mem' := by
    rintro f f' ⟨n, c, g, j, hf⟩ ⟨n', c', g', j', hf'⟩
    refine ⟨n + n', Fin.addCases c c', Fin.addCases g g', Fin.addCases j j', fun χ => ?_⟩
    rw [hf χ, hf' χ, Fin.sum_univ_add]
    simp
  smul_mem' := by
    rintro a f ⟨n, c, g, j, hf⟩
    refine ⟨n, fun i => a • c i, g, j, fun χ => ?_⟩
    rw [hf χ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    rfl

/-- The regular translate span is stable under the fixed right action of `K`. -/
theorem compactPictureAction_mem_regularTranslateSpan {ι : Type*}
    (φ : ι → CompactInductionPicture h K A) (k : K) {f : CompactInductionPicture h K A}
    (hf : f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ) :
    compactPictureAction h K A k f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ := by
  obtain ⟨n, c, g, j, hf⟩ := hf
  refine ⟨n, c, fun i => (k : G) * g i, j, fun χ => ?_⟩
  rw [← compactTranslate_of_mem h hU hδ K hP hK hPK ν hν hr A χ k, hf χ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, compactTranslate_mul, Module.End.mul_apply]

/-- Generators lie in their regular translate span. -/
theorem mem_regularTranslateSpan_self {ι : Type*}
    (φ : ι → CompactInductionPicture h K A) (i : ι) :
    φ i ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => i, fun χ => ?_⟩
  simp only [Fin.sum_univ_one, OneMemClass.coe_one, Pi.one_apply, one_smul]
  simp only [compactTranslate, map_one, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.End.one_apply, LinearEquiv.apply_symm_apply]

end Translates

section Cells

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

local instance compactCellTopologicalGroup : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup K.toSubgroup)

omit [LocallyCompactSpace G] in
theorem compactCell_fixed (L : OpenSubgroup G) (v : A)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) :
    v ∈ fixedVectors (compactPictureInducingRepresentation h K A)
      (conjOpenSubgroup (P.comap K.toSubgroup.subtype)
        (L.comap K.toSubgroup.subtype continuous_subtype_val) 1).toSubgroup := by
  intro x
  have h1 := mem_conjOpenSubgroup.mp x.property
  simp only [inv_one, one_mul, mul_one] at h1
  exact hv ⟨_, x.val.property⟩ (OpenSubgroup.mem_comap.mp h1)

/-- The compact-picture section supported on `(K ∩ P) L` with value `v` at the
identity, for an open compact subgroup `L ≤ K` whose parabolic part fixes `v`. -/
def compactCell (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (v : A)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) :
    CompactInductionPicture h K A :=
  (compactDoubleCosetSection (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)
    (L.comap K.toSubgroup.subtype continuous_subtype_val)
    (K.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL) 1 v
    (compactCell_fixed h K A L v hv)).val

omit [LocallyCompactSpace G] in
theorem eval_compactCell_mul (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (v : A) (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v)
    (p : K) (hp : (p : G) ∈ P) (l : K) (hl : (l : G) ∈ L) :
    eval _ _ (compactCell h K A L hL v hv) (p * l) =
      A.representation (h.projection ⟨p, hp⟩) v := by
  have := compactDoubleCosetSection_apply (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)
    (L.comap K.toSubgroup.subtype continuous_subtype_val)
    (K.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL) 1 v
    (compactCell_fixed h K A L v hv) ⟨p, hp⟩ ⟨l, hl⟩
  simp only [mul_one] at this
  exact this

omit [LocallyCompactSpace G] in
theorem eval_compactCell_eq_zero (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (v : A) (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) (y : K)
    (hy : ∀ p : K, (p : G) ∈ P → ∀ l : K, (l : G) ∈ L → y ≠ p * l) :
    eval _ _ (compactCell h K A L hL v hv) y = 0 := by
  by_contra hne
  have hmem := compactDoubleCosetSection_support_subset (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)
    (L.comap K.toSubgroup.subtype continuous_subtype_val)
    (K.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hL) 1 v
    (compactCell_fixed h K A L v hv) ⟨y, hne, rfl⟩
  obtain ⟨l, hl, hql⟩ := hmem
  have hrel : y * (1 * l)⁻¹ ∈ P.comap K.toSubgroup.subtype :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hql)
  have hrel' : ((y * l⁻¹ : K) : G) ∈ P := by
    simp only [one_mul] at hrel
    exact Subgroup.mem_comap.mp hrel
  apply hy (y * l⁻¹) hrel' l (OpenSubgroup.mem_comap.mp hl)
  simp

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem compactPicture_ext {f f' : CompactInductionPicture h K A}
    (hff : ∀ k : K, eval _ _ f k = eval _ _ f' k) : f = f' :=
  Subtype.ext (Subtype.ext (funext hff))

/-- Evaluation of a compact section at a point of `K`, as a linear map. -/
def compactEvalLinear (k : K) : CompactInductionPicture h K A →ₗ[ℂ] A where
  toFun f := eval _ _ f k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LocallyCompactSpace G] in
/-- A cell is linear in its value. -/
theorem compactCell_finset_sum (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → A)
    (hw : ∀ i, ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) (w i) = w i)
    (hsum : ∀ p : P, (p : G) ∈ L →
      A.representation (h.projection p) (∑ i ∈ s, c i • w i) = ∑ i ∈ s, c i • w i) :
    compactCell h K A L hL (∑ i ∈ s, c i • w i) hsum =
      ∑ i ∈ s, c i • compactCell h K A L hL (w i) (hw i) := by
  apply compactPicture_ext
  intro y
  change _ = compactEvalLinear h K A y _
  rw [_root_.map_sum]
  by_cases hy : ∃ p : K, ∃ hp : (p : G) ∈ P, ∃ l : K, (l : G) ∈ L ∧ y = p * l
  · obtain ⟨p, hp, l, hl, rfl⟩ := hy
    rw [eval_compactCell_mul h K A L hL _ _ p hp l hl, _root_.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    change _ = c i • eval _ _ (compactCell h K A L hL (w i) (hw i)) (p * l)
    rw [eval_compactCell_mul h K A L hL _ _ p hp l hl]
  · push Not at hy
    rw [eval_compactCell_eq_zero h K A L hL _ _ y hy]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul]
    change c i • eval _ _ (compactCell h K A L hL (w i) (hw i)) y = 0
    rw [eval_compactCell_eq_zero h K A L hL _ _ y hy, smul_zero]

/-- The elements of an open subgroup of `K` lying in a second subgroup `L`. -/
def cellSubgroup (H : OpenSubgroup K) (L : Subgroup G) : Subgroup H where
  carrier := {x | ((x : K) : G) ∈ L}
  mul_mem' hx hy := L.mul_mem hx hy
  one_mem' := L.one_mem
  inv_mem' hx := L.inv_mem hx

omit [LocallyCompactSpace G] in
theorem finite_cellSubgroup (H : OpenSubgroup K) (hH : IsCompact (H : Set K))
    (L : OpenSubgroup G) : Finite (H ⧸ cellSubgroup K H L) := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  apply Subgroup.quotient_finite_of_isOpen
  have hc : Continuous fun x : H => ((x : K) : G) := by fun_prop
  exact L.isOpen.preimage hc

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem eval_compactPicture_smul (c : ℂ) (f : CompactInductionPicture h K A) (y : K) :
    eval _ _ (c • f) y = c • eval _ _ f y := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem eval_compactPicture_sum {ι : Type*} (s : Finset ι) (f : ι → CompactInductionPicture h K A)
    (y : K) : eval _ _ (∑ i ∈ s, f i) y = ∑ i ∈ s, eval _ _ (f i) y :=
  _root_.map_sum (compactEvalLinear h K A y) f s

omit [LocallyCompactSpace G] in
theorem eval_compactPictureAction (k : K) (f : CompactInductionPicture h K A) (y : K) :
    eval _ _ (compactPictureAction h K A k f) y = eval _ _ f (y * k) := rfl

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem eval_compactPicture_mul (f : CompactInductionPicture h K A) (p : K) (hp : (p : G) ∈ P)
    (y : K) : eval _ _ f (p * y) = A.representation (h.projection ⟨p, hp⟩) (eval _ _ f y) :=
  f.1.2 ⟨p, hp⟩ y

omit [LocallyCompactSpace G] in
/-- A compact section fixed by a subgroup of `K` is right invariant under it. -/
theorem eval_mul_of_compactFixed (H : Subgroup K) (f : CompactInductionPicture h K A)
    (hf : f ∈ fixedVectors (compactPictureAction h K A) H) (l : H) (y : K) :
    eval _ _ f (y * l) = eval _ _ f y :=
  congrArg (fun F : CompactInductionPicture h K A => eval _ _ F y) (hf l)

omit [LocallyCompactSpace G] in
theorem compactSection_fixed (H : OpenSubgroup K) (v : A)
    (hv : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H → A.representation (h.projection ⟨p, hp⟩) v = v) :
    v ∈ fixedVectors (compactPictureInducingRepresentation h K A)
      (conjOpenSubgroup (P.comap K.toSubgroup.subtype) H 1).toSubgroup := by
  intro x
  have h1 := mem_conjOpenSubgroup.mp x.property
  simp only [inv_one, one_mul, mul_one] at h1
  exact hv x.val.val x.val.property h1

/-- The compact-picture section supported on `(K ∩ P) H` with value `v` at the
identity, for a compact open subgroup `H` of `K`. -/
def compactSection (H : OpenSubgroup K) (hH : IsCompact (H : Set K)) (v : A)
    (hv : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H → A.representation (h.projection ⟨p, hp⟩) v = v) :
    CompactInductionPicture h K A :=
  (compactDoubleCosetSection (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A) H hH 1 v
    (compactSection_fixed h K A H v hv)).val

omit [LocallyCompactSpace G] in
theorem eval_compactSection_mul (H : OpenSubgroup K) (hH : IsCompact (H : Set K)) (v : A)
    (hv : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H → A.representation (h.projection ⟨p, hp⟩) v = v)
    (p : K) (hp : (p : G) ∈ P) (l : K) (hl : l ∈ H) :
    eval _ _ (compactSection h K A H hH v hv) (p * l) =
      A.representation (h.projection ⟨p, hp⟩) v := by
  have := compactDoubleCosetSection_apply (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A) H hH 1 v
    (compactSection_fixed h K A H v hv) ⟨p, hp⟩ ⟨l, hl⟩
  simp only [mul_one] at this
  exact this

omit [LocallyCompactSpace G] in
theorem eval_compactSection_eq_zero (H : OpenSubgroup K) (hH : IsCompact (H : Set K)) (v : A)
    (hv : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H → A.representation (h.projection ⟨p, hp⟩) v = v)
    (y : K) (hy : ∀ p : K, (p : G) ∈ P → ∀ l : K, l ∈ H → y ≠ p * l) :
    eval _ _ (compactSection h K A H hH v hv) y = 0 := by
  by_contra hne
  have hmem := compactDoubleCosetSection_support_subset (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A) H hH 1 v
    (compactSection_fixed h K A H v hv) ⟨y, hne, rfl⟩
  obtain ⟨l, hl, hql⟩ := hmem
  have hrel : y * (1 * l)⁻¹ ∈ P.comap K.toSubgroup.subtype :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hql)
  have hrel' : ((y * l⁻¹ : K) : G) ∈ P := by
    simp only [one_mul] at hrel
    exact Subgroup.mem_comap.mp hrel
  apply hy (y * l⁻¹) hrel' l hl
  simp

omit [LocallyCompactSpace G] in
/-- Averaging a cell over a larger compact open subgroup of `K` gives a nonzero
multiple of the corresponding section. Hence every submodule stable under `K`
that contains the smaller cell contains the larger section. -/
theorem compactSection_mem_of_le (S : Submodule ℂ (CompactInductionPicture h K A))
    (hS : ∀ k : K, ∀ f ∈ S, compactPictureAction h K A k f ∈ S)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (H : OpenSubgroup K)
    (hH : IsCompact (H : Set K)) (hle : ∀ l : K, (l : G) ∈ L → l ∈ H) (u : A)
    (hu : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H → A.representation (h.projection ⟨p, hp⟩) u = u)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) u = u)
    (hmem : compactCell h K A L hL u hv ∈ S) :
    compactSection h K A H hH u hu ∈ S := by
  classical
  set ψ := compactCell h K A L hL u hv with hψdef
  let L' := cellSubgroup K H L
  let := finite_cellSubgroup K H hH L
  let := Fintype.ofFinite (H ⧸ L')
  have hρ := smoothInduced_smooth (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)
  have hfix : ∀ l : L', compactPictureAction h K A ((l : H) : K) ψ = ψ := by
    intro l
    apply compactPicture_ext
    intro y
    rw [eval_compactPictureAction]
    exact compactDoubleCosetSection_mul _ _ _ _ 1 u _ ⟨((l : H) : K), l.property⟩ y
  have havg := averageMap_eq_finiteMean_cosets (compactPictureAction h K A) hρ H hH L' ψ hfix
  set avg := Compact.averageMap (compactPictureAction h K A) hρ H hH ψ with havgdef
  have havgS : avg ∈ S := by
    rw [havg]
    unfold Compact.finiteMean
    exact S.smul_mem _ (S.sum_mem fun q _ => hS _ _ hmem)
  have hval : ∀ y : K, eval _ _ avg y = (Fintype.card (H ⧸ L') : ℂ)⁻¹ •
      ∑ q : H ⧸ L', eval _ _ ψ (y * ((q.out : H) : K)) := by
    intro y
    rw [havg]
    unfold Compact.finiteMean
    rw [eval_compactPicture_smul, eval_compactPicture_sum]
    rfl
  let C : H ⧸ L' → Prop := fun q =>
    ∃ p : K, (p : G) ∈ P ∧ ∃ l : K, (l : G) ∈ L ∧ ((q.out : H) : K) = p * l
  have hψval : ∀ q : H ⧸ L', eval _ _ ψ ((q.out : H) : K) = (if C q then (1 : ℂ) else 0) • u := by
    intro q
    by_cases hq : C q
    · simp only [hq, ↓reduceIte, one_smul]
      obtain ⟨p, hp, l, hl, hpl⟩ := hq
      rw [hpl, hψdef, eval_compactCell_mul h K A L hL _ _ p hp l hl]
      apply hu
      have : p = ((q.out : H) : K) * l⁻¹ := by rw [hpl]; simp
      rw [this]
      exact H.mul_mem (q.out : H).property (H.inv_mem (hle l hl))
    · simp only [hq, ↓reduceIte, zero_smul]
      rw [hψdef]
      apply eval_compactCell_eq_zero
      intro p hp l hl hpl
      exact hq ⟨p, hp, l, hl, hpl⟩
  set c : ℂ := (Fintype.card (H ⧸ L') : ℂ)⁻¹ *
    ((Finset.univ.filter C).card : ℂ) with hcdef
  have hval1 : eval _ _ avg 1 = c • u := by
    rw [hval 1]
    simp only [one_mul]
    rw [Finset.sum_congr rfl fun q _ => hψval q, ← Finset.sum_smul, Finset.sum_boole, smul_smul]
  have hc : c ≠ 0 := by
    apply mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨(QuotientGroup.mk (1 : H) : H ⧸ L'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hout : ((QuotientGroup.mk (1 : H) : H ⧸ L').out : H) ∈ L' := by
      obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L' (1 : H)
      rw [hl, one_mul]
      exact l.property
    exact ⟨1, P.one_mem, ((QuotientGroup.mk (1 : H) : H ⧸ L').out : H), hout, (one_mul _).symm⟩
  have heq : avg = c • compactSection h K A H hH u hu := by
    apply compactPicture_ext
    intro y
    change eval _ _ avg y = c • eval _ _ (compactSection h K A H hH u hu) y
    by_cases hy : ∃ p : K, ∃ hp : (p : G) ∈ P, ∃ l : K, l ∈ H ∧ y = p * l
    · obtain ⟨p, hp, l, hl, rfl⟩ := hy
      rw [eval_compactSection_mul h K A H hH u hu p hp l hl,
        eval_compactPicture_mul h K A avg p hp l]
      have hinv : eval _ _ avg l = eval _ _ avg 1 := by
        have := eval_mul_of_compactFixed h K A H.toSubgroup avg
          (Compact.averageMap_mem_fixedVectors _ hρ H hH ψ) ⟨l, hl⟩ 1
        simpa using this
      rw [hinv, hval1, map_smul]
    · push Not at hy
      rw [eval_compactSection_eq_zero h K A H hH u hu y hy, smul_zero, hval y]
      rw [Finset.sum_eq_zero, smul_zero]
      intro q _
      rw [hψdef]
      apply eval_compactCell_eq_zero
      intro p hp l hl hpl
      apply hy p hp (l * ((q.out : H) : K)⁻¹)
      · exact H.mul_mem (hle l hl) (H.inv_mem (q.out : H).property)
      · rw [← mul_assoc, ← hpl]
        simp
  have : compactSection h K A H hH u hu = c⁻¹ • avg := by
    rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this]
  exact S.smul_mem _ havgS

omit [LocallyCompactSpace G] in
theorem compactCell_congr (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) {v v' : A}
    (hvv : v = v') (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v)
    (hv' : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v' = v') :
    compactCell h K A L hL v hv = compactCell h K A L hL v' hv' := by
  subst hvv
  rfl

omit [LocallyCompactSpace G] in
/-- A cell is fixed by `L ∩ K`, hence by `L` when `L ≤ K`. -/
theorem compactCell_mem_compactFixed (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (v : A)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) :
    compactCell h K A L hL v hv ∈ CompactFixedVectors h K A L := by
  intro x
  apply compactPicture_ext
  intro y
  exact compactDoubleCosetSection_mul _ _ _ _ 1 v _ ⟨(x : K), x.property⟩ y

omit [LocallyCompactSpace G] in
/-- The averaging step for two compact open subgroups of `G`. -/
theorem compactCell_mem_of_le (S : Submodule ℂ (CompactInductionPicture h K A))
    (hS : ∀ k : K, ∀ f ∈ S, compactPictureAction h K A k f ∈ S)
    (L Lbig : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLbig : IsCompact (Lbig : Set G))
    (hle : (L : Subgroup G) ≤ Lbig) (u : A)
    (hu : ∀ p : P, (p : G) ∈ Lbig → A.representation (h.projection p) u = u)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) u = u)
    (hmem : compactCell h K A L hL u hv ∈ S) :
    compactCell h K A Lbig hLbig u hu ∈ S :=
  compactSection_mem_of_le h K A S hS L hL (Lbig.comap K.toSubgroup.subtype continuous_subtype_val)
    (K.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hLbig) (fun _ hl => hle hl) u
    (fun p hp hpH => hu ⟨p, hp⟩ hpH) hv hmem

end Cells

section Factorization

variable {G : Type uG} [Group G]

/-- Iwahori factorization of a subgroup in the order: upper radical, Levi,
opposite radical. -/
def IsCellFactorized (U M Ubar L : Subgroup G) : Prop :=
  ∀ x ∈ L, ∃ u ∈ L ⊓ U, ∃ m ∈ L ⊓ M, ∃ n ∈ L ⊓ Ubar, x = u * m * n

variable {P M U Ubar L : Subgroup G} (h : IsSemidirectDecomposition P M U)

include h in
/-- Under `P ∩ Ubar = 1`, the Levi projection of an element of `P ∩ L` lies in `L`. -/
theorem IsCellFactorized.projection_mem (hL : IsCellFactorized U M Ubar L)
    (hPU : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1) (p : P) (hp : (p : G) ∈ L) :
    ((h.projection p : M) : G) ∈ L := by
  obtain ⟨u, hu, m, hm, n, hn, hpe⟩ := hL _ hp
  have hn1 : n = 1 := by
    apply hPU n _ hn.2
    have : n = (u * m)⁻¹ * (p : G) := by rw [hpe]; group
    rw [this]
    exact P.mul_mem (P.inv_mem (P.mul_mem (h.unipotent_le hu.2) (h.levi_le hm.2))) p.property
  have hproj : h.projection p = ⟨m, hm.2⟩ := by
    rw [h.projection_eq_iff]
    rw [hpe, hn1, mul_one]
    change m⁻¹ * (u * m) ∈ U
    have := h.levi_le_normalizer (M.inv_mem hm.2)
    have hmem := (Subgroup.mem_normalizer_iff.mp this u).mp hu.2
    simpa [mul_assoc] using hmem
  rw [hproj]
  exact hm.1

include h in
/-- The radical and the Levi subgroup intersect trivially. -/
theorem eq_one_of_mem_radical_of_mem_levi {x : G} (hxU : x ∈ U) (hxM : x ∈ M) : x = 1 := by
  have h1 := (h.projection_eq_one_iff ⟨x, h.unipotent_le hxU⟩).mpr hxU
  have h2 := h.projection_levi ⟨x, hxM⟩
  have h3 : (⟨x, h.unipotent_le hxU⟩ : P) = ⟨(⟨x, hxM⟩ : M), h.levi_le hxM⟩ := rfl
  rw [h3, h2] at h1
  exact congrArg Subtype.val h1

include h in
/-- Uniqueness of the factorization `U · M · Ubar` when `P ∩ Ubar = 1`. -/
theorem factor_unique (hPU : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1) {u u' m m' n n' : G}
    (hu : u ∈ U) (hu' : u' ∈ U) (hm : m ∈ M) (hm' : m' ∈ M) (hn : n ∈ Ubar) (hn' : n' ∈ Ubar)
    (he : u * m * n = u' * m' * n') : u = u' ∧ m = m' ∧ n = n' := by
  have h1 : n' * n⁻¹ = (u' * m')⁻¹ * (u * m) := by
    have : u * m = u' * m' * n' * n⁻¹ := by rw [← he]; group
    rw [this]
    group
  have hnn : n' * n⁻¹ = 1 := by
    apply hPU
    · rw [h1]
      exact P.mul_mem (P.inv_mem (P.mul_mem (h.unipotent_le hu') (h.levi_le hm')))
        (P.mul_mem (h.unipotent_le hu) (h.levi_le hm))
    · exact Ubar.mul_mem hn' (Ubar.inv_mem hn)
  have hn_eq : n = n' := by
    rw [mul_inv_eq_one] at hnn
    exact hnn.symm
  subst hn_eq
  have hum : u * m = u' * m' := mul_right_cancel he
  have h2 : u'⁻¹ * u = m' * m⁻¹ := by
    have : u = u' * m' * m⁻¹ := by rw [← hum]; group
    rw [this]
    group
  have h3 : u'⁻¹ * u = 1 :=
    eq_one_of_mem_radical_of_mem_levi h (U.mul_mem (U.inv_mem hu') hu)
      (h2 ▸ M.mul_mem hm' (M.inv_mem hm))
  have hu_eq : u = u' := by
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  subst hu_eq
  exact ⟨rfl, mul_left_cancel hum, rfl⟩

include h in
/-- Intersection with the conjugate of a second factorized subgroup by a Levi
element preserves factorization. -/
theorem IsCellFactorized.inf_conj (hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G))
    (hPU : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1) {L₀ L' : Subgroup G}
    (h₀ : IsCellFactorized U M Ubar L₀) (h' : IsCellFactorized U M Ubar L') {a : G}
    (ha : a ∈ M) :
    IsCellFactorized U M Ubar (L' ⊓ L₀.comap (MulAut.conj a).toMonoidHom) := by
  intro x hx
  obtain ⟨hxL', hxL₀⟩ := hx
  have hxL₀' : a * x * a⁻¹ ∈ L₀ := by simpa using hxL₀
  obtain ⟨u, hu, m, hm, n, hn, rfl⟩ := h' x hxL'
  obtain ⟨u', hu', m', hm', n', hn', he⟩ := h₀ _ hxL₀'
  have hcu : a * u * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (h.levi_le_normalizer ha) u).mp hu.2
  have hcm : a * m * a⁻¹ ∈ M := M.mul_mem (M.mul_mem ha hm.2) (M.inv_mem ha)
  have hcn : a * n * a⁻¹ ∈ Ubar := (Subgroup.mem_normalizer_iff.mp (hMUbar ha) n).mp hn.2
  have he' : (a * u * a⁻¹) * (a * m * a⁻¹) * (a * n * a⁻¹) = u' * m' * n' := by
    rw [← he]
    group
  obtain ⟨e1, e2, e3⟩ := factor_unique h hPU hcu hu'.2 hcm hm'.2 hcn hn'.2 he'
  refine ⟨u, ⟨⟨hu.1, ?_⟩, hu.2⟩, m, ⟨⟨hm.1, ?_⟩, hm.2⟩, n, ⟨⟨hn.1, ?_⟩, hn.2⟩, rfl⟩
  · simpa [e1] using hu'.1
  · simpa [e2] using hm'.1
  · simpa [e3] using hn'.1

/-- Conjugation by a Levi element preserves factorization. -/
theorem IsCellFactorized.conj (hUM : M ≤ Subgroup.normalizer (U : Set G))
    (hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G)) {L : Subgroup G}
    (hL : IsCellFactorized U M Ubar L) {a : G} (ha : a ∈ M) :
    IsCellFactorized U M Ubar (L.comap (MulAut.conj a).toMonoidHom) := by
  intro x hx
  have hx' : a * x * a⁻¹ ∈ L := by simpa using hx
  obtain ⟨u, hu, m, hm, n, hn, he⟩ := hL _ hx'
  have hai : a⁻¹ ∈ M := M.inv_mem ha
  refine ⟨a⁻¹ * u * a, ⟨?_, ?_⟩, a⁻¹ * m * a, ⟨?_, ?_⟩, a⁻¹ * n * a, ⟨?_, ?_⟩, ?_⟩
  · simpa [mul_assoc] using hu.1
  · simpa using (Subgroup.mem_normalizer_iff.mp (hUM hai) u).mp hu.2
  · simpa [mul_assoc] using hm.1
  · exact M.mul_mem (M.mul_mem hai hm.2) ha
  · simpa [mul_assoc] using hn.1
  · simpa using (Subgroup.mem_normalizer_iff.mp (hMUbar hai) n).mp hn.2
  · have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [this, he]
    group

end Factorization

section CellTranslates

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) {Ubar : Subgroup G}

/-- The scalar of the actual normalized twisted inducing action at `p ∈ P`. -/
def inductionScalar (χ : unramifiedCharacters ν) (p : P) : ℂ :=
  (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) *
    (χ.val (h.projection p) : ℂ)

theorem inductionScalar_mul (χ : unramifiedCharacters ν) (p q : P) :
    inductionScalar h hU ν χ (p * q) = inductionScalar h hU ν χ p * inductionScalar h hU ν χ q := by
  simp only [inductionScalar, map_mul, Units.val_mul]
  ring

include hP hK hν hr in
theorem inductionScalar_of_mem (χ : unramifiedCharacters ν) (p : P) (hp : (p : G) ∈ K) :
    inductionScalar h hU ν χ p = 1 := by
  have hp' : p ∈ conjOpenSubgroup P K 1 := by
    apply mem_conjOpenSubgroup.mpr
    simpa using hp
  rw [inductionScalar, HaarModulus.closedHalfCharacter_eq_one_of_mem_compactOpen U P hU
    h.le_normalizer hP K hK hp,
    unramifiedPullback_eq_one_of_mem_conjOpenSubgroup P hP ν hν h.projection hr χ K hK 1 hp']
  simp

/-- The actual covariance extension of a compact section at `p k`. -/
theorem extension_eval_mul (χ : unramifiedCharacters ν) (f : CompactInductionPicture h K A)
    (p : P) (k : K) :
    eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)
      ((p : G) * (k : G)) =
      inductionScalar h hU ν χ p • A.representation (h.projection p) (eval _ _ f k) := by
  rw [unramifiedLeviInductionCompactEquiv_symm_mul, inductionScalar, mul_smul]
  rfl

omit [LocallyCompactSpace G] in
/-- On a factorized subgroup of `K`, membership of a point of `K` in the cell
support only depends on the opposite-radical part. -/
theorem eval_compactCell_eq_zero_of_factorized (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hLK : (L : Subgroup G) ≤ K) (hfac : IsCellFactorized U M Ubar L) (v : A)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) (y : K)
    (hy : ∀ p : K, (p : G) ∈ P → ∀ n : K, (n : G) ∈ (L : Subgroup G) ⊓ Ubar → y ≠ p * n) :
    eval _ _ (compactCell h K A L hL v hv) y = 0 := by
  apply eval_compactCell_eq_zero h K A L hL v hv y
  intro p hp l hl hyl
  obtain ⟨u, hu, m, hm, n, hn, hl'⟩ := hfac _ hl
  have humK : u * m ∈ K := K.mul_mem (hLK hu.1) (hLK hm.1)
  apply hy (p * ⟨u * m, humK⟩) (P.mul_mem hp (P.mul_mem (h.unipotent_le hu.2) (h.levi_le hm.2)))
    ⟨n, hLK hn.1⟩ hn
  apply Subtype.ext
  simp [hyl, hl', mul_assoc]

/-- The actual extension of a cell on the opposite-radical part. -/
theorem extension_compactCell_mul (χ : unramifiedCharacters ν) (L : OpenSubgroup G)
    (hL : IsCompact (L : Set G)) (hLK : (L : Subgroup G) ≤ K) (v : A)
    (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) (p : P) (n : G)
    (hn : n ∈ L) :
    eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm
      (compactCell h K A L hL v hv)) ((p : G) * n) =
      inductionScalar h hU ν χ p • A.representation (h.projection p) v := by
  have := extension_eval_mul h hU hδ K hP hK hPK ν hν hr A χ (compactCell h K A L hL v hv) p
    ⟨n, hLK hn⟩
  rw [this]
  congr 2
  have h1 := eval_compactCell_mul h K A L hL v hv 1 (P.one_mem) ⟨n, hLK hn⟩ hn
  simp only [one_mul] at h1
  rw [h1]
  have : (⟨((1 : K) : G), P.one_mem⟩ : P) = 1 := rfl
  rw [this, map_one, map_one, Module.End.one_apply]

/-- The actual extension of a cell vanishes off `P (L ∩ Ubar)`. -/
theorem extension_compactCell_eq_zero (χ : unramifiedCharacters ν) (L : OpenSubgroup G)
    (hL : IsCompact (L : Set G)) (hLK : (L : Subgroup G) ≤ K) (hfac : IsCellFactorized U M Ubar L)
    (v : A) (hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) v = v) (x : G)
    (hx : ∀ p : P, ∀ n ∈ (L : Subgroup G) ⊓ Ubar, x ≠ (p : G) * n) :
    eval _ _ ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm
      (compactCell h K A L hL v hv)) x = 0 := by
  obtain ⟨p, k, rfl⟩ := hPK x
  rw [extension_eval_mul, eval_compactCell_eq_zero_of_factorized h K A L hL hLK hfac v hv k ?_]
  · rw [map_zero, smul_zero]
    rfl
  intro p' hp' n hn hk
  apply hx (p * ⟨p', hp'⟩) n hn
  rw [hk]
  simp [mul_assoc]

/-- Right translation by a Levi element carries a cell to a cell with the
conjugated opposite-radical part, up to the actual inducing scalar. -/
theorem compactTranslate_compactCell (χ : unramifiedCharacters ν) (m : M)
    (La Lb : OpenSubgroup G) (hLa : IsCompact (La : Set G)) (hLb : IsCompact (Lb : Set G))
    (hLaK : (La : Subgroup G) ≤ K) (hLbK : (Lb : Subgroup G) ≤ K)
    (hfa : IsCellFactorized U M Ubar La) (hfb : IsCellFactorized U M Ubar Lb)
    (hN : ∀ n : G, n ∈ (Lb : Subgroup G) ⊓ Ubar ↔ (m : G)⁻¹ * n * m ∈ (La : Subgroup G) ⊓ Ubar)
    (w : A) (hwa : ∀ p : P, (p : G) ∈ La → A.representation (h.projection p) w = w)
    (hwb : ∀ p : P, (p : G) ∈ Lb →
      A.representation (h.projection p) (A.representation m w) = A.representation m w) :
    compactTranslate h hU hδ K hP hK hPK ν hν hr A χ (m : G) (compactCell h K A La hLa w hwa) =
      inductionScalar h hU ν χ ⟨m, h.levi_le m.2⟩ •
        compactCell h K A Lb hLb (A.representation m w) hwb := by
  apply compactPicture_ext
  intro y
  rw [eval_compactTranslate]
  change _ = inductionScalar h hU ν χ ⟨m, h.levi_le m.2⟩ •
    eval _ _ (compactCell h K A Lb hLb (A.representation m w) hwb) y
  by_cases hy : ∃ p : K, ∃ hp : (p : G) ∈ P, ∃ n : K,
      (n : G) ∈ (Lb : Subgroup G) ⊓ Ubar ∧ y = p * n
  · obtain ⟨p, hp, n, hn, rfl⟩ := hy
    have hn' := (hN n).mp hn
    have e : ((p * n : K) : G) * (m : G) =
        ((⟨p, hp⟩ * ⟨m, h.levi_le m.2⟩ : P) : G) * ((m : G)⁻¹ * n * m) := by
      simp [mul_assoc]
    rw [e, extension_compactCell_mul h hU hδ K hP hK hPK ν hν hr A χ La hLa hLaK w hwa _ _ hn'.1,
      eval_compactCell_mul h K A Lb hLb _ _ p hp n hn.1, inductionScalar_mul,
      inductionScalar_of_mem h hU K hP hK ν hν hr χ ⟨p, hp⟩ p.property, one_mul, map_mul,
      h.projection_levi, map_mul, Module.End.mul_apply]
  · push Not at hy
    rw [extension_compactCell_eq_zero h hU hδ K hP hK hPK ν hν hr A χ La hLa hLaK hfa w hwa _ ?_,
      eval_compactCell_eq_zero_of_factorized h K A Lb hLb hLbK hfb _ _ y hy, smul_zero]
    · rfl
    intro p n hn hyn
    have hn'' : (m : G) * n * (m : G)⁻¹ ∈ (Lb : Subgroup G) ⊓ Ubar := by
      apply (hN _).mpr
      simpa [mul_assoc] using hn
    have hy' : (y : G) = (p : G) * (m : G)⁻¹ * ((m : G) * n * (m : G)⁻¹) := by
      have : (y : G) = (y : G) * m * (m : G)⁻¹ := by group
      rw [this, hyn]
      group
    have hK' : (p : G) * (m : G)⁻¹ ∈ K := by
      have : (p : G) * (m : G)⁻¹ = (y : G) * ((m : G) * n * (m : G)⁻¹)⁻¹ := by
        rw [hy']
        group
      rw [this]
      exact K.mul_mem y.property (K.inv_mem (hLbK hn''.1))
    apply hy ⟨_, hK'⟩ (P.mul_mem p.property (P.inv_mem (h.levi_le m.2)))
      ⟨_, hLbK hn''.1⟩ hn''
    apply Subtype.ext
    simpa [mul_assoc] using hy'

end CellTranslates

section Generation

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M) {Ubar : Subgroup G}

/-- The regular function `χ ↦ δ^{1/2}(m) χ(m)` of the actual inducing scalar. -/
def inductionScalarRegular (m : M) : unramifiedRegularFunctions ν :=
  (HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨m, h.levi_le m.2⟩ : ℂ) •
    unramifiedEvaluationRegular ν m

theorem inductionScalarRegular_apply (m : M) (χ : unramifiedCharacters ν) :
    (inductionScalarRegular h hU ν m).val χ = inductionScalar h hU ν χ ⟨m, h.levi_le m.2⟩ := by
  simp only [inductionScalarRegular, inductionScalar, h.projection_levi]
  rfl

theorem inductionScalar_inv_mul (χ : unramifiedCharacters ν) (m : M) :
    inductionScalar h hU ν χ ⟨((m⁻¹ : M) : G), h.levi_le (m⁻¹).2⟩ *
      inductionScalar h hU ν χ ⟨(m : G), h.levi_le m.2⟩ = 1 := by
  rw [← inductionScalar_mul]
  have : (⟨((m⁻¹ : M) : G), h.levi_le (m⁻¹).2⟩ * ⟨(m : G), h.levi_le m.2⟩ : P) = 1 := by
    apply Subtype.ext
    simp
  rw [this]
  simp [inductionScalar]

/-- A regular multiple of a parameter translate of a member stays in the span. -/
theorem mem_regularTranslateSpan_of_translate {ι : Type*}
    (φ : ι → CompactInductionPicture h K A) {f F : CompactInductionPicture h K A}
    (hf : f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ)
    (r : unramifiedRegularFunctions ν) (g : G)
    (hF : ∀ χ : unramifiedCharacters ν,
      F = r.val χ • compactTranslate h hU hδ K hP hK hPK ν hν hr A χ g f) :
    F ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ := by
  obtain ⟨n, c, g', j, hf⟩ := hf
  refine ⟨n, fun i => r * c i, fun i => g * g' i, j, fun χ => ?_⟩
  rw [hF χ, hf χ, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_smul, compactTranslate_mul, Module.End.mul_apply]
  rfl

/-- The fixed compact sections used as generators. -/
abbrev fixedGenerators (L₀ : OpenSubgroup G) :
    CompactFixedVectors h K A L₀ → CompactInductionPicture h K A :=
  fun w => w.val

theorem regularTranslateSpan_stable {ι : Type*} (φ : ι → CompactInductionPicture h K A) :
    ∀ k : K, ∀ f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ,
      compactPictureAction h K A k f ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ :=
  fun k _ hf => compactPictureAction_mem_regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A φ k hf

variable (hMUbar : M ≤ Subgroup.normalizer (Ubar : Set G))
  (hPUbar : ∀ x : G, x ∈ P → x ∈ Ubar → x = 1)

include hMUbar hPUbar in
/-- Contraction step: a cell on a factorized subgroup of `L₀` with an
`L₀`-fixed value is a regular combination of parameter translates of fixed
generators. -/
theorem compactCell_mem_of_contraction (L₀ : OpenSubgroup G) (hL₀ : IsCompact (L₀ : Set G))
    (hL₀K : (L₀ : Subgroup G) ≤ K) (hf₀ : IsCellFactorized U M Ubar L₀)
    (g : G) (hg : Jacquet.IsIwahoriContraction L₀ U M Ubar g)
    (L' : OpenSubgroup G) (hL' : IsCompact (L' : Set G)) (hL'₀ : (L' : Subgroup G) ≤ L₀)
    (hf' : IsCellFactorized U M Ubar L') (v : A)
    (hv₀ : ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) v = v)
    (hv : ∀ p : P, (p : G) ∈ L' → A.representation (h.projection p) v = v) :
    compactCell h K A L' hL' v hv ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L₀) := by
  obtain ⟨s, hs⟩ := hg.contract L'
  have haM : g ^ s ∈ M := M.pow_mem hg.mem_levi s
  let L₃ : OpenSubgroup G := L' ⊓ L₀.comap (MulAut.conj (g ^ s)).toMonoidHom
    (IsTopologicalGroup.continuous_conj (g ^ s))
  have hL₃' : (L₃ : Subgroup G) ≤ L' := fun x hx => hx.1
  have hL₃ : IsCompact (L₃ : Set G) := hL'.of_isClosed_subset L₃.isClosed hL₃'
  have hL₃K : (L₃ : Subgroup G) ≤ K := fun x hx => hL₀K (hL'₀ hx.1)
  have hf₃ : IsCellFactorized U M Ubar L₃ :=
    IsCellFactorized.inf_conj h hMUbar hPUbar hf₀ hf' haM
  let a : M := ⟨g ^ s, haM⟩
  let m : M := a⁻¹
  let w : A := A.representation a v
  have hw₀ : ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) w = w := by
    intro p hp
    have hpm := IsCellFactorized.projection_mem h hf₀ hPUbar p hp
    have hc : ((a : G))⁻¹ * ((h.projection p : M) : G) * (a : G) ∈ (L₀ : Subgroup G) ⊓ M :=
      hg.levi_pow s _ ⟨hpm, (h.projection p).2⟩
    have hfix := hv₀ ⟨_, h.levi_le hc.2⟩ hc.1
    rw [show (⟨_, h.levi_le hc.2⟩ : P) = ⟨(⟨_, hc.2⟩ : M), h.levi_le hc.2⟩ from rfl,
      h.projection_levi] at hfix
    have e : h.projection p * a = a * ⟨_, hc.2⟩ := by
      apply Subtype.ext
      simp [a, mul_assoc]
    change A.representation (h.projection p) (A.representation a v) = A.representation a v
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfix]
  have hmw : A.representation m w = v := by
    change A.representation a⁻¹ (A.representation a v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hwb : ∀ p : P, (p : G) ∈ L₃ →
      A.representation (h.projection p) (A.representation m w) = A.representation m w := by
    rw [hmw]
    exact fun p hp => hv p hp.1
  have hN : ∀ n : G, n ∈ (L₃ : Subgroup G) ⊓ Ubar ↔
      (m : G)⁻¹ * n * m ∈ (L₀ : Subgroup G) ⊓ Ubar := by
    intro n
    have em : (m : G)⁻¹ * n * m = g ^ s * n * (g ^ s)⁻¹ := by simp [m, a]
    rw [em]
    constructor
    · rintro ⟨⟨_, hn₀⟩, hn⟩
      have hn₀' : g ^ s * n * (g ^ s)⁻¹ ∈ L₀ := hn₀
      exact ⟨hn₀', (Subgroup.mem_normalizer_iff.mp (hMUbar haM) n).mp hn⟩
    · rintro ⟨hn₀, hn⟩
      have hnU : n ∈ Ubar := by
        have := (Subgroup.mem_normalizer_iff.mp (hMUbar (M.inv_mem haM)) _).mp hn
        simpa [mul_assoc] using this
      have hnL' : n ∈ L' := by
        have := hs _ ⟨hn₀, hn⟩
        simpa [mul_assoc] using this
      exact ⟨⟨hnL', hn₀⟩, hnU⟩
  have hgen : compactCell h K A L₀ hL₀ w hw₀ ∈ regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A
      (fixedGenerators h K A L₀) :=
    mem_regularTranslateSpan_self h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀)
      ⟨_, compactCell_mem_compactFixed h K A L₀ hL₀ w hw₀⟩
  have h3 : compactCell h K A L₃ hL₃ v (fun p hp => hv p (hL₃' hp)) ∈
      regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) := by
    apply mem_regularTranslateSpan_of_translate h hU hδ K hP hK hPK ν hν hr A _ hgen
      (inductionScalarRegular h hU ν m⁻¹) (m : G)
    intro χ
    rw [compactTranslate_compactCell h hU hδ K hP hK hPK ν hν hr A χ m L₀ L₃ hL₀ hL₃ hL₀K hL₃K
      hf₀ hf₃ hN w hw₀ hwb, smul_smul, inductionScalarRegular_apply]
    have := inductionScalar_inv_mul h hU ν χ m
    rw [this, one_smul]
    exact compactCell_congr h K A L₃ hL₃ hmw.symm _ _
  exact compactCell_mem_of_le h K A _ (regularTranslateSpan_stable h hU hδ K hP hK hPK ν hν hr A _)
    L₃ L' hL₃ hL' hL₃' v hv _ h3

include hMUbar hPUbar in
/-- Levi step: the cell on `L` with value `A(m) v` is a regular multiple of the
parameter translate by `m` of the cell on `m⁻¹ L m ⊆ L₀` with value `v`. -/
theorem compactCell_mem_of_levi (L₀ : OpenSubgroup G) (hL₀ : IsCompact (L₀ : Set G))
    (hL₀K : (L₀ : Subgroup G) ≤ K) (hf₀ : IsCellFactorized U M Ubar L₀)
    (g : G) (hg : Jacquet.IsIwahoriContraction L₀ U M Ubar g)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK : (L : Subgroup G) ≤ K)
    (hfL : IsCellFactorized U M Ubar L) (m : M)
    (hmL : ∀ x ∈ (L : Subgroup G), (m : G)⁻¹ * x * m ∈ L₀) (v : A)
    (hv₀ : ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) v = v)
    (hv : ∀ p : P, (p : G) ∈ L →
      A.representation (h.projection p) (A.representation m v) = A.representation m v) :
    compactCell h K A L hL (A.representation m v) hv ∈
      regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) := by
  let La : OpenSubgroup G := L.comap (MulAut.conj (m : G)).toMonoidHom
    (IsTopologicalGroup.continuous_conj (m : G))
  have hmemLa : ∀ x : G, x ∈ La ↔ (m : G) * x * (m : G)⁻¹ ∈ L := fun x => Iff.rfl
  have hLa₀ : (La : Subgroup G) ≤ L₀ := by
    intro x hx
    have := hmL _ ((hmemLa x).mp hx)
    simpa [mul_assoc] using this
  have hLa : IsCompact (La : Set G) := hL₀.of_isClosed_subset La.isClosed hLa₀
  have hfa : IsCellFactorized U M Ubar La :=
    IsCellFactorized.conj h.levi_le_normalizer hMUbar hfL m.2
  have hva : ∀ p : P, (p : G) ∈ La → A.representation (h.projection p) v = v :=
    fun p hp => hv₀ p (hLa₀ hp)
  have hca := compactCell_mem_of_contraction h hU hδ K hP hK hPK ν hν hr A hMUbar hPUbar
    L₀ hL₀ hL₀K hf₀ g hg La hLa hLa₀ hfa v hv₀ hva
  have hN : ∀ n : G, n ∈ (L : Subgroup G) ⊓ Ubar ↔
      (m : G)⁻¹ * n * m ∈ (La : Subgroup G) ⊓ Ubar := by
    intro n
    constructor
    · rintro ⟨hnL, hn⟩
      refine ⟨(hmemLa _).mpr (by simpa [mul_assoc] using hnL), ?_⟩
      simpa using (Subgroup.mem_normalizer_iff.mp (hMUbar (M.inv_mem m.2)) n).mp hn
    · rintro ⟨hnLa, hn⟩
      refine ⟨by simpa [mul_assoc] using (hmemLa _).mp hnLa, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hMUbar m.2) _).mp hn
      simpa [mul_assoc] using this
  apply mem_regularTranslateSpan_of_translate h hU hδ K hP hK hPK ν hν hr A _ hca
    (inductionScalarRegular h hU ν m⁻¹) (m : G)
  intro χ
  rw [compactTranslate_compactCell h hU hδ K hP hK hPK ν hν hr A χ m La L hLa hL
    (fun x hx => hL₀K (hLa₀ hx)) hLK hfa hfL hN v hva hv, smul_smul,
    inductionScalarRegular_apply, inductionScalar_inv_mul, one_smul]

include hMUbar hPUbar in
/-- Every cell on a factorized subgroup of `K` lies in the regular translate span
of `L₀`-fixed sections, when finitely many `L₀ ∩ M`-fixed vectors generate `A`. -/
theorem compactCell_mem_of_factorized (L₀ : OpenSubgroup G) (hL₀ : IsCompact (L₀ : Set G))
    (hL₀K : (L₀ : Subgroup G) ≤ K) (hf₀ : IsCellFactorized U M Ubar L₀)
    (g : G) (hg : Jacquet.IsIwahoriContraction L₀ U M Ubar g)
    {J : Type*} (v : J → A)
    (hgen : ∀ u : A, u ∈ Submodule.span ℂ
      (Set.range fun x : M × J => A.representation x.1 (v x.2)))
    (hvL₀ : ∀ j, ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) (v j) = v j)
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ (L : Set G) ⊆ O ∧
        IsCellFactorized U M Ubar L)
    (L : OpenSubgroup G) (hL : IsCompact (L : Set G)) (hLK : (L : Subgroup G) ≤ K)
    (u : A) (hu : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) u = u) :
    compactCell h K A L hL u hu ∈
      regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hgen u)
  let O : Set G := (L : Set G) ∩ ⋂ x ∈ c.support, {y | ((x.1 : M) : G)⁻¹ * y * x.1 ∈ L₀}
  have hO : IsOpen O := by
    refine L.isOpen.inter (isOpen_biInter_finset fun x _ => ?_)
    exact L₀.isOpen.preimage (by fun_prop)
  have h1 : (1 : G) ∈ O := by
    refine ⟨L.one_mem, Set.mem_iInter₂.mpr fun x _ => ?_⟩
    simp
  obtain ⟨L'', hL''c, hL''O, hf''⟩ := hbasis O hO h1
  have hL''L : (L'' : Subgroup G) ≤ L := fun y hy => (hL''O hy).1
  have hconj : ∀ x ∈ c.support, ∀ y ∈ (L'' : Subgroup G), ((x.1 : M) : G)⁻¹ * y * x.1 ∈ L₀ :=
    fun x hx y hy => Set.mem_iInter₂.mp (hL''O hy).2 x hx
  have hfix : ∀ x : c.support, ∀ p : P, (p : G) ∈ L'' →
      A.representation (h.projection p) (A.representation x.1.1 (v x.1.2)) =
        A.representation x.1.1 (v x.1.2) := by
    intro x p hp
    have hpm := IsCellFactorized.projection_mem h hf'' hPUbar p hp
    have hc' := hconj x.1 x.2 _ hpm
    have hcM : ((x.1.1 : M) : G)⁻¹ * ((h.projection p : M) : G) * (x.1.1 : M) ∈ M :=
      M.mul_mem (M.mul_mem (M.inv_mem x.1.1.2) (h.projection p).2) x.1.1.2
    have hfx := hvL₀ x.1.2 ⟨_, h.levi_le hcM⟩ hc'
    rw [show (⟨_, h.levi_le hcM⟩ : P) = ⟨(⟨_, hcM⟩ : M), h.levi_le hcM⟩ from rfl,
      h.projection_levi] at hfx
    have e : h.projection p * x.1.1 = x.1.1 * ⟨_, hcM⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hfx]
  have hu_eq : u = ∑ x : c.support, c x • A.representation x.1.1 (v x.1.2) := by
    rw [← hc, Finsupp.sum, ← Finset.sum_coe_sort]
  have hsum : ∀ p : P, (p : G) ∈ L'' → A.representation (h.projection p)
      (∑ x : c.support, c x • A.representation x.1.1 (v x.1.2)) =
        ∑ x : c.support, c x • A.representation x.1.1 (v x.1.2) := by
    intro p hp
    rw [← hu_eq]
    exact hu p (hL''L hp)
  have hcell : compactCell h K A L'' hL''c u (fun p hp => hu p (hL''L hp)) ∈
      regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) := by
    rw [compactCell_congr h K A L'' hL''c hu_eq _ hsum,
      compactCell_finset_sum h K A L'' hL''c Finset.univ (fun x : c.support => c x)
        (fun x => A.representation x.1.1 (v x.1.2)) hfix hsum]
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    exact compactCell_mem_of_levi h hU hδ K hP hK hPK ν hν hr A hMUbar hPUbar L₀ hL₀ hL₀K hf₀
      g hg L'' hL''c (fun y hy => hLK (hL''L hy)) hf'' x.1.1 (hconj x.1 x.2) (v x.1.2)
      (hvL₀ x.1.2) (hfix x)
  exact compactCell_mem_of_le h K A _ (regularTranslateSpan_stable h hU hδ K hP hK hPK ν hν hr A _)
    L'' L hL''c hL hL''L u hu _ hcell

include hMUbar hPUbar in
/-- Regular generation: every compact section is a finite combination, valid at
every unramified parameter, of parameter translates of `L₀`-fixed sections with
coefficients in the concrete regular algebra. -/
theorem regularTranslateSpan_eq_top [T2Space G] (L₀ : OpenSubgroup G)
    (hL₀ : IsCompact (L₀ : Set G))
    (hL₀K : (L₀ : Subgroup G) ≤ K) (hf₀ : IsCellFactorized U M Ubar L₀)
    (g : G) (hg : Jacquet.IsIwahoriContraction L₀ U M Ubar g)
    {J : Type*} (v : J → A)
    (hgen : ∀ u : A, u ∈ Submodule.span ℂ
      (Set.range fun x : M × J => A.representation x.1 (v x.2)))
    (hvL₀ : ∀ j, ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) (v j) = v j)
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ (L : Set G) ⊆ O ∧
        IsCellFactorized U M Ubar L) :
    regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) = ⊤ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  set S := regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀)
  -- compact sections of `K`
  have hsec : ∀ (H : OpenSubgroup K) (hH : IsCompact (H : Set K)) (w : A)
      (hw : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H →
        A.representation (h.projection ⟨p, hp⟩) w = w),
      compactSection h K A H hH w hw ∈ S := by
    intro H hH w hw
    have hOopen : IsOpen ((K.toSubgroup.subtype : K → G) '' (H : Set K)) :=
      K.isOpen.isOpenMap_subtype_val _ H.isOpen
    obtain ⟨L, hLc, hLO, hfL⟩ := hbasis _ hOopen ⟨1, H.one_mem, rfl⟩
    have hLK : (L : Subgroup G) ≤ K := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := hLO hx
      exact y.property
    have hLH : ∀ l : K, (l : G) ∈ L → l ∈ H := by
      intro l hl
      obtain ⟨y, hy, hyl⟩ := hLO hl
      have : y = l := Subtype.ext hyl
      rwa [← this]
    have hv : ∀ p : P, (p : G) ∈ L → A.representation (h.projection p) w = w :=
      fun p hp => hw ⟨p, hLK hp⟩ p.property (hLH ⟨p, hLK hp⟩ hp)
    exact compactSection_mem_of_le h K A S (regularTranslateSpan_stable h hU hδ K hP hK hPK ν hν
      hr A _) L hLc H hH hLH w hw hv
      (compactCell_mem_of_factorized h hU hδ K hP hK hPK ν hν hr A hMUbar hPUbar L₀ hL₀ hL₀K hf₀
        g hg v hgen hvL₀ hbasis L hLc hLK w hv)
  -- the published spanning theorem on `K`
  have hbK : ∀ O : Set K, IsOpen O → (1 : K) ∈ O →
      ∃ L : OpenSubgroup K, IsCompact (L : Set K) ∧ (L : Set K) ⊆ O := by
    intro O hO h1
    have hOG : (K.toSubgroup.subtype : K → G) '' O ∈ 𝓝 (1 : G) :=
      (K.isOpen.isOpenMap_subtype_val _ hO).mem_nhds ⟨1, h1, rfl⟩
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ hOG
    refine ⟨V.comap K.toSubgroup.subtype continuous_subtype_val,
      (V.comap K.toSubgroup.subtype continuous_subtype_val).isClosed.isCompact, ?_⟩
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hV hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hPK' : IsClosed ((P.comap K.toSubgroup.subtype : Subgroup K) : Set K) :=
    hP.preimage continuous_subtype_val
  have hspan := compactLocalSectionSpanning K hbK (P.comap K.toSubgroup.subtype) hPK' A
    (compactPictureInducingRepresentation h K A)
  have hbij := compactInclusion_bijective_of_compactSpace (P.comap K.toSubgroup.subtype)
    (compactPictureInducingRepresentation h K A)
  apply eq_top_iff.mpr
  intro f _
  obtain ⟨f', rfl⟩ := hbij.2 f
  have hle : (⊤ : Submodule ℂ (CompactFunctions (P.comap K.toSubgroup.subtype)
      (compactPictureInducingRepresentation h K A))) ≤
      S.comap (compactInclusion (P.comap K.toSubgroup.subtype)
        (compactPictureInducingRepresentation h K A)).toLinearMap := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, H, hH, w, hw, rfl⟩
    have hw' : ∀ p : K, ∀ hp : (p : G) ∈ P, p ∈ H →
        A.representation (h.projection ⟨p, hp⟩) w = w := by
      intro p hp hpH
      exact hw ⟨⟨p, hp⟩, mem_conjOpenSubgroup.mpr (by simpa using hpH)⟩
    exact regularTranslateSpan_stable h hU hδ K hP hK hPK ν hν hr A _ k _ (hsec H hH w hw')
  exact hle (Submodule.mem_top : f' ∈ (⊤ : Submodule ℂ _))

include hMUbar hPUbar in
/-- Existence form of regular generation: for a finite-length inducing
representation and an opposite Iwahori contraction basis, there is a compact
open `L₀ ⊆ O ∩ K` whose fixed sections generate the compact picture regularly. -/
theorem exists_regularTranslateSpan_eq_top [T2Space G] (g : G)
    (hbasis : Jacquet.HasOppositeIwahoriContractionBasis U M Ubar g)
    (hfin : A.HasFiniteLength) (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ L₀ : OpenSubgroup G, IsCompact (L₀ : Set G) ∧ (L₀ : Set G) ⊆ O ∧
      (L₀ : Subgroup G) ≤ K ∧
        regularTranslateSpan h hU hδ K hP hK hPK ν hν hr A (fixedGenerators h K A L₀) = ⊤ := by
  obtain ⟨n, v, hgen⟩ := exists_orbit_generators A hfin
  choose Mj hMj using fun j => A.isSmooth (v j)
  choose t ht using fun j => isOpen_induced_iff.mp (Mj j).isOpen
  let O' : Set G := O ∩ (K : Set G) ∩ ⋂ j, t j
  have hO' : IsOpen O' :=
    (hO.inter K.isOpen).inter (isOpen_iInter_of_finite fun j => (ht j).1)
  have h1' : (1 : G) ∈ O' := by
    refine ⟨⟨h1, K.one_mem⟩, Set.mem_iInter.mpr fun j => ?_⟩
    have : (1 : M) ∈ (Mj j : Set M) := (Mj j).one_mem
    rw [← (ht j).2] at this
    exact this
  obtain ⟨L₀, hL₀c, hL₀O, hc1, hc2⟩ := hbasis O' hO' h1'
  have hL₀K : (L₀ : Subgroup G) ≤ K := fun x hx => (hL₀O hx).1.2
  have hf₀ : IsCellFactorized U M Ubar L₀ := fun x hx => hc2.factor x hx
  have hvL₀ : ∀ j, ∀ p : P, (p : G) ∈ L₀ → A.representation (h.projection p) (v j) = v j := by
    intro j p hp
    have hpm := IsCellFactorized.projection_mem h hf₀ hPUbar p hp
    have ht' : (h.projection p : M) ∈ (Mj j : Set M) := by
      rw [← (ht j).2]
      exact Set.mem_iInter.mp (hL₀O hpm).2 j
    exact hMj j ⟨_, ht'⟩
  have hbasis' : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ (L : Set G) ⊆ O ∧
        IsCellFactorized U M Ubar L := by
    intro O hO h1
    obtain ⟨L, hLc, hLO, _, hL2⟩ := hbasis O hO h1
    exact ⟨L, hLc, hLO, fun x hx => hL2.factor x hx⟩
  exact ⟨L₀, hL₀c, fun x hx => (hL₀O hx).1.1, hL₀K,
    regularTranslateSpan_eq_top h hU hδ K hP hK hPK ν hν hr A hMUbar hPUbar L₀ hL₀c hL₀K hf₀ g
      hc1 v hgen hvL₀ hbasis'⟩

end Generation


end Langlands.Plancherel
