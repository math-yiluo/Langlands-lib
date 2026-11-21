import Langlands.Galois.ClosureRestriction
import Langlands.Galois.QuadraticPatchingStatement
import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.Representation.Category.FiniteIndexSemisimplicity
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.IndexNormal

/-! # Quadratic patching of continuous semisimple Galois representations -/

noncomputable section

open scoped Topology

namespace Langlands.GaloisRepresentation

namespace QuadraticPatching

universe uF uC uV

variable {F : Type uF} [Field F]

private abbrev FiniteField (F : Type uF) [Field F] :=
  FiniteGaloisIntermediateField F (AlgebraicClosure F)

private abbrev Γ (F : Type uF) [Field F] := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F

private abbrev fixing (E : FiniteField F) : Subgroup (Γ F) := E.toIntermediateField.fixingSubgroup

private instance fixing_normal [CharZero F] (E : FiniteField F) : (fixing E).Normal :=
  (InfiniteGalois.normal_iff_isGalois E.toIntermediateField).2 inferInstance

private theorem fixing_open (E : FiniteField F) : IsOpen (fixing E : Set (Γ F)) :=
  E.toIntermediateField.fixingSubgroup_isOpen

private theorem fixing_antitone : Antitone (fixing (F := F)) :=
  fun _ _ h => IntermediateField.fixingSubgroup_antitone h

private theorem fixing_sup (E L : FiniteField F) : fixing (E ⊔ L) = fixing E ⊓ fixing L :=
  IntermediateField.fixingSubgroup_sup

private theorem fixing_bot : fixing (⊥ : FiniteField F) = ⊤ :=
  IntermediateField.fixingSubgroup_bot

private theorem fixing_index [CharZero F] (E : FiniteField F) :
    (fixing E).index = Module.finrank F E :=
  (IntermediateField.finrank_eq_fixingSubgroup_index
    (AlgebraicClosure F) E.toIntermediateField).symm

private theorem fixing_sup_eq_top [CharZero F] {E L : FiniteField F} (h : E ⊓ L = ⊥) :
    fixing E ⊔ fixing L = ⊤ := by
  let H := fixing E ⊔ fixing L
  have hH : IsClosed (H : Set (Γ F)) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_left (fixing_open E))
  have hEL : E.toIntermediateField ⊓ L.toIntermediateField = ⊥ :=
    congrArg FiniteGaloisIntermediateField.toIntermediateField h
  have hfixed : IntermediateField.fixedField H = ⊥ := by
    apply le_bot_iff.mp
    rw [← hEL]
    exact le_inf
      ((IntermediateField.fixedField_antitone (show fixing E ≤ H from le_sup_left)).trans_eq
        (InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField))
      ((IntermediateField.fixedField_antitone (show fixing L ≤ H from le_sup_right)).trans_eq
        (InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField))
  have hfix := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩
  change (IntermediateField.fixedField H).fixingSubgroup = H at hfix
  rw [hfixed, IntermediateField.fixingSubgroup_bot] at hfix
  exact hfix.symm

section Span

variable {C : Type uC} [Field C] {D : Type*} [Ring D] [Algebra C D]
variable {G : Type*} [Group G] {H : Subgroup G}

/-- The linear span of the action on elements of `H` that belong to `K`. -/
private def actionSpan (r : H →* D) (K : Subgroup G) : Submodule C D :=
  Submodule.span C (r '' {h : H | (h : G) ∈ K})

private theorem actionSpan_le (r : H →* D) {K L : Subgroup G} (h : K ≤ L) :
    actionSpan (C := C) r K ≤ actionSpan (C := C) r L :=
  Submodule.span_mono (Set.image_mono fun _ hx => h hx)

private theorem action_mem_span (r : H →* D) {K : Subgroup G} {h : H} (hh : (h : G) ∈ K) :
    r h ∈ actionSpan (C := C) r K :=
  Submodule.subset_span ⟨h, hh, rfl⟩

private theorem actionSpan_full (r : H →* D) {U K : Subgroup G} [U.Normal]
    (hUH : U ≤ H) (hKU : K ⊔ U = ⊤)
    (hspan : actionSpan (C := C) r (K ⊓ U) = actionSpan (C := C) r U) :
    actionSpan (C := C) r K = actionSpan (C := C) r H := by
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨g, _, rfl⟩
    exact ⟨g, g.property, rfl⟩
  rintro _ ⟨g, _, rfl⟩
  have hg : (g : G) ∈ K ⊔ U := hKU ▸ Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have haH : a ∈ H := by
    have := H.mul_mem g.property (H.inv_mem (hUH hb))
    simpa [← hab] using this
  let aH : H := ⟨a, haH⟩
  let bH : H := ⟨b, hUH hb⟩
  have habH : aH * bH = g := Subtype.ext hab
  have hleft : ∀ d ∈ actionSpan (C := C) r (K ⊓ U), r aH * d ∈ actionSpan (C := C) r K := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [← map_mul]
      exact action_mem_span r (K.mul_mem ha hj.1)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  rw [← habH, map_mul]
  exact hleft _ (hspan.symm ▸ action_mem_span r hb)

/-- The minimum-dimensional span persists on every deeper finite Galois subgroup. -/
private theorem exists_stable_span [FiniteDimensional C D] (L : FiniteField F)
    (r : fixing L →* D) :
    ∃ M : FiniteField F, L ≤ M ∧ ∀ N : FiniteField F, M ≤ N →
      actionSpan (C := C) r (fixing N) = actionSpan (C := C) r (fixing M) := by
  classical
  let d (M : FiniteField F) := Module.finrank C (actionSpan (C := C) r (fixing M))
  have hex : ∃ n : ℕ, ∃ M : FiniteField F, L ≤ M ∧ d M = n := ⟨d L, L, le_rfl, rfl⟩
  obtain ⟨M, hLM, hd⟩ := Nat.find_spec hex
  refine ⟨M, hLM, fun N hMN => Submodule.eq_of_le_of_finrank_le
    (actionSpan_le r (fixing_antitone hMN)) ?_⟩
  change d M ≤ d N
  rw [hd]
  exact Nat.find_min' hex ⟨N, hLM.trans hMN, rfl⟩

private theorem actionSpan_full_of_independent [CharZero F] (L : FiniteField F)
    (r : fixing L →* D)
    {M : FiniteField F} (hLM : L ≤ M)
    (hM : ∀ N : FiniteField F, M ≤ N →
      actionSpan (C := C) r (fixing N) = actionSpan (C := C) r (fixing M))
    {N : FiniteField F} (hK : fixing N ⊔ fixing M = ⊤) :
    actionSpan (C := C) r (fixing N) = actionSpan (C := C) r (fixing L) := by
  apply actionSpan_full r (fixing_antitone hLM) hK
  rw [← fixing_sup]
  exact hM _ le_sup_right

/-- A linear identity that holds on the smaller span holds on every action in
the larger span. -/
private theorem linear_eq_of_actionSpan {P : Type*} [AddCommGroup P] [Module C P]
    (r : H →* D) {K : Subgroup G}
    (hspan : actionSpan (C := C) r K = actionSpan (C := C) r H)
    {f g : D →ₗ[C] P} (hfg : ∀ h : H, (h : G) ∈ K → f (r h) = g (r h))
    (h : H) : f (r h) = g (r h) := by
  apply LinearMap.eqOn_span (s := r '' {h : H | (h : G) ∈ K})
  · rintro _ ⟨a, ha, rfl⟩
    exact hfg a ha
  · change r h ∈ actionSpan (C := C) r K
    rw [hspan]
    exact action_mem_span r h.property

end Span

section Extension

variable {G : Type*} [Group G] {H K L : Subgroup G}
variable {C : Type uC} [Field C]
variable {V W : Type*} [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W]

private theorem inf_sup_eq_top [H.Normal] [K.Normal]
    (hHK : K ⊔ H = ⊤) (hL : L ⊔ (H ⊓ K) = ⊤) : (K ⊓ L) ⊔ H = ⊤ := by
  apply top_unique
  intro g _
  have hg : g ∈ K ⊔ H := hHK ▸ Subgroup.mem_top _
  obtain ⟨k, hk, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hk' : k ∈ L ⊔ (H ⊓ K) := hL ▸ Subgroup.mem_top _
  obtain ⟨l, hl, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hk'
  have hlK : l ∈ K := (K.mul_mem_cancel_right ha.2).mp hk
  rw [mul_assoc]
  exact Subgroup.mul_mem _
    ((show K ⊓ L ≤ (K ⊓ L) ⊔ H from le_sup_left) ⟨hlK, hl⟩)
    ((show H ≤ (K ⊓ L) ⊔ H from le_sup_right) (H.mul_mem ha.1 hh))

private theorem mul_inv_mem_of_notMem {t g : G} (hidx : H.index = 2)
    (ht : t ∉ H) (hg : g ∉ H) : g * t⁻¹ ∈ H := by
  rw [Subgroup.mul_mem_iff_of_index_two hidx, H.inv_mem_iff]
  exact iff_of_false hg ht

/-- Extend from an index-two subgroup by prescribing the action of one element
of the other coset. The two relations are conjugation and the square relation. -/
private def quadraticExtend [H.Normal] (r : Representation C H V) {t : G} (hidx : H.index = 2)
    (ht : t ∉ H) (T : Module.End C V)
    (hconj : ∀ h : H, T * r h = r (MulAut.conjNormal t h) * T)
    (hsq : T * T = r ⟨t * t, Subgroup.mul_self_mem_of_index_two hidx t⟩) :
    Representation C G V := by
  classical
  let rep (g : G) : Module.End C V :=
    if hg : g ∈ H then r ⟨g, hg⟩ else r ⟨g * t⁻¹, mul_inv_mem_of_notMem hidx ht hg⟩ * T
  have inside (h : H) : rep h = r h := dite_eq_left h.property
  have outside (h : H) : rep ((h : G) * t) = r h * T := by
    have hn : (h : G) * t ∉ H := mt (H.mul_mem_cancel_left h.property).mp ht
    simp only [rep, dite_eq_right hn, mul_inv_cancel_right]
  refine { toFun := rep, map_one' := (inside 1).trans r.map_one, map_mul' := ?_ }
  have cases_coset (g : G) : (∃ h : H, g = h.val) ∨ (∃ h : H, g = h.val * t) := by
    by_cases hg : g ∈ H
    · exact Or.inl ⟨⟨g, hg⟩, rfl⟩
    · exact Or.inr ⟨⟨g * t⁻¹, mul_inv_mem_of_notMem hidx ht hg⟩, (inv_mul_cancel_right _ _).symm⟩
  intro a b
  rcases cases_coset a with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases cases_coset b with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · change rep ((a * b : H) : G) = _
    rw [inside, inside, inside, map_mul]
  · rw [show (a : G) * ((b : G) * t) = ((a * b : H) : G) * t from (mul_assoc _ _ _).symm,
      outside, inside, outside, map_mul, mul_assoc]
  · have hab : ((a : G) * t) * b = ((a * MulAut.conjNormal t b : H) : G) * t := by
      change _ = (a : G) * (t * (b : G) * t⁻¹) * t
      simp [mul_assoc]
    rw [hab, outside, outside, inside, map_mul, mul_assoc, ← hconj, mul_assoc]
  · let q : H := ⟨t * t, Subgroup.mul_self_mem_of_index_two hidx t⟩
    have hab : ((a : G) * t) * ((b : G) * t) = ((a * MulAut.conjNormal t b * q : H) : G) := by
      change _ = (a : G) * (t * (b : G) * t⁻¹) * (t * t)
      simp [mul_assoc]
    rw [hab, inside, outside, outside, map_mul, map_mul]
    calc
      r a * r (MulAut.conjNormal t b) * r q =
          r a * (r (MulAut.conjNormal t b) * T) * T := by rw [← hsq]; simp [mul_assoc]
      _ = (r a * T) * (r b * T) := by rw [← hconj]; simp [mul_assoc]

private theorem quadraticExtend_on [H.Normal] (r : Representation C H V) {t : G} (hidx : H.index = 2)
    (ht : t ∉ H) (T : Module.End C V) (hconj) (hsq) (h : H) :
    quadraticExtend r hidx ht T hconj hsq h = r h :=
  dite_eq_left h.property

private theorem quadraticExtend_off [H.Normal] (r : Representation C H V) {t : G}
    (hidx : H.index = 2)
    (ht : t ∉ H) (T : Module.End C V) (hconj) (hsq) {g : G} (hg : g ∉ H) :
    quadraticExtend r hidx ht T hconj hsq g =
      r ⟨g * t⁻¹, mul_inv_mem_of_notMem hidx ht hg⟩ * T :=
  dite_eq_right hg

private theorem continuous_of_open_restriction [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace C] [IsTopologicalRing C] [FiniteDimensional C V]
    (hH : IsOpen (H : Set G)) (r : Representation C G V)
    (hr : letI := moduleTopology C (Module.End C V); Continuous (r.comp H.subtype)) :
    letI := moduleTopology C (Module.End C V); Continuous r := by
  let := moduleTopology C (Module.End C V)
  let : IsModuleTopology C (Module.End C V) := ⟨rfl⟩
  let : IsTopologicalRing (Module.End C V) := IsModuleTopology.isTopologicalRing C _
  apply continuous_of_continuousAt_one r
  exact (continuousOn_iff_continuous_domRestrict.mpr hr).continuousAt
    (hH.mem_nhds H.one_mem)

private theorem semisimple_comp_of_surjective {G' : Type*} [Monoid G']
    (r : Representation C G' V) (f : G →* G') (hf : Function.Surjective f)
    (hr : Representation.IsSemisimpleRepresentation r) :
    Representation.IsSemisimpleRepresentation (r.comp f) := by
  refine ⟨fun X => ?_⟩
  let Y : Subrepresentation r := ⟨X.toSubmodule, fun g x hx => by
    obtain ⟨a, rfl⟩ := hf g
    exact X.apply_mem_toSubmodule a hx⟩
  obtain ⟨Z, hZ⟩ := exists_isCompl Y
  let Z' : Subrepresentation (r.comp f) :=
    ⟨Z.toSubmodule, fun g _ hx => Z.apply_mem_toSubmodule (f g) hx⟩
  have hcompl : IsCompl Y.toSubmodule Z.toSubmodule :=
    FiniteIndexSemisimplicity.isCompl_toSubmodule hZ
  exact ⟨Z', FiniteIndexSemisimplicity.isCompl_of_isCompl_toSubmodule hcompl⟩

/-- Conjugating the action by an invertible linear map supplies an intertwiner. -/
private def equivOfConj {G' : Type*} [Monoid G']
    (r : Representation C G' V) (s : Representation C G' W)
    (e : V ≃ₗ[C] W) (he : ∀ g, e.conj (r g) = s g) : r.Equiv s :=
  Representation.Equiv.mk e fun g => by
    ext v
    simpa [LinearEquiv.conj_apply_apply] using LinearMap.congr_fun (he g) (e v)

/-- An intertwiner on two subgroups also intertwines the action of their join. -/
private def equivOfSup [H.Normal] (r : Representation C G V) (s : Representation C G W)
    (e : V ≃ₗ[C] W) (hHK : H ⊔ K = ⊤)
    (hH : ∀ h : H, e.conj (r h) = s h)
    (hK : ∀ k : K, e.conj (r k) = s k) : r.Equiv s := by
  refine equivOfConj r s e fun g => ?_
  have hg : g ∈ K ⊔ H := (sup_comm H K ▸ hHK) ▸ Subgroup.mem_top _
  obtain ⟨k, hk, h, hh, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  change e.conjRingEquiv (r (k * h)) = s (k * h)
  simp only [map_mul]
  exact congrArg₂ (· * ·) (hK ⟨k, hk⟩) (hH ⟨h, hh⟩)

/-- An intertwining equation is linear in the pair of actions. -/
private def equivOfPairSpan (r : Representation C H V) (s : Representation C H W)
    (e : V ≃ₗ[C] W)
    (hspan : actionSpan (C := C) (MonoidHom.prod r s) K = actionSpan (C := C) (MonoidHom.prod r s) H)
    (he : ∀ h : H, (h : G) ∈ K → e.conj (r h) = s h) : r.Equiv s :=
  equivOfConj r s e
    (linear_eq_of_actionSpan (MonoidHom.prod r s) hspan
      (f := e.conj.toLinearMap.comp (LinearMap.fst C (Module.End C V) (Module.End C W)))
      (g := LinearMap.snd C (Module.End C V) (Module.End C W)) he)

/-- Use the second subgroup to choose the cyclic intertwiner for the first. -/
private theorem exists_common_extension [H.Normal] (hidx : H.index = 2)
    (r : Representation C H V) (s : Representation C K W)
    (hHK : H ⊔ K = ⊤)
    (hspan : actionSpan (C := C) r K = actionSpan (C := C) r H)
    (hinv : ∀ t : G, Nonempty (r.Equiv (r.comp (MulAut.conjNormal t).toMonoidHom)))
    (e : V ≃ₗ[C] W)
    (he : ∀ g : ↥(H ⊓ K), e.conj (r ⟨g, g.property.1⟩) = s ⟨g, g.property.2⟩) :
    ∃ a : Representation C G V, a.comp H.subtype = r ∧
      Nonempty (Representation.Equiv (a.comp K.subtype) s) := by
  have hex : ∃ t : K, (t : G) ∉ H := by
    by_contra! h
    have htop : H = ⊤ := (sup_eq_left.mpr (fun x hx => h ⟨x, hx⟩)).symm.trans hHK
    simp [htop] at hidx
  obtain ⟨t, ht⟩ := hex
  let s' := e.symm.conjRingEquiv.toMonoidHom.comp s
  have transport (k : K) : e.conj (s' k) = s k := e.conj.apply_symm_apply (s k)
  have hagree (h : H) (hk : (h : G) ∈ K) : r h = s' ⟨h, hk⟩ := by
    apply e.conj.injective
    rw [transport]
    exact he ⟨h, h.property, hk⟩
  let T := s' t
  have hsq : T * T = r ⟨(t : G) * t, Subgroup.mul_self_mem_of_index_two hidx t⟩ := by
    rw [show T * T = s' (t * t) from (s'.map_mul t t).symm]
    exact (hagree ⟨(t : G) * t, Subgroup.mul_self_mem_of_index_two hidx t⟩
      (t * t).property).symm
  obtain ⟨q⟩ := hinv t
  let Q := q.toLinearEquiv
  have hQ (h : H) : Q.conj (r h) = r (MulAut.conjNormal (t : G) h) :=
    q.conj_apply_self h
  let f : Module.End C V →ₗ[C] Module.End C V := LinearMap.mulLeft C T
  let g : Module.End C V →ₗ[C] Module.End C V :=
    (LinearMap.mulRight C T).comp Q.conj.toLinearMap
  have hT (h : H) : T * r h = r (MulAut.conjNormal (t : G) h) * T := by
    have hfg : f (r h) = g (r h) := by
      apply linear_eq_of_actionSpan r hspan _ h
      intro j hj
      let c : H := MulAut.conjNormal (t : G) j
      have hc : (c : G) ∈ K := K.mul_mem (K.mul_mem t.property hj) (K.inv_mem t.property)
      change T * r j = Q.conj (r j) * T
      rw [hQ, hagree j hj, hagree c hc, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp [c, MulAut.conjNormal_apply, mul_assoc]
    change T * r h = Q.conj (r h) * T at hfg
    simpa only [hQ] using hfg
  let a := quadraticExtend r hidx ht T hT hsq
  refine ⟨a, MonoidHom.ext (fun h => quadraticExtend_on r hidx ht T hT hsq h), ?_⟩
  refine ⟨equivOfConj _ _ e fun k => ?_⟩
  change e.conj (a k) = s k
  suffices hak : a k = s' k by rw [hak, transport]
  by_cases hk : (k : G) ∈ H
  · exact (quadraticExtend_on r hidx ht T hT hsq ⟨k, hk⟩).trans (hagree _ k.property)
  · have hm : (k : G) * (t : G)⁻¹ ∈ K := (k * t⁻¹).property
    rw [quadraticExtend_off r hidx ht T hT hsq hk, hagree _ hm]
    change s' (k * t⁻¹) * s' t = s' k
    rw [← map_mul, inv_mul_cancel_right]

end Extension

section Closure

private def commonClosure (E : FiniteField F) : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure F := by
  letI : IsAlgClosure E (AlgebraicClosure F) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  letI : Module.IsTorsionFree E (AlgebraicClosure E) := DivisionSemiring.to_moduleIsTorsionFree
  letI : Module.IsTorsionFree E (AlgebraicClosure F) := DivisionSemiring.to_moduleIsTorsionFree
  exact IsAlgClosure.equiv E (AlgebraicClosure E) (AlgebraicClosure F)

/-- Compare the absolute group of an auxiliary field with its fixing subgroup
in the common algebraic closure. -/
private def toFixing (E : FiniteField F) : Γ E ≃* fixing E :=
  (AlgEquiv.autCongr (commonClosure E)).trans
    (IntermediateField.fixingSubgroupEquiv E.toIntermediateField).symm

private theorem toFixing_apply (E : FiniteField F) (g : Γ E) (x : AlgebraicClosure F) :
    (toFixing E g).val x = commonClosure E (g ((commonClosure E).symm x)) := rfl

private theorem toFixing_commutes (E : FiniteField F) (g : Γ E) (x : AlgebraicClosure E) :
    (toFixing E g).val (commonClosure E x) = commonClosure E (g x) := by
  rw [toFixing_apply, AlgEquiv.symm_apply_apply]

variable {K L : Type uF} [Field K] [Field L]

private def closureEmbeddingOfCommutes (f : K →+* L)
    (j : AlgebraicClosure K →+* AlgebraicClosure L)
    (hj : ∀ x, j (algebraMap K (AlgebraicClosure K) x) = algebraMap L (AlgebraicClosure L) (f x)) :
    ClosureEmbedding f := by
  letI : Algebra K L := f.toAlgebra
  refine { j with commutes' := fun x => ?_ }
  rw [IsScalarTower.algebraMap_apply K L (AlgebraicClosure L)]
  exact hj x

private abbrev closureRestriction (f : K →+* L) (ι : ClosureEmbedding f) :
    Γ L →ₜ* Γ K :=
  letI : Algebra K L := f.toAlgebra
  restrictionAlongClosure ι

private theorem closureRestriction_commutes (f : K →+* L) (ι : ClosureEmbedding f)
    (g : Γ L) (x : AlgebraicClosure K) :
    let : Algebra K L := f.toAlgebra
    ι (closureRestriction f ι g x) = g (ι x) := by
  let : Algebra K L := f.toAlgebra
  exact restrictionAlongClosure_commutes ι g x

private def baseClosure (E : FiniteField F) : ClosureEmbedding (algebraMap F E) :=
  closureEmbeddingOfCommutes _ (commonClosure E).symm.toRingHom fun x => by
    change (commonClosure E).symm (algebraMap F (AlgebraicClosure F) x) =
      algebraMap E (AlgebraicClosure E) (algebraMap F E x)
    rw [← (commonClosure E).symm.commutes, ← IsScalarTower.algebraMap_apply]

private theorem baseClosure_restriction (E : FiniteField F) (g : Γ E) :
    closureRestriction _ (baseClosure E) g = (toFixing E g).val := by
  apply AlgEquiv.ext
  intro x
  rw [toFixing_apply]
  have h := closureRestriction_commutes _ (baseClosure E) g x
  change (commonClosure E).symm (closureRestriction _ (baseClosure E) g x) =
    g ((commonClosure E).symm x) at h
  simpa only [AlgEquiv.apply_symm_apply] using congrArg (commonClosure E) h

private theorem toFixing_continuous (E : FiniteField F) : Continuous (toFixing E) := by
  apply continuous_induced_rng.2
  exact (closureRestriction _ (baseClosure E)).continuous.congr
    (baseClosure_restriction E)

private theorem toFixing_symm_continuous [CharZero F] (E : FiniteField F) :
    Continuous (toFixing E).symm := by
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  let e := (toFixing_continuous E).homeoOfEquivCompactToT2 (f := (toFixing E).toEquiv)
  exact e.symm.continuous

private abbrev fieldInclusion {E N : FiniteField F} (hEN : E ≤ N) : E →+* N :=
  (IntermediateField.inclusion (show E.toIntermediateField ≤ N.toIntermediateField from hEN)).toRingHom

private def inclusionClosure {E N : FiniteField F} (hEN : E ≤ N) :
    ClosureEmbedding (fieldInclusion hEN) :=
  closureEmbeddingOfCommutes _ ((commonClosure N).symm.toRingHom.comp (commonClosure E).toRingHom)
    fun x => by
      change (commonClosure N).symm (commonClosure E (algebraMap E (AlgebraicClosure E) x)) =
        algebraMap N (AlgebraicClosure N) (fieldInclusion hEN x)
      rw [(commonClosure E).commutes, ← (commonClosure N).symm.commutes]
      rfl

private theorem inclusionClosure_restriction {E N : FiniteField F} (hEN : E ≤ N) (g : Γ N) :
    (toFixing E (closureRestriction _ (inclusionClosure hEN) g)).val = (toFixing N g).val := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (commonClosure E).surjective x
  rw [toFixing_commutes, toFixing_apply]
  have h := closureRestriction_commutes _ (inclusionClosure hEN) g y
  change (commonClosure N).symm (commonClosure E (closureRestriction _ (inclusionClosure hEN) g y)) =
    g ((commonClosure N).symm (commonClosure E y)) at h
  simpa only [AlgEquiv.apply_symm_apply] using congrArg (commonClosure N) h

private theorem inclusionClosure_on_fixing {E N : FiniteField F} (hEN : E ≤ N) (h : fixing N) :
    closureRestriction _ (inclusionClosure hEN) ((toFixing N).symm h) =
      (toFixing E).symm ⟨h, fixing_antitone hEN h.property⟩ := by
  apply (toFixing E).injective
  apply Subtype.ext
  rw [inclusionClosure_restriction, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private abbrev fieldAutomorphism (E : FiniteField F) (t : Γ F) : E ≃ₐ[F] E :=
  t.restrictNormal E.toIntermediateField

private def automorphismClosure (E : FiniteField F) (t : Γ F) :
    ClosureEmbedding (fieldAutomorphism E t).toRingEquiv.toRingHom :=
  closureEmbeddingOfCommutes _
    ((commonClosure E).symm.toRingHom.comp (t.toRingHom.comp (commonClosure E).toRingHom))
    fun x => by
      change (commonClosure E).symm (t (commonClosure E (algebraMap E (AlgebraicClosure E) x))) =
        algebraMap E (AlgebraicClosure E) (fieldAutomorphism E t x)
      rw [(commonClosure E).commutes, ← t.restrictNormal_commutes E.toIntermediateField,
        (commonClosure E).symm.commutes]

private theorem automorphismClosure_restriction [CharZero F] (E : FiniteField F) (t : Γ F)
    (g : Γ E) :
    toFixing E (closureRestriction _ (automorphismClosure E t⁻¹) g) =
      MulAut.conjNormal t (toFixing E g) := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  apply AlgEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (commonClosure E).surjective x
  rw [toFixing_commutes, AlgEquiv.mul_apply, AlgEquiv.mul_apply, toFixing_apply]
  have h := closureRestriction_commutes _ (automorphismClosure E t⁻¹) g y
  change (commonClosure E).symm (t.symm (commonClosure E
    (closureRestriction _ (automorphismClosure E t⁻¹) g y))) =
    g ((commonClosure E).symm (t.symm (commonClosure E y))) at h
  change commonClosure E (closureRestriction _ (automorphismClosure E t⁻¹) g y) =
    t (commonClosure E (g ((commonClosure E).symm (t.symm (commonClosure E y)))))
  simpa only [AlgEquiv.apply_symm_apply] using
    congrArg (fun x => t (commonClosure E x)) h

variable {C : Type uC} [Field C] [TopologicalSpace C]

/-- Replace Mathlib's chosen lift by the compatible embedding used in the
common closure, retaining an actual intertwiner. -/
private def specifiedPullbackEquiv (f : K →+* L) (ι : ClosureEmbedding f)
    (A : Objects.{uF, uC, uV} K C) :
    FiniteRepresentation.Equiv (pullback f A).val
      (FiniteRepresentation.of
        (A.val.representation.comp (closureRestriction f ι).toMonoidHom)) := by
  letI : Algebra K L := f.toAlgebra
  rw [← pullbackAlongClosure_chosen_eq f A]
  exact pullbackAlongClosureEquiv ι IsAlgClosed.lift A

private abbrev fixingAction (E : FiniteField F) (A : Objects.{uF, uC, uV} E C) :
    Representation C (fixing E) A.val :=
  A.val.representation.comp (toFixing E).symm.toMonoidHom

private theorem fixingAction_invariant [CharZero F] (E : FiniteField F) (A : Objects E C)
    (hinv : ∀ σ : E ≃ₐ[F] E,
      Nonempty (FiniteRepresentation.Equiv (pullback σ.toRingEquiv.toRingHom A).val A.val))
    (t : Γ F) :
    Nonempty ((fixingAction E A).Equiv ((fixingAction E A).comp (MulAut.conjNormal t).toMonoidHom)) := by
  obtain ⟨p⟩ := hinv (fieldAutomorphism E t⁻¹)
  let ι := automorphismClosure E t⁻¹
  let q := p.symm.trans (specifiedPullbackEquiv _ ι A)
  refine ⟨equivOfConj _ _ q.toLinearEquiv fun h => ?_⟩
  let g := (toFixing E).symm h
  have hg : closureRestriction _ ι g = (toFixing E).symm (MulAut.conjNormal t h) := by
    apply (toFixing E).injective
    simp only [ι, automorphismClosure_restriction, g, MulEquiv.apply_symm_apply]
  have hq := q.conj_apply_self g
  change q.toLinearEquiv.conj (A.val.representation g) =
    A.val.representation (closureRestriction _ ι g) at hq
  rw [hg] at hq
  exact hq

private theorem fixingAction_pair (E N : FiniteField F) (A : Objects E C) (B : Objects N C)
    (p : Nonempty (FiniteRepresentation.Equiv
      (pullback (fieldInclusion (le_sup_left (a := E) (b := N))) A).val
      (pullback (fieldInclusion (le_sup_right (a := E) (b := N))) B).val)) :
    ∃ e : A.val ≃ₗ[C] B.val, ∀ g : ↥(fixing E ⊓ fixing N),
      e.conj (fixingAction E A ⟨g, g.property.1⟩) = fixingAction N B ⟨g, g.property.2⟩ := by
  obtain ⟨p⟩ := p
  let hE : E ≤ E ⊔ N := le_sup_left
  let hN : N ≤ E ⊔ N := le_sup_right
  let eE := specifiedPullbackEquiv _ (inclusionClosure hE) A
  let eN := specifiedPullbackEquiv _ (inclusionClosure hN) B
  let q := (eE.symm.trans p).trans eN
  refine ⟨q.toLinearEquiv, fun g => ?_⟩
  let h : fixing (E ⊔ N) := ⟨g, by rw [fixing_sup]; exact g.property⟩
  have hq := q.conj_apply_self ((toFixing (E ⊔ N)).symm h)
  change q.toLinearEquiv.conj
    (A.val.representation (closureRestriction _ (inclusionClosure hE) ((toFixing (E ⊔ N)).symm h))) =
    B.val.representation (closureRestriction _ (inclusionClosure hN) ((toFixing (E ⊔ N)).symm h))
    at hq
  simp only [inclusionClosure_on_fixing] at hq
  exact hq

/-- An intertwiner on a fixing subgroup is equivalent to one for the
published pullback to the corresponding field. -/
private theorem pullback_equiv_iff_fixing (E : FiniteField F) (A : Objects F C) (B : Objects E C) :
    Nonempty (FiniteRepresentation.Equiv (pullback (algebraMap F E) A).val B.val) ↔
      Nonempty (Representation.Equiv
        (A.val.representation.comp (fixing E).subtype) (fixingAction E B)) := by
  let p := specifiedPullbackEquiv _ (baseClosure E) A
  constructor
  · rintro ⟨e⟩
    let q := p.symm.trans e
    refine ⟨equivOfConj _ _ q.toLinearEquiv fun h => ?_⟩
    let g := (toFixing E).symm h
    have hq := q.conj_apply_self g
    change q.toLinearEquiv.conj (A.val.representation (closureRestriction _ (baseClosure E) g)) =
      B.val.representation g at hq
    change q.toLinearEquiv.conj (A.val.representation h.val) = B.val.representation ((toFixing E).symm h)
    simpa only [baseClosure_restriction, g, MulEquiv.apply_symm_apply] using hq
  · rintro ⟨q⟩
    refine ⟨p.trans (equivOfConj _ _ q.toLinearEquiv fun g => ?_)⟩
    change q.toLinearEquiv.conj (A.val.representation (closureRestriction _ (baseClosure E) g)) =
      B.val.representation g
    calc
      _ = q.toLinearEquiv.conj (A.val.representation (toFixing E g).val) :=
        congrArg (fun a : Γ F => q.toLinearEquiv.conj (A.val.representation a))
          (baseClosure_restriction E g)
      _ = B.val.representation g := by
        have hq := q.conj_apply_self (toFixing E g)
        change q.toLinearEquiv.conj (A.val.representation (toFixing E g).val) =
          B.val.representation ((toFixing E).symm (toFixing E g)) at hq
        exact hq.trans (congrArg B.val.representation ((toFixing E).symm_apply_apply g))

end Closure

section Patching

variable [CharZero F] {C : Type uC} [Field C] [TopologicalSpace C]
variable {I : Set (FiniteField F)} (R : (E : I) → Objects.{uF, uC, uV} E.val C)

private abbrev HasRestriction {V : Type*} [AddCommGroup V] [Module C V]
    (a : Representation C (Γ F) V) (E : I) : Prop :=
  Nonempty (Representation.Equiv (a.comp (fixing E.val).subtype) (fixingAction E.val (R E)))

private theorem exists_fixing_patch
    (hdisj : ∀ M : FiniteField F, ∃ N : I, N.val ⊓ M = ⊥)
    (hdegree : ∀ E : I, Module.finrank F E.val = 2)
    (hinv : ∀ (E : I) (t : Γ F),
      Nonempty ((fixingAction E.val (R E)).Equiv
        ((fixingAction E.val (R E)).comp (MulAut.conjNormal t).toMonoidHom)))
    (hpair : ∀ E N : I, ∃ e : (R E).val ≃ₗ[C] (R N).val,
      ∀ h : ↥(fixing E.val ⊓ fixing N.val),
        e.conj (fixingAction E.val (R E) ⟨h, h.property.1⟩) =
          fixingAction N.val (R N) ⟨h, h.property.2⟩) :
    ∃ E₀ : I, ∃ a : Representation C (Γ F) (R E₀).val,
      a.comp (fixing E₀.val).subtype = fixingAction E₀.val (R E₀) ∧
        ∀ E : I, HasRestriction R a E := by
  obtain ⟨E₀, _⟩ := hdisj ⊥
  let r := fixingAction E₀.val (R E₀)
  obtain ⟨M, hE₀M, hM⟩ := exists_stable_span (C := C) E₀.val r
  have hidx : (fixing E₀.val).index = 2 := (fixing_index E₀.val).trans (hdegree E₀)
  have extension (N : I) (hNM : fixing N.val ⊔ fixing M = ⊤) :
      ∃ a : Representation C (Γ F) (R E₀).val,
        a.comp (fixing E₀.val).subtype = r ∧ HasRestriction R a N := by
    have hjoin : fixing E₀.val ⊔ fixing N.val = ⊤ := by
      apply top_unique
      rw [← hNM]
      exact sup_le le_sup_right ((fixing_antitone hE₀M).trans le_sup_left)
    have hs := actionSpan_full_of_independent E₀.val r hE₀M hM hNM
    obtain ⟨e, he⟩ := hpair E₀ N
    exact exists_common_extension hidx r _ hjoin hs (hinv E₀) e he
  obtain ⟨E₁, hE₁M⟩ := hdisj M
  have hE₁join := fixing_sup_eq_top hE₁M
  obtain ⟨a, ha₀, ⟨ha₁⟩⟩ := extension E₁ hE₁join
  -- Compare the two extensions on the compositum with E₁, then on E₀.
  have matches_independent (N : I) (hN : N.val ⊓ (M ⊔ E₁.val) = ⊥) : HasRestriction R a N := by
    have hNj := fixing_sup_eq_top hN
    rw [fixing_sup] at hNj
    have hNM : fixing N.val ⊔ fixing M = ⊤ := by
      apply top_unique
      rw [← hNj]
      exact sup_le_sup_left inf_le_left _
    obtain ⟨b, hb₀, ⟨hbN⟩⟩ := extension N hNM
    obtain ⟨e, he⟩ := hpair E₁ N
    let f := hbN.symm
    let T := (ha₁.toLinearEquiv.trans e).trans f.toLinearEquiv
    have hTN (h : fixing (E₁.val ⊔ N.val)) : T.conj (a h.val) = b h.val := by
      have hg : h.val ∈ fixing E₁.val ⊓ fixing N.val := fixing_sup E₁.val N.val ▸ h.property
      have hf := f.conj_apply_self (⟨h.val, hg.2⟩ : fixing N.val)
      change f.toLinearEquiv.conj (fixingAction N.val (R N) ⟨h.val, hg.2⟩) = b h.val at hf
      calc
        _ = f.toLinearEquiv.conj (e.conj (ha₁.toLinearEquiv.conj (a h.val))) := rfl
        _ = f.toLinearEquiv.conj (e.conj (fixingAction E₁.val (R E₁) ⟨h, hg.1⟩)) :=
          congrArg (fun d => f.toLinearEquiv.conj (e.conj d)) (ha₁.conj_apply_self ⟨h, hg.1⟩)
        _ = f.toLinearEquiv.conj (fixingAction N.val (R N) ⟨h, hg.2⟩) :=
          congrArg f.toLinearEquiv.conj (he ⟨h, hg⟩)
        _ = b h.val := hf
    have hj : fixing (E₁.val ⊔ N.val) ⊔ fixing M = ⊤ := by
      rw [fixing_sup]
      exact inf_sup_eq_top hE₁join hNj
    have hs := actionSpan_full_of_independent E₀.val r hE₀M hM hj
    have har (h : fixing E₀.val) : a h.val = r h := DFunLike.congr_fun ha₀ h
    have hbr (h : fixing E₀.val) : b h.val = r h := DFunLike.congr_fun hb₀ h
    have hT₀ (h : fixing E₀.val) : T.conj (a h.val) = b h.val := by
      rw [har, hbr]
      refine linear_eq_of_actionSpan r hs (f := T.conj.toLinearMap) (g := LinearMap.id) ?_ h
      intro j hj
      change T.conj (r j) = r j
      exact (congrArg T.conj (har j).symm).trans ((hTN ⟨j, hj⟩).trans (hbr j))
    have htop : fixing E₀.val ⊔ fixing (E₁.val ⊔ N.val) = ⊤ := by
      apply top_unique
      rw [← hj]
      exact sup_le le_sup_right ((fixing_antitone hE₀M).trans le_sup_left)
    let q := equivOfSup a b T htop hT₀ hTN
    let qN := equivOfConj (a.comp (fixing N.val).subtype) (b.comp (fixing N.val).subtype)
      q.toLinearEquiv (fun h => q.conj_apply_self h.val)
    exact ⟨qN.trans hbN⟩
  -- On an arbitrary auxiliary field, stabilize the span of both actions.
  refine ⟨E₀, a, ha₀, fun E => ?_⟩
  let aE := a.comp (fixing E.val).subtype
  let rE := fixingAction E.val (R E)
  let pair := MonoidHom.prod aE rE
  obtain ⟨L, hEL, hL⟩ := exists_stable_span (C := C) E.val pair
  obtain ⟨N, hN⟩ := hdisj ((M ⊔ E₁.val) ⊔ L)
  have hNsmall : N.val ⊓ (M ⊔ E₁.val) = ⊥ :=
    bot_unique ((inf_le_inf_left _ le_sup_left).trans_eq hN)
  have hNL : fixing N.val ⊔ fixing L = ⊤ :=
    fixing_sup_eq_top (bot_unique ((inf_le_inf_left _ le_sup_right).trans_eq hN))
  obtain ⟨haN⟩ := matches_independent N hNsmall
  obtain ⟨e, he⟩ := hpair N E
  let T := haN.toLinearEquiv.trans e
  have hs := actionSpan_full_of_independent E.val pair hEL hL hNL
  refine ⟨equivOfPairSpan aE rE T hs fun g hg => ?_⟩
  calc
    _ = e.conj (haN.toLinearEquiv.conj (a g.val)) := rfl
    _ = e.conj (fixingAction N.val (R N) ⟨g, hg⟩) :=
      congrArg e.conj (haN.conj_apply_self ⟨g, hg⟩)
    _ = rE g := he ⟨g, hg, g.property⟩

private theorem fixing_patch_unique {V W : Type*}
    [AddCommGroup V] [Module C V] [FiniteDimensional C V]
    [AddCommGroup W] [Module C W] [FiniteDimensional C W]
    (hdisj : ∀ M : FiniteField F, ∃ N : I, N.val ⊓ M = ⊥)
    (a : Representation C (Γ F) V) (b : Representation C (Γ F) W)
    (ha : ∀ E : I, HasRestriction R a E) (hb : ∀ E : I, HasRestriction R b E) :
    Nonempty (a.Equiv b) := by
  let H := fixing (⊥ : FiniteField F)
  let r := a.comp H.subtype
  let s := b.comp H.subtype
  let pair := MonoidHom.prod r s
  obtain ⟨M, hM, hstable⟩ := exists_stable_span (C := C) ⊥ pair
  obtain ⟨N, hN⟩ := hdisj M
  have hs := actionSpan_full_of_independent ⊥ pair hM hstable (fixing_sup_eq_top hN)
  obtain ⟨e⟩ := ha N
  obtain ⟨f⟩ := hb N
  let q := e.trans f.symm
  let qH := equivOfPairSpan r s q.toLinearEquiv hs fun h hh => q.conj_apply_self ⟨h, hh⟩
  refine ⟨equivOfConj a b qH.toLinearEquiv fun g => ?_⟩
  have hg : g ∈ H := by change g ∈ fixing (⊥ : FiniteField F); rw [fixing_bot]; trivial
  exact qH.conj_apply_self ⟨g, hg⟩

end Patching

end QuadraticPatching

open QuadraticPatching in
/-- Quadratic patching by cyclic extension and stable finite-dimensional
spans of actions, with actual linear intertwiners on all auxiliary fields. -/
theorem quadraticPatching.{uF, uC, uV} : QuadraticPatchingStatement.{uF, uC, uV} := by
  classical
  intro F _ _ C _ _ _ _ _ _ n S I R hdegree habundance hR hinv hpair
  let : Infinite (Global.FinitePlace F) := Global.numberField_finitePlaces_infinite F
  obtain ⟨v, hv⟩ := Finset.exists_notMem S
  have hdisj (M : FiniteField F) : ∃ E : I, E.val ⊓ M = ⊥ := by
    obtain ⟨E, hE, _⟩ := habundance v hv M
    exact ⟨E, hE⟩
  obtain ⟨E₀, a, ha₀, ha⟩ := exists_fixing_patch R hdisj hdegree
    (fun E => fixingAction_invariant E.val (R E) (hinv E))
    (fun E N => fixingAction_pair E.val N.val (R E) (R N) (hpair E N))
  have hc : IsContinuous (FiniteRepresentation.of a) := by
    apply continuous_of_open_restriction (fixing_open E₀.val) a
    rw [ha₀]
    let : TopologicalSpace (Module.End C (R E₀).val) := moduleTopology C _
    exact (R E₀).property.comp (toFixing_symm_continuous E₀.val)
  let A : Objects.{uF, uC, uV} F C := ⟨FiniteRepresentation.of a, hc⟩
  have hs : Representation.IsSemisimpleRepresentation a := by
    have hidx : (fixing E₀.val).index = 2 := (fixing_index E₀.val).trans (hdegree E₀)
    let : (fixing E₀.val).FiniteIndex := ⟨by rw [hidx]; decide⟩
    apply Langlands.finiteIndexSemisimplicityAscent C (Γ F) (R E₀).val (fixing E₀.val) a
    rw [ha₀]
    exact semisimple_comp_of_surjective _ _ (toFixing E₀.val).symm.surjective (hR E₀).2
  refine ⟨A, ⟨(hR E₀).1, hs, fun E => (pullback_equiv_iff_fixing E.val A (R E)).mpr (ha E)⟩, ?_⟩
  intro B hB
  exact fixing_patch_unique R hdisj a B.val.representation ha
    (fun E => (pullback_equiv_iff_fixing E.val B (R E)).mp (hB.2.2 E))

end Langlands.GaloisRepresentation
