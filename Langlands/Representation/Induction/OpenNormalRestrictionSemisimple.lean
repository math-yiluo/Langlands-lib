import Langlands.Representation.Induction.OpenAdjunction
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Restriction of a compact induction to an open normal subgroup

Let `H` be an open normal subgroup of a topological group `G` and `σ` an irreducible
smooth representation of `H` over a field `k`. The restriction to `H` of the compact
induction `c-Ind_H^G σ` is a semisimple `k[H]`-module: it is the sum of the images of the
`H`-intertwiners `v ↦ x⁻¹ · unit(v)` from the conjugates of `σ`, which are simple.

Consequently, for every `H`-intertwiner `j : σ → τ|_H` that is injective, every nonzero
subquotient `D` of `c-Ind_H^G σ` (given by an injective `G`-intertwiner `B → c-Ind σ` and a
surjective `G`-intertwiner `B → D`) admits a nonzero `H`-intertwiner `D|_H → τ|_H`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open scoped MonoidAlgebra

namespace Langlands.Induction

universe uR uG uV uW uB uD

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {V : Type uV} [AddCommGroup V] [Module k V]

section Conj

variable (H : Subgroup G) [H.Normal]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Conjugation `h ↦ x h x⁻¹` on a normal subgroup. -/
def normalConj (x : G) : H →* H where
  toFun h := ⟨x * h * x⁻¹, Subgroup.Normal.conj_mem inferInstance _ h.2 x⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] theorem normalConj_apply_coe (x : G) (h : H) :
    ((normalConj H x h : H) : G) = x * h * x⁻¹ :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem normalConj_surjective (x : G) : Function.Surjective (normalConj H x) := by
  intro h
  refine ⟨⟨x⁻¹ * h * x, ?_⟩, ?_⟩
  · simpa using Subgroup.Normal.conj_mem inferInstance _ h.2 x⁻¹
  · ext
    simp [mul_assoc]

end Conj

/-- Composition with a surjective homomorphism preserves irreducibility. -/
theorem isIrreducible_comp_of_surjective {K L : Type*} [Monoid K] [Monoid L]
    (σ : Representation k L V) (f : K →* L) (hf : Function.Surjective f)
    (hσ : σ.IsIrreducible) : Representation.IsIrreducible (σ.comp f) := by
  let e : Subrepresentation σ ≃o Subrepresentation (σ.comp f) :=
    { toFun := fun S => ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g _ hv => by
        obtain ⟨h, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule h hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mp hσ

section Semisimple

variable (H : Subgroup G) [H.Normal] (hH : IsOpen (H : Set G))
  (σ : Representation k H V) (hσ : IsSmooth σ)

/-- The `H`-intertwiner `v ↦ x⁻¹ · unit(v)` from the conjugate `σ ∘ (h ↦ x h x⁻¹)` to the
restriction of the compact induction. -/
def translatedUnitMap (x : G) :
    Representation.IntertwiningMap (σ.comp (normalConj H x))
      ((compactInduced H σ).comp H.subtype) where
  toLinearMap := (compactInduced H σ x⁻¹).comp (unitMap H hH σ hσ).toLinearMap
  isIntertwining' h := by
    refine LinearMap.ext fun v => ?_
    change compactInduced H σ x⁻¹ (unitMap H hH σ hσ (σ (normalConj H x h) v)) =
      compactInduced H σ h (compactInduced H σ x⁻¹ (unitMap H hH σ hσ v))
    rw [(unitMap H hH σ hσ).isIntertwining]
    change compactInduced H σ x⁻¹ (compactInduced H σ (x * h * x⁻¹) _) = _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

theorem translatedUnitMap_apply (x : G) (v : V) :
    translatedUnitMap H hH σ hσ x v = compactInduced H σ x⁻¹ (unitMap H hH σ hσ v) :=
  rfl

include hH hσ in
/-- The restriction to an open normal subgroup `H` of the compact induction of an
irreducible smooth representation of `H` is a semisimple `k[H]`-module. -/
theorem isSemisimpleModule_compactInduced_restrict (hirr : σ.IsIrreducible) :
    IsSemisimpleModule k[H] (Representation.asModule ((compactInduced H σ).comp H.subtype)) := by
  let p : G → Submodule k[H] (Representation.asModule ((compactInduced H σ).comp H.subtype)) :=
    fun x =>
    LinearMap.range (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (translatedUnitMap H hH σ hσ x))
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := p) (fun x => ?_) ?_
  · have : Representation.IsIrreducible (σ.comp (normalConj H x)) :=
      isIrreducible_comp_of_surjective σ _ (normalConj_surjective H x) hirr
    exact IsSemisimpleModule.range _
  · rw [eq_top_iff]
    intro f _
    have hf := cosetSum_unitMap H hH σ hσ f
    change f ∈ ⨆ x, p x
    rw [← hf, cosetSum_apply]
    refine finsum_induction (fun y => y ∈ ⨆ x, p x) (Submodule.zero_mem _)
      (fun a b ha hb => Submodule.add_mem _ ha hb) ?_
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    apply Submodule.mem_iSup_of_mem x
    exact ⟨Induction.eval H σ f.1 x, rfl⟩

end Semisimple

section Subquotient

variable {W : Type uW} [AddCommGroup W] [Module k W]
variable (H : Subgroup G) (σ : Representation k H V)

/-- For `x : G` and an `H`-intertwiner `j : σ → τ|_H`, the `H`-intertwiner
`f ↦ τ(x⁻¹) j(f x)` from the restriction of the compact induction to `τ|_H`. -/
def evalTranslate [H.Normal] (τ : Representation k G W)
    (j : Representation.IntertwiningMap σ (τ.comp H.subtype)) (x : G) :
    Representation.IntertwiningMap ((compactInduced H σ).comp H.subtype) (τ.comp H.subtype) where
  toFun f := τ x⁻¹ (j (Induction.eval H σ f.1 x))
  map_add' f f' := by
    change τ x⁻¹ (j (Induction.eval H σ f.1 x + Induction.eval H σ f'.1 x)) = _
    rw [map_add, map_add]
  map_smul' c f := by
    change τ x⁻¹ (j (c • Induction.eval H σ f.1 x)) = _
    rw [map_smul, map_smul]
    rfl
  isIntertwining' h := by
    ext f
    change τ x⁻¹ (j (Induction.eval H σ f.1 (x * h))) =
      τ h (τ x⁻¹ (j (Induction.eval H σ f.1 x)))
    have hcov := f.1.1.2 (normalConj H x h) x
    have hx : x * (h : G) = H.subtype (normalConj H x h) * x := by
      simp [mul_assoc]
    change Induction.eval H σ f.1 (H.subtype (normalConj H x h) * x) =
      σ (normalConj H x h) (Induction.eval H σ f.1 x) at hcov
    rw [hx, hcov, j.isIntertwining]
    change τ x⁻¹ (τ (x * h * x⁻¹) _) = _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group

theorem evalTranslate_apply [H.Normal] (τ : Representation k G W)
    (j : Representation.IntertwiningMap σ (τ.comp H.subtype)) (x : G) (f : CompactFunctions H σ) :
    evalTranslate H σ τ j x f = τ x⁻¹ (j (Induction.eval H σ f.1 x)) :=
  rfl

variable [H.Normal] (hH : IsOpen (H : Set G)) (hσ : IsSmooth σ)

include hH hσ in
/-- Let `j : σ → τ|_H` be an injective `H`-intertwiner from an irreducible smooth
representation of the open normal subgroup `H`. If `D` is a subquotient of `c-Ind_H^G σ`,
presented by an injective `G`-intertwiner `i : B → c-Ind σ` and a surjective
`G`-intertwiner `q : B → D`, and `D` is nonzero, then there is a nonzero
`H`-intertwiner `D|_H → τ|_H`. -/
theorem exists_restricted_intertwiningMap_ne_zero_of_subquotient
    (hirr : σ.IsIrreducible) (τ : Representation k G W)
    (j : Representation.IntertwiningMap σ (τ.comp H.subtype)) (hj : Function.Injective j)
    {B : Type uB} [AddCommGroup B] [Module k B] (β : Representation k G B)
    {D : Type uD} [AddCommGroup D] [Module k D] (δ : Representation k G D)
    (i : β.IntertwiningMap (compactInduced H σ)) (hi : Function.Injective i)
    (q : β.IntertwiningMap δ) (hq : Function.Surjective q) (d : D) (hd : d ≠ 0) :
    ∃ φ : Representation.IntertwiningMap (δ.comp H.subtype) (τ.comp H.subtype), φ ≠ 0 := by
  have := isSemisimpleModule_compactInduced_restrict H hH σ hσ hirr
  let iH := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (resIntertwining H (compactInduced H σ) i)
  have hiH : Function.Injective iH := hi
  have : IsSemisimpleModule k[H] (Representation.asModule (β.comp H.subtype)) :=
    IsSemisimpleModule.of_injective iH hiH
  let qH := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (resIntertwining H δ q)
  have hqH : Function.Surjective qH := hq
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property qH hqH LinearMap.id
  let s' := (Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm s
  have hqs : q (s' d) = d := congrArg (fun T => T d) hs
  have hsd : s' d ≠ 0 := by
    intro h0
    apply hd
    rw [← hqs, h0, map_zero]
  have hisd : i (s' d) ≠ 0 := by
    intro h0
    exact hsd (hi (h0.trans (map_zero i).symm))
  obtain ⟨x, hx⟩ : ∃ x, Induction.eval H σ (i (s' d)).1 x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hisd (compactFunctions_ext H σ fun y => (hcon y).trans rfl)
  refine ⟨((evalTranslate H σ τ j x).comp (resIntertwining H (compactInduced H σ) i)).comp s',
    fun hφ => ?_⟩
  have h0 := congrArg (fun T => T d) hφ
  change τ x⁻¹ (j (Induction.eval H σ (i (s' d)).1 x)) = 0 at h0
  have h1 : j (Induction.eval H σ (i (s' d)).1 x) = 0 := by
    have h2 := congrArg (τ x) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero] at h2
  exact hx (hj (h1.trans (map_zero j).symm))

end Subquotient

end Langlands.Induction
