import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Splitting a cofinite restricted product along a predicate on the indices

For a decidable predicate `p` on the index type, the cofinite restricted product over all
indices is identified with the product of the cofinite restricted products over `{i // p i}`
and over `{i // ¬ p i}`. When every restricting subset is open this is a homeomorphism, and for
groups and subgroups it is an isomorphism of topological groups. When `{i // p i}` is finite,
the first factor is the full product over `{i // p i}`.
-/

open Filter Set
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} (R : ι → Type*) (A : (i : ι) → Set (R i))

section Set

/-- Restriction of a cofinite restricted family to the indices of a subtype. -/
def restrictSubtype (q : ι → Prop) :
    Πʳ i, [R i, A i] → Πʳ (i : {i // q i}), [R i, A i] :=
  mapAlong R (fun i : {i // q i} => R i) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ => id) (Eventually.of_forall fun _ => mapsTo_id _)

@[simp]
theorem restrictSubtype_apply (q : ι → Prop) (x : Πʳ i, [R i, A i]) (i : {i // q i}) :
    restrictSubtype R A q x i = x i :=
  rfl

variable (p : ι → Prop) [DecidablePred p]

/-- Glue a cofinite restricted family over `{i // p i}` and one over `{i // ¬ p i}`. -/
def glueSubtype (x : Πʳ (i : {i // p i}), [R i, A i])
    (y : Πʳ (i : {i // ¬ p i}), [R i, A i]) : Πʳ i, [R i, A i] :=
  ⟨fun i => if h : p i then x ⟨i, h⟩ else y ⟨i, h⟩, by
    have hx : {i : {i // p i} | x i ∉ A i}.Finite := eventually_cofinite.mp x.2
    have hy : {i : {i // ¬ p i} | y i ∉ A i}.Finite := eventually_cofinite.mp y.2
    refine eventually_cofinite.mpr (((hx.image Subtype.val).union
      (hy.image Subtype.val)).subset ?_)
    intro i hi
    by_cases h : p i
    · exact Or.inl ⟨⟨i, h⟩, by simpa [h] using hi, rfl⟩
    · exact Or.inr ⟨⟨i, h⟩, by simpa [h] using hi, rfl⟩⟩

theorem glueSubtype_apply_of_pos (x : Πʳ (i : {i // p i}), [R i, A i])
    (y : Πʳ (i : {i // ¬ p i}), [R i, A i]) {i : ι} (h : p i) :
    glueSubtype R A p x y i = x ⟨i, h⟩ :=
  dite_eq_left h

theorem glueSubtype_apply_of_neg (x : Πʳ (i : {i // p i}), [R i, A i])
    (y : Πʳ (i : {i // ¬ p i}), [R i, A i]) {i : ι} (h : ¬ p i) :
    glueSubtype R A p x y i = y ⟨i, h⟩ :=
  dite_eq_right h

/-- A cofinite restricted product is the product of the cofinite restricted products over the
indices satisfying `p` and over those not satisfying `p`. -/
def splitEquiv :
    Πʳ i, [R i, A i] ≃ Πʳ (i : {i // p i}), [R i, A i] × Πʳ (i : {i // ¬ p i}), [R i, A i] where
  toFun x := (restrictSubtype R A p x, restrictSubtype R A (fun i => ¬ p i) x)
  invFun z := glueSubtype R A p z.1 z.2
  left_inv x := by
    ext i
    by_cases h : p i
    · exact glueSubtype_apply_of_pos R A p _ _ h
    · exact glueSubtype_apply_of_neg R A p _ _ h
  right_inv z := by
    refine Prod.ext ?_ ?_
    · ext i
      exact glueSubtype_apply_of_pos R A p _ _ i.2
    · ext i
      exact glueSubtype_apply_of_neg R A p _ _ i.2

@[simp]
theorem splitEquiv_apply_fst (x : Πʳ i, [R i, A i]) (i : {i // p i}) :
    (splitEquiv R A p x).1 i = x i :=
  rfl

@[simp]
theorem splitEquiv_apply_snd (x : Πʳ i, [R i, A i]) (i : {i // ¬ p i}) :
    (splitEquiv R A p x).2 i = x i :=
  rfl

theorem splitEquiv_symm_apply
    (z : Πʳ (i : {i // p i}), [R i, A i] × Πʳ (i : {i // ¬ p i}), [R i, A i]) :
    (splitEquiv R A p).symm z = glueSubtype R A p z.1 z.2 :=
  rfl

/-- A family lies in every restricting subset exactly when both of its parts do. -/
theorem forall_mem_iff_splitEquiv (x : Πʳ i, [R i, A i]) :
    (∀ i, x i ∈ A i) ↔
      (∀ i : {i // p i}, (splitEquiv R A p x).1 i ∈ A i) ∧
        ∀ i : {i // ¬ p i}, (splitEquiv R A p x).2 i ∈ A i := by
  refine ⟨fun h => ⟨fun i => h i, fun i => h i⟩, fun h i => ?_⟩
  by_cases hi : p i
  · exact h.1 ⟨i, hi⟩
  · exact h.2 ⟨i, hi⟩

end Set

section Topology

variable [∀ i, TopologicalSpace (R i)]

theorem continuous_restrictSubtype (q : ι → Prop) : Continuous (restrictSubtype R A q) :=
  mapAlong_continuous _ _ _ _ _ _ fun _ => continuous_id

variable {A} (p : ι → Prop) [DecidablePred p]

theorem continuous_glueSubtype (hA : ∀ i, IsOpen (A i)) :
    Continuous (fun z : Πʳ (i : {i // p i}), [R i, A i] × Πʳ (i : {i // ¬ p i}), [R i, A i] =>
      glueSubtype R A p z.1 z.2) := by
  rw [continuous_dom_prod_right (fun i : {i // p i} => hA i)]
  intro S hS
  rw [continuous_dom_prod_left (fun i : {i // ¬ p i} => hA i)]
  intro T hT
  let U : Set ι := {i | if h : p i then (⟨i, h⟩ : {i // p i}) ∈ S
    else (⟨i, h⟩ : {i // ¬ p i}) ∈ T}
  have hU : cofinite ≤ 𝓟 U := by
    have hS' : Sᶜ.Finite := mem_cofinite.mp (le_principal_iff.mp hS)
    have hT' : Tᶜ.Finite := mem_cofinite.mp (le_principal_iff.mp hT)
    refine le_principal_iff.mpr (mem_cofinite.mpr (((hS'.image Subtype.val).union
      (hT'.image Subtype.val)).subset ?_))
    intro i hi
    by_cases h : p i
    · exact Or.inl ⟨⟨i, h⟩, by simpa [U, h] using hi, rfl⟩
    · exact Or.inr ⟨⟨i, h⟩, by simpa [U, h] using hi, rfl⟩
  let g : Πʳ (i : {i // p i}), [R i, A i]_[𝓟 S] × Πʳ (i : {i // ¬ p i}), [R i, A i]_[𝓟 T] →
      Πʳ i, [R i, A i]_[𝓟 U] := fun z =>
    ⟨fun i => if h : p i then z.1 ⟨i, h⟩ else z.2 ⟨i, h⟩, by
      refine eventually_principal.mpr fun i hi => ?_
      by_cases h : p i
      · have hiS : (⟨i, h⟩ : {i // p i}) ∈ S := by simpa [U, h] using hi
        simp only [h, ↓reduceDIte]
        exact eventually_principal.mp z.1.2 _ hiS
      · have hiT : (⟨i, h⟩ : {i // ¬ p i}) ∈ T := by simpa [U, h] using hi
        simp only [h, ↓reduceDIte]
        exact eventually_principal.mp z.2.2 _ hiT⟩
  show Continuous (inclusion R A hU ∘ g)
  refine (continuous_inclusion hU).comp ?_
  refine continuous_rng_of_principal_iff_forall.mpr fun i => ?_
  by_cases h : p i
  · have hg : (fun x : Πʳ i, [R i, A i]_[𝓟 U] => x i) ∘ g = fun z => z.1 ⟨i, h⟩ := by
      funext z
      exact dite_eq_left h
    rw [hg]
    exact (continuous_eval _).comp continuous_fst
  · have hg : (fun x : Πʳ i, [R i, A i]_[𝓟 U] => x i) ∘ g = fun z => z.2 ⟨i, h⟩ := by
      funext z
      exact dite_eq_right h
    rw [hg]
    exact (continuous_eval _).comp continuous_snd

/-- If every restricting subset is open, splitting along `p` is a homeomorphism. -/
def splitHomeomorph (hA : ∀ i, IsOpen (A i)) :
    Πʳ i, [R i, A i] ≃ₜ Πʳ (i : {i // p i}), [R i, A i] × Πʳ (i : {i // ¬ p i}), [R i, A i] where
  toEquiv := splitEquiv R A p
  continuous_toFun :=
    (continuous_restrictSubtype R A p).prodMk (continuous_restrictSubtype R A _)
  continuous_invFun := continuous_glueSubtype R p hA

@[simp]
theorem coe_splitHomeomorph (hA : ∀ i, IsOpen (A i)) :
    ⇑(splitHomeomorph R p hA) = splitEquiv R A p :=
  rfl

@[simp]
theorem coe_splitHomeomorph_symm (hA : ∀ i, IsOpen (A i)) :
    ⇑(splitHomeomorph R p hA).symm = (splitEquiv R A p).symm :=
  rfl

variable (A) in
/-- Over a finite index type the cofinite restricted product is the full product. -/
def finiteHomeomorph [Finite ι] : Πʳ i, [R i, A i] ≃ₜ Π i, R i where
  toFun x i := x i
  invFun := inclusion R A cofinite_eq_bot.le ∘ homeoBot (R := R) (A := A)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coe
  continuous_invFun := (continuous_inclusion _).comp (homeoBot (R := R) (A := A)).continuous

@[simp]
theorem finiteHomeomorph_apply [Finite ι] (x : Πʳ i, [R i, A i]) (i : ι) :
    finiteHomeomorph R A x i = x i :=
  rfl

@[simp]
theorem finiteHomeomorph_symm_apply [Finite ι] (x : Π i, R i) (i : ι) :
    (finiteHomeomorph R A).symm x i = x i :=
  rfl

/-- If every restricting subset is open and only finitely many indices satisfy `p`, the
cofinite restricted product is the full product over `{i // p i}` times the cofinite
restricted product over `{i // ¬ p i}`. -/
def splitFiniteHomeomorph [Finite {i // p i}] (hA : ∀ i, IsOpen (A i)) :
    Πʳ i, [R i, A i] ≃ₜ (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, A i] :=
  (splitHomeomorph R p hA).trans ((finiteHomeomorph _ _).prodCongr (Homeomorph.refl _))

@[simp]
theorem splitFiniteHomeomorph_apply_fst [Finite {i // p i}] (hA : ∀ i, IsOpen (A i))
    (x : Πʳ i, [R i, A i]) (i : {i // p i}) :
    (splitFiniteHomeomorph R p hA x).1 i = x i :=
  rfl

@[simp]
theorem splitFiniteHomeomorph_apply_snd [Finite {i // p i}] (hA : ∀ i, IsOpen (A i))
    (x : Πʳ i, [R i, A i]) (i : {i // ¬ p i}) :
    (splitFiniteHomeomorph R p hA x).2 i = x i :=
  rfl

theorem splitFiniteHomeomorph_symm_apply_of_pos [Finite {i // p i}] (hA : ∀ i, IsOpen (A i))
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, A i]) {i : ι} (h : p i) :
    (splitFiniteHomeomorph R p hA).symm z i = z.1 ⟨i, h⟩ :=
  glueSubtype_apply_of_pos R A p _ _ h

theorem splitFiniteHomeomorph_symm_apply_of_neg [Finite {i // p i}] (hA : ∀ i, IsOpen (A i))
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, A i]) {i : ι} (h : ¬ p i) :
    (splitFiniteHomeomorph R p hA).symm z i = z.2 ⟨i, h⟩ :=
  glueSubtype_apply_of_neg R A p _ _ h

end Topology

section Group

variable {S : ι → Type*} [Π i, SetLike (S i) (R i)] (B : Π i, S i)
variable [Π i, Monoid (R i)] [∀ i, SubmonoidClass (S i) (R i)]
variable (p : ι → Prop) [DecidablePred p]

/-- Splitting along `p` as a multiplicative isomorphism. -/
def splitMulEquiv :
    Πʳ i, [R i, B i] ≃* Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i] where
  toEquiv := splitEquiv R (fun i => (B i : Set (R i))) p
  map_mul' _ _ := rfl

@[simp]
theorem splitMulEquiv_apply_fst (x : Πʳ i, [R i, B i]) (i : {i // p i}) :
    (splitMulEquiv R B p x).1 i = x i :=
  rfl

@[simp]
theorem splitMulEquiv_apply_snd (x : Πʳ i, [R i, B i]) (i : {i // ¬ p i}) :
    (splitMulEquiv R B p x).2 i = x i :=
  rfl

variable [∀ i, TopologicalSpace (R i)]

/-- If every subgroup is open, splitting along `p` is an isomorphism of topological groups. -/
def splitContinuousMulEquiv (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Πʳ i, [R i, B i] ≃ₜ* Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i] where
  toMulEquiv := splitMulEquiv R B p
  continuous_toFun := (splitHomeomorph R p hB).continuous
  continuous_invFun := (splitHomeomorph R p hB).symm.continuous

@[simp]
theorem splitContinuousMulEquiv_apply_fst (hB : ∀ i, IsOpen (B i : Set (R i)))
    (x : Πʳ i, [R i, B i]) (i : {i // p i}) :
    (splitContinuousMulEquiv R B p hB x).1 i = x i :=
  rfl

@[simp]
theorem splitContinuousMulEquiv_apply_snd (hB : ∀ i, IsOpen (B i : Set (R i)))
    (x : Πʳ i, [R i, B i]) (i : {i // ¬ p i}) :
    (splitContinuousMulEquiv R B p hB x).2 i = x i :=
  rfl

theorem splitContinuousMulEquiv_symm_apply_of_pos (hB : ∀ i, IsOpen (B i : Set (R i)))
    (z : Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι}
    (h : p i) : (splitContinuousMulEquiv R B p hB).symm z i = z.1 ⟨i, h⟩ :=
  glueSubtype_apply_of_pos R (fun i => (B i : Set (R i))) p z.1 z.2 h

theorem splitContinuousMulEquiv_symm_apply_of_neg (hB : ∀ i, IsOpen (B i : Set (R i)))
    (z : Πʳ (i : {i // p i}), [R i, B i] × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι}
    (h : ¬ p i) : (splitContinuousMulEquiv R B p hB).symm z i = z.2 ⟨i, h⟩ :=
  glueSubtype_apply_of_neg R (fun i => (B i : Set (R i))) p z.1 z.2 h

/-- Over a finite index type the cofinite restricted product of monoids is the full product,
as topological monoids. -/
def finiteContinuousMulEquiv [Finite ι] : Πʳ i, [R i, B i] ≃ₜ* Π i, R i where
  toMulEquiv :=
    { toEquiv := (finiteHomeomorph R (fun i => (B i : Set (R i)))).toEquiv
      map_mul' _ _ := rfl }
  continuous_toFun := (finiteHomeomorph R _).continuous
  continuous_invFun := (finiteHomeomorph R _).symm.continuous

@[simp]
theorem finiteContinuousMulEquiv_apply [Finite ι] (x : Πʳ i, [R i, B i]) (i : ι) :
    finiteContinuousMulEquiv R B x i = x i :=
  rfl

@[simp]
theorem finiteContinuousMulEquiv_symm_apply [Finite ι] (x : Π i, R i) (i : ι) :
    (finiteContinuousMulEquiv R B).symm x i = x i :=
  rfl

/-- If every subgroup is open and only finitely many indices satisfy `p`, the cofinite
restricted product is, as a topological monoid, the full product over `{i // p i}` times the
cofinite restricted product over `{i // ¬ p i}`. -/
def splitFiniteContinuousMulEquiv [Finite {i // p i}] (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Πʳ i, [R i, B i] ≃ₜ* (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i] where
  toMulEquiv :=
    { toEquiv := (splitFiniteHomeomorph R p hB).toEquiv
      map_mul' _ _ := rfl }
  continuous_toFun := (splitFiniteHomeomorph R p hB).continuous
  continuous_invFun := (splitFiniteHomeomorph R p hB).symm.continuous

@[simp]
theorem splitFiniteContinuousMulEquiv_apply_fst [Finite {i // p i}]
    (hB : ∀ i, IsOpen (B i : Set (R i))) (x : Πʳ i, [R i, B i]) (i : {i // p i}) :
    (splitFiniteContinuousMulEquiv R B p hB x).1 i = x i :=
  rfl

@[simp]
theorem splitFiniteContinuousMulEquiv_apply_snd [Finite {i // p i}]
    (hB : ∀ i, IsOpen (B i : Set (R i))) (x : Πʳ i, [R i, B i]) (i : {i // ¬ p i}) :
    (splitFiniteContinuousMulEquiv R B p hB x).2 i = x i :=
  rfl

theorem splitFiniteContinuousMulEquiv_symm_apply_of_pos [Finite {i // p i}]
    (hB : ∀ i, IsOpen (B i : Set (R i)))
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι} (h : p i) :
    (splitFiniteContinuousMulEquiv R B p hB).symm z i = z.1 ⟨i, h⟩ :=
  glueSubtype_apply_of_pos R (fun i => (B i : Set (R i))) p
    ((finiteHomeomorph _ _).symm z.1) z.2 h

theorem splitFiniteContinuousMulEquiv_symm_apply_of_neg [Finite {i // p i}]
    (hB : ∀ i, IsOpen (B i : Set (R i)))
    (z : (Π i : {i // p i}, R i) × Πʳ (i : {i // ¬ p i}), [R i, B i]) {i : ι} (h : ¬ p i) :
    (splitFiniteContinuousMulEquiv R B p hB).symm z i = z.2 ⟨i, h⟩ :=
  glueSubtype_apply_of_neg R (fun i => (B i : Set (R i))) p
    ((finiteHomeomorph _ _).symm z.1) z.2 h

end Group

end RestrictedProduct
