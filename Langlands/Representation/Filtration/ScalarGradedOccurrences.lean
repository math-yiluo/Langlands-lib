import Langlands.Representation.Filtration.Definitions
import Mathlib.RepresentationTheory.Irreducible

/-! # A character met by a subrepresentation and by its quotient occurs in two grades

Let a representation carry a finite filtration whose successive quotients are irreducible or
zero, and on each of which a family of operators acts by scalars. If a subrepresentation has a
uniform generalized eigenvector for a family of eigenvalues, and the quotient by it has one
too, then two distinct nonzero grades carry these scalars. The lemma serves the comparison
of the exponents of the two constituents of an induced representation in the proof of
Renard VII.1.3, applied to the filtration of the geometric lemma; it is internal.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uK uG uB uV uW uR uC vC

namespace ScalarGraded

variable {k : Type uK} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]

/-- In a finite chain of propositions that is false at the start and true at the end, some
consecutive pair goes from false to true. -/
theorem exists_step {n : ℕ} (P : Fin (n + 1) → Prop) (h0 : ¬ P 0) (hn : P (Fin.last n)) :
    ∃ i : Fin n, ¬ P i.castSucc ∧ P i.succ := by
  by_contra h
  push Not at h
  have hall : ∀ j : Fin (n + 1), ¬ P j := by
    intro j
    induction j using Fin.induction with
    | zero => exact h0
    | succ i ih => exact h i ih
  exact hall _ hn

/-- Polynomials in an operator preserve an invariant submodule. -/
theorem pow_sub_smul_apply_mem (T : Submodule k V) (f : Module.End k V)
    (hT : ∀ x ∈ T, f x ∈ T) (b : k) (m : ℕ) {x : V} (hx : x ∈ T) :
    ((f - b • 1) ^ m) x ∈ T := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact T.sub_mem (hT _ ih) (T.smul_mem b ih)

/-- If `f` acts on `T` by the scalar `c` modulo `S`, then `(f - b)^m` acts on `T` by
`(c - b)^m` modulo `S`. -/
theorem pow_sub_smul_apply_sub_mem (S T : Submodule k V) (f : Module.End k V)
    (hT : ∀ x ∈ T, f x ∈ T) (c b : k) (hscal : ∀ x ∈ T, f x - c • x ∈ S) (m : ℕ)
    {x : V} (hx : x ∈ T) :
    ((f - b • 1) ^ m) x - (c - b) ^ m • x ∈ S := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hy := pow_sub_smul_apply_mem T f hT b m hx
    have key : ((f - b • 1) ^ (m + 1)) x - (c - b) ^ (m + 1) • x =
        (f (((f - b • 1) ^ m) x) - c • ((f - b • 1) ^ m) x) +
          (c - b) • (((f - b • 1) ^ m) x - (c - b) ^ m • x) := by
      rw [pow_succ', Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, pow_succ']
      module
    rw [key]
    exact S.add_mem (hscal _ hy) (S.smul_mem _ ih)

/-- A nonzero uniform generalized eigenvector lies in some grade whose scalars are the
eigenvalues. -/
theorem exists_grade_of_pow_apply_eq_zero {B : Type uB} {n : ℕ} (F : Fin (n + 1) → Submodule k V)
    (h0 : F 0 = ⊥) (hn : F (Fin.last n) = ⊤) (f : B → Module.End k V)
    (hT : ∀ (i : Fin n) t, ∀ x ∈ F i.succ, f t x ∈ F i.succ) (c : Fin n → B → k)
    (hscal : ∀ (i : Fin n) t, ∀ x ∈ F i.succ, f t x - c i t • x ∈ F i.castSucc)
    (χ : B → k) (d : ℕ) {v : V} (hv : v ≠ 0) (hgen : ∀ t, ((f t - χ t • 1) ^ d) v = 0) :
    ∃ i : Fin n, v ∈ F i.succ ∧ v ∉ F i.castSucc ∧ c i = χ := by
  obtain ⟨i, hi0, hi1⟩ := exists_step (fun j => v ∈ F j)
    (by simpa only [h0, Submodule.mem_bot] using hv) (by simp only [hn, Submodule.mem_top])
  refine ⟨i, hi1, hi0, funext fun t => ?_⟩
  by_contra hne
  have hmem := pow_sub_smul_apply_sub_mem (F i.castSucc) (F i.succ) (f t) (hT i t) (c i t) (χ t)
    (hscal i t) d hi1
  rw [hgen t, zero_sub, neg_mem_iff] at hmem
  have hpow : (c i t - χ t) ^ d ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
  apply hi0
  simpa only [smul_smul, inv_mul_cancel₀ hpow, one_smul] using
    (F i.castSucc).smul_mem ((c i t - χ t) ^ d)⁻¹ hmem

/-- A vector outside an invariant submodule `E` that is a uniform generalized eigenvector
modulo `E` gives a grade whose scalars are the eigenvalues, and which is not covered by `E`
together with the lower step. -/
theorem exists_grade_of_pow_apply_mem {B : Type uB} {n : ℕ} (F : Fin (n + 1) → Submodule k V)
    (h0 : F 0 = ⊥) (hn : F (Fin.last n) = ⊤) (f : B → Module.End k V)
    (hT : ∀ (i : Fin n) t, ∀ x ∈ F i.succ, f t x ∈ F i.succ) (c : Fin n → B → k)
    (hscal : ∀ (i : Fin n) t, ∀ x ∈ F i.succ, f t x - c i t • x ∈ F i.castSucc)
    (E : Submodule k V) (hE : ∀ t, ∀ x ∈ E, f t x ∈ E) (χ : B → k) (d : ℕ) {w : V}
    (hw : w ∉ E) (hgen : ∀ t, ((f t - χ t • 1) ^ d) w ∈ E) :
    ∃ j : Fin n, c j = χ ∧ ∃ u ∈ F j.succ, u ∉ F j.castSucc ⊔ E := by
  obtain ⟨j, hj0, hj1⟩ := exists_step (fun j => w ∈ F j ⊔ E)
    (by simpa only [h0, bot_sup_eq] using hw) (by simp only [hn, top_sup_eq, Submodule.mem_top])
  obtain ⟨u, hu, e, he, rfl⟩ := Submodule.mem_sup.mp hj1
  have hu' : u ∉ F j.castSucc ⊔ E := by
    intro h
    exact hj0 (Submodule.add_mem _ h (Submodule.mem_sup_right he))
  refine ⟨j, funext fun t => ?_, u, hu, hu'⟩
  by_contra hne
  have hmem := pow_sub_smul_apply_sub_mem (F j.castSucc) (F j.succ) (f t) (hT j t) (c j t) (χ t)
    (hscal j t) d hu
  have hE' : ((f t - χ t • 1) ^ d) u ∈ E := by
    have h1 := hgen t
    have h2 := pow_sub_smul_apply_mem E (f t) (hE t) (χ t) d he
    rw [map_add] at h1
    simpa only [add_sub_cancel_right] using E.sub_mem h1 h2
  have hsmul : (c j t - χ t) ^ d • u ∈ F j.castSucc ⊔ E := by
    have h := (F j.castSucc ⊔ E).sub_mem (Submodule.mem_sup_right hE')
      (Submodule.mem_sup_left hmem)
    simpa only [sub_sub_cancel] using h
  have hpow : (c j t - χ t) ^ d ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hne)
  apply hu'
  simpa only [smul_smul, inv_mul_cancel₀ hpow, one_smul] using
    (F j.castSucc ⊔ E).smul_mem ((c j t - χ t) ^ d)⁻¹ hsmul

variable {G : Type uG} [Monoid G] {ρ : Representation k G V}

/-- Two scalar grades. Let `F` be a finite filtration of `ρ` by subrepresentations with no
subrepresentation strictly between consecutive steps, on whose successive quotients each
`ρ (ι t)` acts by the scalar `c i t`. If a subrepresentation `E` contains a nonzero uniform
generalized eigenvector with eigenvalues `χ`, and some vector outside `E` is a uniform
generalized eigenvector with eigenvalues `χ` modulo `E`, then two distinct nonzero grades
have scalars `χ`. -/
theorem exists_two_grades {B : Type uB} {n : ℕ} (F : Fin (n + 1) → Subrepresentation ρ)
    (h0 : F 0 = ⊥) (hn : F (Fin.last n) = ⊤) (hmono : ∀ i : Fin n, F i.castSucc ≤ F i.succ)
    (ι : B → G) (c : Fin n → B → k)
    (hscal : ∀ (i : Fin n) t, ∀ x ∈ F i.succ, ρ (ι t) x - c i t • x ∈ F i.castSucc)
    (hmax : ∀ (i : Fin n) (S : Subrepresentation ρ), F i.castSucc ≤ S → S ≤ F i.succ →
      S = F i.castSucc ∨ S = F i.succ)
    (E : Subrepresentation ρ) (χ : B → k) {d d' : ℕ}
    {v : V} (hv : v ≠ 0) (hvE : v ∈ E) (hgen : ∀ t, ((ρ (ι t) - χ t • 1) ^ d) v = 0)
    {w : V} (hw : w ∉ E) (hgen' : ∀ t, ((ρ (ι t) - χ t • 1) ^ d') w ∈ E) :
    ∃ i j : Fin n, i ≠ j ∧ c i = χ ∧ c j = χ ∧ F i.castSucc ≠ F i.succ ∧
      F j.castSucc ≠ F j.succ := by
  have h0' : (F 0).toSubmodule = ⊥ := by rw [h0]; rfl
  have hn' : (F (Fin.last n)).toSubmodule = ⊤ := by rw [hn]; rfl
  have hT : ∀ (i : Fin n) t, ∀ x ∈ (F i.succ).toSubmodule, ρ (ι t) x ∈ (F i.succ).toSubmodule :=
    fun i t x hx => (F i.succ).apply_mem_toSubmodule (ι t) hx
  obtain ⟨i, hi1, hi0, hci⟩ := exists_grade_of_pow_apply_eq_zero (fun j => (F j).toSubmodule)
    h0' hn' (fun t => ρ (ι t)) hT c hscal χ d hv hgen
  obtain ⟨j, hcj, u, hu, hu'⟩ := exists_grade_of_pow_apply_mem (fun j => (F j).toSubmodule)
    h0' hn' (fun t => ρ (ι t)) hT c hscal E.toSubmodule
    (fun t x hx => E.apply_mem_toSubmodule (ι t) hx) χ d' hw hgen'
  have hij : i ≠ j := by
    rintro rfl
    rcases hmax i (F i.castSucc ⊔ (E ⊓ F i.succ)) le_sup_left
        (sup_le (hmono i) inf_le_right) with h | h
    · apply hi0
      have hvS : v ∈ F i.castSucc ⊔ (E ⊓ F i.succ) :=
        (le_sup_right : E ⊓ F i.succ ≤ _) ⟨hvE, hi1⟩
      rw [h] at hvS
      exact hvS
    · apply hu'
      have huS : u ∈ F i.succ := hu
      rw [← h] at huS
      exact (sup_le_sup_left inf_le_left _ : F i.castSucc ⊔ (E ⊓ F i.succ) ≤
        F i.castSucc ⊔ E) huS
  refine ⟨i, j, hij, hci, hcj, ?_, ?_⟩
  · intro h
    apply hi0
    change v ∈ F i.castSucc
    rw [h]
    exact hi1
  · intro h
    apply hu'
    have huF : u ∈ F j.castSucc := by rw [h]; exact hu
    exact Submodule.mem_sup_left huF

section Quotient

variable {W : Type uW} [AddCommGroup W] [Module k W] {σ : Representation k G W}

/-- If `π` maps the subrepresentation `T` to `σ` with kernel `S`, and `ρ g` acts on `σ` by
the scalar `c`, then `ρ g` acts on `T` by `c` modulo `S`. -/
theorem apply_sub_smul_mem_of_intertwiningMap (S T : Subrepresentation ρ)
    (π : T.toRepresentation.IntertwiningMap σ)
    (hker : ∀ x : T.toSubmodule, π x = 0 ↔ (x : V) ∈ S) (g : G) (c : k)
    (hσ : ∀ y, σ g y = c • y) {x : V} (hx : x ∈ T) : ρ g x - c • x ∈ S := by
  have hgx : ρ g x ∈ T.toSubmodule := T.apply_mem_toSubmodule g hx
  have h := (hker (⟨ρ g x, hgx⟩ - c • ⟨x, hx⟩)).mp (by
    rw [map_sub, map_smul]
    have h1 : (⟨ρ g x, hgx⟩ : T.toSubmodule) = T.toRepresentation g ⟨x, hx⟩ := rfl
    rw [h1, Representation.IntertwiningMap.isIntertwining _ _ π, hσ, sub_self])
  simpa using h

/-- If `π` maps the subrepresentation `T ≥ S` to a zero or irreducible `σ` with kernel `S`,
then no subrepresentation lies strictly between `S` and `T`. -/
theorem eq_or_eq_of_intertwiningMap (S T : Subrepresentation ρ)
    (π : T.toRepresentation.IntertwiningMap σ)
    (hker : ∀ x : T.toSubmodule, π x = 0 ↔ (x : V) ∈ S)
    (hσ : Subsingleton W ∨ Representation.IsIrreducible σ) (U : Subrepresentation ρ) (hSU : S ≤ U)
    (hUT : U ≤ T) : U = S ∨ U = T := by
  let I : Subrepresentation σ :=
    { toSubmodule := (U.toSubmodule.comap T.toSubmodule.subtype).map π.toLinearMap
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, hx, rfl⟩
        exact ⟨T.toRepresentation g x, U.apply_mem_toSubmodule g hx,
          Representation.IntertwiningMap.isIntertwining _ _ π g x⟩ }
  have hbot : I = ⊥ → U = S := by
    intro h
    refine le_antisymm (fun x hx => ?_) hSU
    have hxI : π ⟨x, hUT hx⟩ ∈ I := ⟨⟨x, hUT hx⟩, hx, rfl⟩
    rw [h] at hxI
    exact (hker _).mp ((Submodule.mem_bot k).mp hxI)
  have htop : I = ⊤ → U = T := by
    intro h
    refine le_antisymm hUT (fun x hx => ?_)
    have hxI : π ⟨x, hx⟩ ∈ I := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, hxy⟩ := hxI
    have hxy' : π y = π ⟨x, hx⟩ := hxy
    have hd : ((⟨x, hx⟩ - y : T.toSubmodule) : V) ∈ S :=
      (hker _).mp (by rw [map_sub, hxy', sub_self])
    have hU := U.toSubmodule.add_mem (hSU hd) hy
    have : x ∈ U.toSubmodule := by simpa using hU
    exact this
  rcases hσ with hs | hirr
  · refine Or.inl (hbot ?_)
    apply Subrepresentation.toSubmodule_injective
    ext y
    rw [Subsingleton.elim y 0]
    exact iff_of_true (Submodule.zero_mem _) (Submodule.zero_mem _)
  · have := hirr
    rcases IsSimpleOrder.eq_bot_or_eq_top I with h | h
    · exact Or.inl (hbot h)
    · exact Or.inr (htop h)

end Quotient

/-- Each member of a finite family of representations is zero, or irreducible with every
`ι t` acting by the scalar `c i t`. -/
def ZeroOrScalarIrreducible {k : Type uK} [Field k] {G : Type uG} [Monoid G] {B : Type uB}
    {n : ℕ} (R : Fin n → Rep.{uV} k G) (ι : B → G) (c : Fin n → B → k) : Prop :=
  ∀ i, Subsingleton (R i) ∨
    (Representation.IsIrreducible (R i).ρ ∧ ∀ t (y : R i), (R i).ρ (ι t) y = c i t • y)

end ScalarGraded

namespace RepFunctorFiltration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {C : Type uC} [Category.{vC} C]
  {F : C ⥤ Rep.{uV} k G} {n : ℕ}

/-- The projection of the `i.succ`-th step at `X` onto a model `R` of the `i`-th graded
piece. -/
def gradedModelProjection (s : RepFunctorFiltration F n) (X : C) (i : Fin n) {R : Rep.{uV} k G}
    (e : (s.graded i).obj X ≅ R) :
    ((s.step i.succ).obj X).toRepresentation.IntertwiningMap R.ρ :=
  ((s.step i.castSucc).quotientProjection (s.step i.succ) X ≫ e.hom).hom

/-- The kernel of the graded projection is the lower step. -/
theorem gradedModelProjection_eq_zero_iff (s : RepFunctorFiltration F n) (X : C) (i : Fin n)
    {R : Rep.{uV} k G} (e : (s.graded i).obj X ≅ R) (x : ((s.step i.succ).obj X).toSubmodule) :
    s.gradedModelProjection X i e x = 0 ↔ (x : F.obj X) ∈ (s.step i.castSucc).obj X := by
  have hq : ((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom x = 0 ↔
      (x : F.obj X) ∈ (s.step i.castSucc).obj X :=
    Submodule.Quotient.mk_eq_zero _
  constructor
  · intro h
    have h' : e.inv.hom (s.gradedModelProjection X i e x) = 0 := by rw [h, map_zero]
    exact hq.mp ((Rep.inv_hom_apply (e := e) (x :=
      ((s.step i.castSucc).quotientProjection (s.step i.succ) X).hom x)).symm.trans h')
  · intro h
    exact (congrArg e.hom.hom (hq.mpr h)).trans (map_zero _)

/-- A vector of the upper step outside the lower step makes the graded piece nonzero. -/
theorem nontrivial_of_mem_of_notMem (s : RepFunctorFiltration F n) (X : C) (i : Fin n)
    {R : Rep.{uV} k G} (e : (s.graded i).obj X ≅ R) {x : F.obj X}
    (hx : x ∈ (s.step i.succ).obj X) (hx' : x ∉ (s.step i.castSucc).obj X) : Nontrivial R :=
  nontrivial_of_ne (s.gradedModelProjection X i e ⟨x, hx⟩) 0
    fun h => hx' ((s.gradedModelProjection_eq_zero_iff X i e _).mp h)

/-- Distinct consecutive steps make the graded piece nonzero. -/
theorem nontrivial_of_ne (s : RepFunctorFiltration F n) (X : C) (i : Fin n)
    {R : Rep.{uV} k G} (e : (s.graded i).obj X ≅ R)
    (h : (s.step i.castSucc).obj X ≠ (s.step i.succ).obj X) : Nontrivial R := by
  by_contra hR
  rw [not_nontrivial_iff_subsingleton] at hR
  exact h (le_antisymm (s.step_le_next X i) fun x hx =>
    (s.gradedModelProjection_eq_zero_iff X i e ⟨x, hx⟩).mp (Subsingleton.elim _ _))

/-- If `g` acts on the graded piece by the scalar `c`, it acts on the upper step by `c` modulo
the lower step. -/
theorem apply_sub_smul_mem (s : RepFunctorFiltration F n) (X : C) (i : Fin n)
    {R : Rep.{uV} k G} (e : (s.graded i).obj X ≅ R) (g : G) (c : k)
    (hR : ∀ y : R, R.ρ g y = c • y) {x : F.obj X} (hx : x ∈ (s.step i.succ).obj X) :
    (F.obj X).ρ g x - c • x ∈ (s.step i.castSucc).obj X :=
  ScalarGraded.apply_sub_smul_mem_of_intertwiningMap _ _ (s.gradedModelProjection X i e)
    (s.gradedModelProjection_eq_zero_iff X i e) g c hR hx

/-- A zero or irreducible graded piece leaves no subrepresentation strictly between the two
steps. -/
theorem eq_or_eq_of_le (s : RepFunctorFiltration F n) (X : C) (i : Fin n)
    {R : Rep.{uV} k G} (e : (s.graded i).obj X ≅ R)
    (hR : Subsingleton R ∨ Representation.IsIrreducible R.ρ) (U : Subrepresentation (F.obj X).ρ)
    (hSU : (s.step i.castSucc).obj X ≤ U) (hUT : U ≤ (s.step i.succ).obj X) :
    U = (s.step i.castSucc).obj X ∨ U = (s.step i.succ).obj X :=
  ScalarGraded.eq_or_eq_of_intertwiningMap _ _ (s.gradedModelProjection X i e)
    (s.gradedModelProjection_eq_zero_iff X i e) hR U hSU hUT

variable {B : Type uB}

theorem apply_sub_smul_mem_of_zeroOrScalarIrreducible (s : RepFunctorFiltration F n) (X : C)
    {R : Fin n → Rep.{uV} k G} (e : ∀ i, (s.graded i).obj X ≅ R i) {ι : B → G}
    {c : Fin n → B → k} (hR : ScalarGraded.ZeroOrScalarIrreducible R ι c) (i : Fin n) (t : B)
    {x : F.obj X} (hx : x ∈ (s.step i.succ).obj X) :
    (F.obj X).ρ (ι t) x - c i t • x ∈ (s.step i.castSucc).obj X := by
  refine s.apply_sub_smul_mem X i (e i) (ι t) (c i t) (fun y => ?_) hx
  rcases hR i with h | h
  · exact Subsingleton.elim _ _
  · exact h.2 t y

/-- A nonzero uniform generalized eigenvector with eigenvalues `χ` gives a nonzero graded
piece on which `ι` acts by `χ`. -/
theorem exists_grade_of_pow_apply_eq_zero (s : RepFunctorFiltration F n) (X : C)
    {R : Fin n → Rep.{uV} k G} (e : ∀ i, (s.graded i).obj X ≅ R i) {ι : B → G}
    {c : Fin n → B → k} (hR : ScalarGraded.ZeroOrScalarIrreducible R ι c) (χ : B → k) (d : ℕ)
    {v : F.obj X} (hv : v ≠ 0) (hgen : ∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d) v = 0) :
    ∃ i, Nontrivial (R i) ∧ c i = χ := by
  have h0 : ((s.step 0).obj X).toSubmodule = ⊥ := by rw [s.zero X]; rfl
  have hn : ((s.step (Fin.last n)).obj X).toSubmodule = ⊤ := by rw [s.top X]; rfl
  obtain ⟨i, hi1, hi0, hci⟩ := ScalarGraded.exists_grade_of_pow_apply_eq_zero
    (fun j => ((s.step j).obj X).toSubmodule) h0 hn (fun t => (F.obj X).ρ (ι t))
    (fun i t x hx => ((s.step i.succ).obj X).apply_mem_toSubmodule (ι t) hx) c
    (fun i t x hx => s.apply_sub_smul_mem_of_zeroOrScalarIrreducible X e hR i t hx) χ d hv hgen
  exact ⟨i, s.nontrivial_of_mem_of_notMem X i (e i) hi1 hi0, hci⟩

/-- A vector outside a subrepresentation `E` that is a uniform generalized eigenvector with
eigenvalues `χ` modulo `E` gives a nonzero graded piece on which `ι` acts by `χ`. -/
theorem exists_grade_of_pow_apply_mem (s : RepFunctorFiltration F n) (X : C)
    {R : Fin n → Rep.{uV} k G} (e : ∀ i, (s.graded i).obj X ≅ R i) {ι : B → G}
    {c : Fin n → B → k} (hR : ScalarGraded.ZeroOrScalarIrreducible R ι c)
    (E : Subrepresentation (F.obj X).ρ) (χ : B → k) (d : ℕ) {w : F.obj X} (hw : w ∉ E)
    (hgen : ∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d) w ∈ E) :
    ∃ i, Nontrivial (R i) ∧ c i = χ := by
  have h0 : ((s.step 0).obj X).toSubmodule = ⊥ := by rw [s.zero X]; rfl
  have hn : ((s.step (Fin.last n)).obj X).toSubmodule = ⊤ := by rw [s.top X]; rfl
  obtain ⟨j, hcj, u, hu, hu'⟩ := ScalarGraded.exists_grade_of_pow_apply_mem
    (fun j => ((s.step j).obj X).toSubmodule) h0 hn (fun t => (F.obj X).ρ (ι t))
    (fun i t x hx => ((s.step i.succ).obj X).apply_mem_toSubmodule (ι t) hx) c
    (fun i t x hx => s.apply_sub_smul_mem_of_zeroOrScalarIrreducible X e hR i t hx)
    E.toSubmodule (fun t x hx => E.apply_mem_toSubmodule (ι t) hx) χ d hw hgen
  exact ⟨j, s.nontrivial_of_mem_of_notMem X j (e j) hu
    fun h => hu' (Submodule.mem_sup_left h), hcj⟩

/-- Two scalar grades. If a subrepresentation `E` contains a nonzero uniform generalized
eigenvector with eigenvalues `χ`, and some vector outside `E` is one modulo `E`, then two
distinct nonzero graded pieces carry the scalars `χ`. -/
theorem exists_two_grades (s : RepFunctorFiltration F n) (X : C)
    {R : Fin n → Rep.{uV} k G} (e : ∀ i, (s.graded i).obj X ≅ R i) {ι : B → G}
    {c : Fin n → B → k} (hR : ScalarGraded.ZeroOrScalarIrreducible R ι c)
    (E : Subrepresentation (F.obj X).ρ) (χ : B → k) {d d' : ℕ} {v : F.obj X} (hv : v ≠ 0)
    (hvE : v ∈ E) (hgen : ∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d) v = 0) {w : F.obj X}
    (hw : w ∉ E) (hgen' : ∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d') w ∈ E) :
    ∃ i j, i ≠ j ∧ Nontrivial (R i) ∧ Nontrivial (R j) ∧ c i = χ ∧ c j = χ := by
  obtain ⟨i, j, hij, hci, hcj, hi, hj⟩ := ScalarGraded.exists_two_grades
    (fun j => (s.step j).obj X) (s.zero X) (s.top X) (s.step_le_next X) ι c
    (fun i t x hx => s.apply_sub_smul_mem_of_zeroOrScalarIrreducible X e hR i t hx)
    (fun i U hSU hUT => s.eq_or_eq_of_le X i (e i) ((hR i).imp id And.left) U hSU hUT)
    E χ hv hvE hgen hw hgen'
  exact ⟨i, j, hij, s.nontrivial_of_ne X i (e i) hi, s.nontrivial_of_ne X j (e j) hj, hci, hcj⟩

end RepFunctorFiltration

/-- The two-grade lemma for a natural finite filtration of representation-valued functors,
at one object `X`: when every graded piece at `X` is zero, or irreducible with each `ι t`
acting by the scalar `c i t`, a subrepresentation `E` containing a nonzero uniform
generalized eigenvector with eigenvalues `χ`, together with a vector outside `E` that is one
modulo `E`, forces two distinct nonzero graded pieces with scalars `χ`. -/
def TwoScalarGradesStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G] (C : Type uC) [Category.{vC} C]
    (F : C ⥤ Rep.{uV} k G) (n : ℕ) (s : RepFunctorFiltration F n) (X : C)
    (R : Fin n → Rep.{uV} k G) (_e : ∀ i, (s.graded i).obj X ≅ R i) (B : Type uB)
    (ι : B → G) (c : Fin n → B → k), ScalarGraded.ZeroOrScalarIrreducible R ι c →
    ∀ (E : Subrepresentation (F.obj X).ρ) (χ : B → k) (d d' : ℕ) (v w : F.obj X),
      v ≠ 0 → v ∈ E → (∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d) v = 0) → w ∉ E →
      (∀ t, (((F.obj X).ρ (ι t) - χ t • 1) ^ d') w ∈ E) →
      ∃ i j, i ≠ j ∧ Nontrivial (R i) ∧ Nontrivial (R j) ∧ c i = χ ∧ c j = χ

theorem twoScalarGrades : TwoScalarGradesStatement.{uK, uG, uB, uV, uC, vC} := by
  intro k _ G _ C _ F n s X R e B ι c hR E χ d d' v w hv hvE hgen hw hgen'
  exact s.exists_two_grades X e hR E χ hv hvE hgen hw hgen'

end Langlands
