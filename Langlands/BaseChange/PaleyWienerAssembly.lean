import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# The inductive assembly of the trace Paley–Wiener theorem

The proof of the trace Paley–Wiener theorem in Bernstein–Deligne–Kazhdan (1986), §4.3, and its
twisted form in Rogawski (1988), Proposition 11.2, is an induction over standard Levi subgroups.
This module isolates the linear algebra of that induction for an abstract well-founded system of
test-function spaces, distributions, induction maps and Jacquet lifts. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.PaleyWienerAssembly

open Module

universe uι uL uS

variable {ι : Type uι} {Lev : ι → Type uL} {S : ι → Type uS}
  [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]

/-- The span of the induced distributions `θ' ∘ CT_l` of the distributions `θ'` of `Irr` on the
Levis `l` of `i`, where `CT_l` is the test-function map whose transpose realizes induction. -/
def inducedSpan (tgt : ∀ i, Lev i → ι) (Irr : ∀ i, Set (Dual ℂ (S i)))
    (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l)) (i : ι) : Submodule ℂ (Dual ℂ (S i)) :=
  Submodule.span ℂ (⋃ l : Lev i, Dual.transpose (R := ℂ) (CT i l) '' Irr (tgt i l))

/-- The operator `x ↦ x ∘ L_l ∘ CT_l` on distributions: restriction to the Levi `l` (transpose of
the lift `L_l`) followed by induction (transpose of `CT_l`). -/
def descent (tgt : ∀ i, Lev i → ι) (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l))
    (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i) (i : ι) (l : Lev i) :
    Dual ℂ (S i) →ₗ[ℂ] Dual ℂ (S i) :=
  Dual.transpose (R := ℂ) (L i l ∘ₗ CT i l)

omit [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] in
@[simp]
theorem descent_apply [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (tgt : ∀ i, Lev i → ι) (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l))
    (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i) (i : ι) (l : Lev i) (x : Dual ℂ (S i))
    (s : S i) : descent tgt CT L i l x s = x (L i l (CT i l s)) :=
  rfl

/-- Abstract trace Paley–Wiener assembly, modeled on Bernstein–Deligne–Kazhdan (1986), §4.3,
where `hA4` interpolates every good form on the discrete part. Let `r` be a well-founded relation on an index set of groups, each
`i` with Levis `l : Lev i` indexed by `tgt i l`, strictly `r`-below `i`. Suppose:

* `hA1`: every irreducible distribution lies in `Disc i ⊔ inducedSpan i`;
* `hA2`: each operator `descent l` preserves `Disc i`;
* `hA3`: on `inducedSpan i`, `x = ∑ₗ c l • descent l x` (the combinatorial lemma);
* `hA4`: every good functional agrees with evaluation at a test on `Disc i`;
* `hA5`: composing a good functional with induction `θ' ↦ θ' ∘ CT_l` gives a good functional;
* `hA6`: restricting an irreducible distribution to a Levi, `θ ↦ θ ∘ L_l`, lands in the span of
  the irreducible distributions of the Levi.

Then every good functional agrees with evaluation at a test on all irreducible distributions.
The Lean name of a hypothesis matches its number in the paired Markdown. -/
theorem exists_eq_eval_of_good (r : ι → ι → Prop) (hwf : WellFounded r)
    (tgt : ∀ i, Lev i → ι) (htgt : ∀ i l, r (tgt i l) i)
    (Irr : ∀ i, Set (Dual ℂ (S i))) (Good : ∀ i, Set (Dual ℂ (Dual ℂ (S i))))
    (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l)) (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i)
    (c : ∀ i, Lev i →₀ ℂ) (Disc : ∀ i, Submodule ℂ (Dual ℂ (S i)))
    (hA1 : ∀ i, ∀ θ ∈ Irr i, θ ∈ Disc i ⊔ inducedSpan tgt Irr CT i)
    (hA2 : ∀ i l, ∀ x ∈ Disc i, descent tgt CT L i l x ∈ Disc i)
    (hA3 : ∀ i, ∀ x ∈ inducedSpan tgt Irr CT i,
      x = (c i).sum fun l a => a • descent tgt CT L i l x)
    (hA4 : ∀ i, ∀ Φ ∈ Good i, ∃ s : S i, ∀ x ∈ Disc i, Φ x = x s)
    (hA5 : ∀ i l, ∀ Φ ∈ Good i, Φ ∘ₗ Dual.transpose (R := ℂ) (CT i l) ∈ Good (tgt i l))
    (hA6 : ∀ i l, ∀ θ ∈ Irr i, θ ∘ₗ L i l ∈ Submodule.span ℂ (Irr (tgt i l))) :
    ∀ i, ∀ Φ ∈ Good i, ∃ s : S i, ∀ θ ∈ Irr i, Φ θ = θ s := by
  intro i
  induction i using hwf.induction with
  | h i ih =>
  intro Φ hΦ
  obtain ⟨s₁, hs₁⟩ := hA4 i Φ hΦ
  choose sl hsl using fun l : Lev i =>
    ih (tgt i l) (htgt i l) _ (hA5 i l Φ hΦ)
  -- The functional with the discrete part removed.
  set Φ' : Dual ℂ (Dual ℂ (S i)) := Φ - Dual.eval ℂ (S i) s₁ with hΦ'
  have hF1 : ∀ x ∈ Disc i, Φ' x = 0 := by
    intro x hx
    simp [hΦ', hs₁ x hx]
  have hF2 : ∀ l, ∀ y ∈ Submodule.span ℂ (Irr (tgt i l)),
      Φ' (Dual.transpose (R := ℂ) (CT i l) y) = y (sl l - CT i l s₁) := by
    intro l y hy
    have hEq : Set.EqOn (Φ' ∘ₗ Dual.transpose (R := ℂ) (CT i l))
        (Dual.eval ℂ (S (tgt i l)) (sl l - CT i l s₁)) (Irr (tgt i l)) := by
      intro θ' hθ'
      have h := hsl l θ' hθ'
      simp only [LinearMap.comp_apply, Dual.transpose_apply] at h
      simp [hΦ', h, Dual.transpose_apply, map_sub]
    exact LinearMap.eqOn_span hEq hy
  have hF3 : ∀ θ ∈ Irr i,
      Φ' θ = (c i).sum fun l a => a * Φ' (descent tgt CT L i l θ) := by
    intro θ hθ
    obtain ⟨d, hd, x, hx, rfl⟩ := Submodule.mem_sup.1 (hA1 i θ hθ)
    have hdx : ∀ l, Φ' (descent tgt CT L i l (d + x)) = Φ' (descent tgt CT L i l x) := by
      intro l
      rw [map_add, map_add, hF1 _ (hA2 i l d hd), zero_add]
    rw [map_add, hF1 d hd, zero_add]
    conv_lhs => rw [hA3 i x hx]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun l _ => ?_
    rw [map_smul, smul_eq_mul, hdx l]
  have hF4 : ∀ θ ∈ Irr i, ∀ l,
      Φ' (descent tgt CT L i l θ) = θ (L i l (sl l - CT i l s₁)) := by
    intro θ hθ l
    have h := hF2 l (θ ∘ₗ L i l) (hA6 i l θ hθ)
    simpa [descent, Dual.transpose_apply, LinearMap.comp_assoc] using h
  refine ⟨s₁ + (c i).sum fun l a => a • L i l (sl l - CT i l s₁), ?_⟩
  intro θ hθ
  have hΦθ : Φ θ = Φ' θ + θ s₁ := by
    simp [hΦ']
  rw [hΦθ, hF3 θ hθ, map_add, map_finsuppSum, add_comm]
  congr 1
  refine Finsupp.sum_congr fun l _ => ?_
  rw [hF4 θ hθ l, map_smul, smul_eq_mul]

omit [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] in
/-- Restriction to a Levi maps the span of the irreducible distributions into the span of the
irreducible distributions of the Levi, when it does so on the irreducible distributions. -/
theorem comp_mem_span_of_mem_span [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (Irr : ∀ i, Set (Dual ℂ (S i))) {i j : ι} (L : S j →ₗ[ℂ] S i)
    (hL : ∀ θ ∈ Irr i, θ ∘ₗ L ∈ Submodule.span ℂ (Irr j)) {x : Dual ℂ (S i)}
    (hx : x ∈ Submodule.span ℂ (Irr i)) : x ∘ₗ L ∈ Submodule.span ℂ (Irr j) := by
  have hle : Submodule.span ℂ (Irr i) ≤
      (Submodule.span ℂ (Irr j)).comap (Dual.transpose (R := ℂ) L) :=
    Submodule.span_le.2 fun θ hθ => by simpa [Dual.transpose_apply] using hL θ hθ
  simpa [Dual.transpose_apply] using hle hx

omit [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] in
/-- Inducing a distribution in the span of the irreducible distributions of a Levi gives an
element of `inducedSpan`. -/
theorem transpose_mem_inducedSpan [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (tgt : ∀ i, Lev i → ι) (Irr : ∀ i, Set (Dual ℂ (S i)))
    (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l)) (i : ι) (l : Lev i) {y : Dual ℂ (S (tgt i l))}
    (hy : y ∈ Submodule.span ℂ (Irr (tgt i l))) :
    Dual.transpose (R := ℂ) (CT i l) y ∈ inducedSpan tgt Irr CT i := by
  have hle : Submodule.span ℂ (Irr (tgt i l)) ≤
      (inducedSpan tgt Irr CT i).comap (Dual.transpose (R := ℂ) (CT i l)) :=
    Submodule.span_le.2 fun θ' hθ' => Submodule.subset_span
      (Set.mem_iUnion.2 ⟨l, Set.mem_image_of_mem _ hθ'⟩)
  exact hle hy

/-- Discrete trace Paley–Wiener from interpolation on the discrete part, without induction
over Levis (the step of Rogawski 1988, proof of Proposition 11.2, for discrete good forms; `Good`
may be taken to be the good forms vanishing on `inducedSpan i`). Let `Φ` be good and vanish on `inducedSpan i`. If every irreducible distribution
lies in `Disc i ⊔ inducedSpan i` (`hA1`), the operators `descent l` preserve `Disc i` (`hA2`), the
combinatorial identity `hA3` holds on `inducedSpan i`, good functionals agree with evaluations on
`Disc i` (`hA4`), restriction of irreducible distributions lands in the spans of the Levis
(`hA6`) and `Disc i` lies in the span of `Irr i` (`hA9`), then `Φ` agrees with evaluation at
`h - ∑ₗ c l • L l (CT l h)` on `Irr i`, where `h` interpolates `Φ` on `Disc i`. -/
theorem exists_eq_eval_of_discrete (tgt : ∀ i, Lev i → ι)
    (Irr : ∀ i, Set (Dual ℂ (S i))) (Good : ∀ i, Set (Dual ℂ (Dual ℂ (S i))))
    (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l)) (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i)
    (c : ∀ i, Lev i →₀ ℂ) (Disc : ∀ i, Submodule ℂ (Dual ℂ (S i))) (i : ι)
    (hA1 : ∀ θ ∈ Irr i, θ ∈ Disc i ⊔ inducedSpan tgt Irr CT i)
    (hA2 : ∀ l, ∀ x ∈ Disc i, descent tgt CT L i l x ∈ Disc i)
    (hA3 : ∀ x ∈ inducedSpan tgt Irr CT i,
      x = (c i).sum fun l a => a • descent tgt CT L i l x)
    (hA4 : ∀ Φ ∈ Good i, ∃ s : S i, ∀ x ∈ Disc i, Φ x = x s)
    (hA6 : ∀ l, ∀ θ ∈ Irr i, θ ∘ₗ L i l ∈ Submodule.span ℂ (Irr (tgt i l)))
    (hA9 : Disc i ≤ Submodule.span ℂ (Irr i)) :
    ∀ Φ ∈ Good i, (∀ x ∈ inducedSpan tgt Irr CT i, Φ x = 0) →
      ∃ s : S i, ∀ θ ∈ Irr i, Φ θ = θ s := by
  intro Φ hΦ hΦR
  obtain ⟨h, hh⟩ := hA4 Φ hΦ
  refine ⟨h - (c i).sum fun l a => a • L i l (CT i l h), ?_⟩
  intro θ hθ
  obtain ⟨d, hd, x, hx, rfl⟩ := Submodule.mem_sup.1 (hA1 θ hθ)
  -- Each descent of a discrete element is induced and discrete, so it is killed by `Φ` and
  -- by evaluation at `h`.
  have hdesc : ∀ l, descent tgt CT L i l d h = 0 := by
    intro l
    have hmem : descent tgt CT L i l d ∈ inducedSpan tgt Irr CT i := by
      have hy := comp_mem_span_of_mem_span Irr (L i l) (hA6 l) (hA9 hd)
      have := transpose_mem_inducedSpan tgt Irr CT i l hy
      simpa [descent, Dual.transpose_apply, LinearMap.comp_assoc] using this
    rw [← hh _ (hA2 l d hd), hΦR _ hmem]
  have hx' : x h = (c i).sum fun l a => a * descent tgt CT L i l x h := by
    conv_lhs => rw [hA3 x hx]
    rw [LinearMap.finsupp_sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [map_add, hΦR x hx, add_zero, hh d hd, map_sub, map_finsuppSum]
  simp only [map_smul, smul_eq_mul]
  have hsplit : ∀ l, (d + x) (L i l (CT i l h)) =
      descent tgt CT L i l d h + descent tgt CT L i l x h := by
    intro l
    simp [descent_apply]
  simp_rw [hsplit, hdesc, zero_add]
  rw [← hx', LinearMap.add_apply]
  ring

/-- Trace Paley–Wiener by induction from its discrete case. Suppose good functionals that
vanish on `inducedSpan` are trace forms (`hD`), the combinatorial identity holds on
`inducedSpan` (`hA3`), good functionals restrict along induction (`hA5`), restriction of
irreducible distributions lands in the spans of the Levis (`hA6`), `inducedSpan i` lies in the
span of `Irr i` (`hA7`), and good functionals stay good after subtracting an evaluation
(`hA8`). Then every good functional is a trace form on `Irr i`. -/
theorem exists_eq_eval_of_good_of_discrete (r : ι → ι → Prop) (hwf : WellFounded r)
    (tgt : ∀ i, Lev i → ι) (htgt : ∀ i l, r (tgt i l) i)
    (Irr : ∀ i, Set (Dual ℂ (S i))) (Good : ∀ i, Set (Dual ℂ (Dual ℂ (S i))))
    (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l)) (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i)
    (c : ∀ i, Lev i →₀ ℂ)
    (hD : ∀ i, ∀ Φ ∈ Good i, (∀ x ∈ inducedSpan tgt Irr CT i, Φ x = 0) →
      ∃ s : S i, ∀ θ ∈ Irr i, Φ θ = θ s)
    (hA3 : ∀ i, ∀ x ∈ inducedSpan tgt Irr CT i,
      x = (c i).sum fun l a => a • descent tgt CT L i l x)
    (hA5 : ∀ i l, ∀ Φ ∈ Good i, Φ ∘ₗ Dual.transpose (R := ℂ) (CT i l) ∈ Good (tgt i l))
    (hA6 : ∀ i l, ∀ θ ∈ Irr i, θ ∘ₗ L i l ∈ Submodule.span ℂ (Irr (tgt i l)))
    (hA7 : ∀ i, inducedSpan tgt Irr CT i ≤ Submodule.span ℂ (Irr i))
    (hA8 : ∀ i, ∀ Φ ∈ Good i, ∀ s : S i, Φ - Dual.eval ℂ (S i) s ∈ Good i) :
    ∀ i, ∀ Φ ∈ Good i, ∃ s : S i, ∀ θ ∈ Irr i, Φ θ = θ s := by
  intro i
  induction i using hwf.induction with
  | h i ih =>
  intro Φ hΦ
  choose sl hsl using fun l : Lev i =>
    ih (tgt i l) (htgt i l) _ (hA5 i l Φ hΦ)
  have hspan : ∀ l, ∀ y ∈ Submodule.span ℂ (Irr (tgt i l)),
      Φ (Dual.transpose (R := ℂ) (CT i l) y) = y (sl l) := by
    intro l y hy
    have hEq : Set.EqOn (Φ ∘ₗ Dual.transpose (R := ℂ) (CT i l))
        (Dual.eval ℂ (S (tgt i l)) (sl l)) (Irr (tgt i l)) := by
      intro θ' hθ'
      simpa using hsl l θ' hθ'
    exact LinearMap.eqOn_span hEq hy
  set s' : S i := (c i).sum fun l a => a • L i l (sl l) with hs'
  obtain ⟨sd, hsd⟩ := hD i _ (hA8 i Φ hΦ s') (by
    intro x hx
    have hdesc : ∀ l, Φ (descent tgt CT L i l x) = x (L i l (sl l)) := by
      intro l
      have hy := comp_mem_span_of_mem_span Irr (L i l) (hA6 i l) (hA7 i hx)
      have h := hspan l _ hy
      simpa [descent, Dual.transpose_apply, LinearMap.comp_assoc] using h
    have hΦx : Φ x = (c i).sum fun l a => a * x (L i l (sl l)) := by
      conv_lhs => rw [hA3 i x hx]
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun l _ => ?_
      rw [map_smul, smul_eq_mul, hdesc l]
    rw [LinearMap.sub_apply, Dual.eval_apply, hΦx, hs', map_finsuppSum]
    simp only [map_smul, smul_eq_mul, sub_self])
  refine ⟨sd + s', fun θ hθ => ?_⟩
  have h := hsd θ hθ
  rw [LinearMap.sub_apply, Dual.eval_apply] at h
  rw [map_add, ← h]
  ring

/-- `exists_eq_eval_of_good` as a proposition: the abstract trace Paley–Wiener assembly modeled on
Bernstein–Deligne–Kazhdan (1986), §4.3, for index
types in `Type u₁`, Levi types in `Type u₂` and test spaces in `Type u₃`. The hypotheses are, in
order, `hA1`–`hA6` of `exists_eq_eval_of_good`. -/
def PaleyWienerAssemblyStatement.{u₁, u₂, u₃} : Prop :=
  ∀ (ι : Type u₁) (Lev : ι → Type u₂) (S : ι → Type u₃) [∀ i, AddCommGroup (S i)]
    [∀ i, Module ℂ (S i)] (r : ι → ι → Prop), WellFounded r →
    ∀ (tgt : ∀ i, Lev i → ι), (∀ i l, r (tgt i l) i) →
    ∀ (Irr : ∀ i, Set (Dual ℂ (S i))) (Good : ∀ i, Set (Dual ℂ (Dual ℂ (S i))))
      (CT : ∀ i (l : Lev i), S i →ₗ[ℂ] S (tgt i l))
      (L : ∀ i (l : Lev i), S (tgt i l) →ₗ[ℂ] S i)
      (c : ∀ i, Lev i →₀ ℂ) (Disc : ∀ i, Submodule ℂ (Dual ℂ (S i))),
      (∀ i, ∀ θ ∈ Irr i, θ ∈ Disc i ⊔ inducedSpan tgt Irr CT i) →
      (∀ i l, ∀ x ∈ Disc i, descent tgt CT L i l x ∈ Disc i) →
      (∀ i, ∀ x ∈ inducedSpan tgt Irr CT i,
        x = (c i).sum fun l a => a • descent tgt CT L i l x) →
      (∀ i, ∀ Φ ∈ Good i, ∃ s : S i, ∀ x ∈ Disc i, Φ x = x s) →
      (∀ i l, ∀ Φ ∈ Good i, Φ ∘ₗ Dual.transpose (R := ℂ) (CT i l) ∈ Good (tgt i l)) →
      (∀ i l, ∀ θ ∈ Irr i, θ ∘ₗ L i l ∈ Submodule.span ℂ (Irr (tgt i l))) →
      ∀ i, ∀ Φ ∈ Good i, ∃ s : S i, ∀ θ ∈ Irr i, Φ θ = θ s

theorem paleyWienerAssembly : PaleyWienerAssemblyStatement.{uι, uL, uS} := by
  intro ι Lev S _ _ r hwf tgt htgt Irr Good CT L c Disc hA1 hA2 hA3 hA4 hA5 hA6
  exact exists_eq_eval_of_good r hwf tgt htgt Irr Good CT L c Disc hA1 hA2 hA3 hA4 hA5 hA6

end Langlands.BaseChange.PaleyWienerAssembly
