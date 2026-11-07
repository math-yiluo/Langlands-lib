import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Jacquet.CharacterAveraging
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
import Langlands.Representation.FiniteVectors

/-! # The coefficient spaces `A(G)` and `A^w(G)` (Waldspurger, Lemma I.6.1 and Lemma III.2.1)

Waldspurger I.6 (printed p. 249): for `f ∈ C_lisse(G)`, `V_ρ(f)` is the smallest subspace
containing `f` and stable under right translations, `V_{ρ×λ}(f)` the smallest one stable under
right and left translations, `ρ_f` right translation on `V_ρ(f)`, `A_ρ` the set of `f` with
`ρ_f` admissible, `A(π)` the span of the coefficients of `π` and `A(G) = ⋃_π A(π) = Σ_π A(π)`.
Lemma I.6.1: for `f ∈ A_ρ`, `V_{ρ×λ}(f) = A(ρ_f)`, and `A_ρ = A(G)` (with the analogous
statements for `λ`). Lemma III.2.1 (printed p. 265): `A^w(G) = A(G) ∩ C^w_lisse(G)` is the union,
and the sum, of the `A(π)` over the admissible tempered `π`.

This module proves the statements for `ρ`, for a topological group with a compact open subgroup:

* `twoSidedTranslateSpan_eq_coefficientFunctionSpace` (Lemma I.6.1 (1)), through
  `mem_span_evalFunctional` (every smooth linear form on `V_ρ(f)` is a combination of point
  evaluations, the source's `V = V_ρ(f)ˇ`);
* `isRightAdmissible_iff` (Lemma I.6.1 (2), `A_ρ = A(G)`) and
  `exists_admissible_coefficient_add` (`⋃_π A(π)` is closed under addition), through the
  admissibility of a sum of two admissible subrepresentations (`isAdmissible_sup`);
* `temperedCoefficient_iff` (Lemma III.2.1) and `exists_tempered_coefficient_add`.

The statements for left translation (`A_λ`, `A(λ̌_f)`) are not formalized. -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Langlands.Compact

universe u

section RightTranslates

variable {G : Type u} [Group G]

theorem rightTranslation_apply' (g : G) (f : G → ℂ) (x : G) :
    Whittaker.rightTranslation ℂ G g f x = f (x * g) :=
  rfl

/-- Waldspurger's `V_ρ(f)`: the smallest subspace of `G → ℂ` containing `f` and stable under
right translations, as a subrepresentation of right translation. -/
abbrev rightTranslateSpan (f : G → ℂ) : Subrepresentation (Whittaker.rightTranslation ℂ G) :=
  FiniteVectors.orbitSubrepresentation (Whittaker.rightTranslation ℂ G) f

theorem rightTranslation_mem_rightTranslateSpan (f : G → ℂ) (g : G) :
    Whittaker.rightTranslation ℂ G g f ∈ (rightTranslateSpan f).toSubmodule :=
  Submodule.subset_span ⟨g, rfl⟩

theorem mem_rightTranslateSpan_self (f : G → ℂ) : f ∈ (rightTranslateSpan f).toSubmodule := by
  have h := rightTranslation_mem_rightTranslateSpan f 1
  rwa [map_one] at h

/-- Waldspurger's `V_{ρ×λ}(f)`: the span of the two-sided translates `x ↦ f(g₂⁻¹ x g₁)`. -/
def twoSidedTranslateSpan (f : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun p : G × G => translate p.1 p.2 f)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Waldspurger's `A_ρ`: `f` is bi-invariant under a compact open subgroup and right translation
on `V_ρ(f)` is admissible. -/
def IsRightAdmissible (f : G → ℂ) : Prop :=
  (∃ H : CompactOpenSubgroup G, IsBiInvariant H.toSubgroup f) ∧
    IsAdmissible (rightTranslateSpan f).toRepresentation

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Elements of `V_ρ(f)` are left invariant under a subgroup under which `f` is. -/
theorem leftInvariant_of_mem_rightTranslateSpan {H : Subgroup G} {f : G → ℂ}
    (hf : ∀ h ∈ H, ∀ x, f (h * x) = f x) {v : G → ℂ}
    (hv : v ∈ (rightTranslateSpan f).toSubmodule) : ∀ h ∈ H, ∀ x, v (h * x) = v x := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨g, rfl⟩ := hw
    intro h hh x
    simp only [rightTranslation_apply', mul_assoc]
    exact hf h hh _
  | zero => intro h _ x; rfl
  | add w₁ w₂ _ _ h₁ h₂ =>
    intro h hh x
    simp only [Pi.add_apply, h₁ h hh x, h₂ h hh x]
  | smul c w _ hw =>
    intro h hh x
    simp only [Pi.smul_apply, hw h hh x]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Evaluation at `x` as a linear form on `V_ρ(f)`. -/
def evalFunctional (f : G → ℂ) (x : G) : Module.Dual ℂ (rightTranslateSpan f).toSubmodule :=
  (LinearMap.proj x).comp (rightTranslateSpan f).toSubmodule.subtype

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem evalFunctional_apply (f : G → ℂ) (x : G) (v : (rightTranslateSpan f).toSubmodule) :
    evalFunctional f x v = (v : G → ℂ) x :=
  rfl

/-- If `f` is left invariant under the compact open `H`, evaluation at `x` is a smooth linear
form on `V_ρ(f)`, fixed by `x⁻¹ H x`. -/
theorem isSmoothVector_evalFunctional {f : G → ℂ} (H : CompactOpenSubgroup G)
    (hf : ∀ h ∈ H.toSubgroup, ∀ y, f (h * y) = f y) (x : G) :
    IsSmoothVector (rightTranslateSpan f).toRepresentation.dual (evalFunctional f x) := by
  refine ⟨(H.conj x⁻¹).1, ?_⟩
  intro k
  apply LinearMap.ext
  intro v
  have hk : x * (k : G)⁻¹ * x⁻¹ ∈ H.toSubgroup := by
    have h1 := (mem_conjSubgroup (g := x⁻¹) (H := H.toSubgroup)).1 k.2
    have h2 := H.toSubgroup.inv_mem h1
    simpa [mul_assoc] using h2
  change (v : G → ℂ) (x * (k : G)⁻¹) = (v : G → ℂ) x
  have h := leftInvariant_of_mem_rightTranslateSpan hf v.2 _ hk x
  rwa [show x * (k : G)⁻¹ * x⁻¹ * x = x * (k : G)⁻¹ by group] at h

end RightTranslates

section Averaging

variable {K : Type*} [Group K] {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- A linear form constant on an orbit takes that value at the orbit mean. -/
theorem map_orbitMean_of_forall_eq (τ : Representation ℂ K X) (v : X) [Finite (orbit τ v)]
    (φ : X →ₗ[ℂ] ℂ) (c : ℂ) (h : ∀ k, φ (τ k v) = c) : φ (orbitMean τ v) = c := by
  classical
  let := Fintype.ofFinite (orbit τ v)
  have hx : ∀ x : orbit τ v, φ x.val = c := fun x => by
    obtain ⟨k, hk⟩ := x.property
    rw [← hk]
    exact h k
  have hc : (Fintype.card (orbit τ v) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Jacquet.Localization.orbitMean_eq_smul_sum, map_smul, map_sum,
    Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end Averaging

section Evaluations

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Waldspurger, proof of Lemma I.6.1**: if `f ∈ A_ρ`, every smooth linear form on `V_ρ(f)`
is a linear combination of evaluations at points of `G` ("`V = V_ρ(f)ˇ`"). -/
theorem mem_span_evalFunctional {f : G → ℂ} (hf : IsRightAdmissible f)
    (ℓ : SmoothDual (rightTranslateSpan f).toRepresentation) :
    ℓ.val ∈ Submodule.span ℂ (Set.range (evalFunctional f)) := by
  obtain ⟨⟨H, hH⟩, hW⟩ := hf
  have : Nonempty (CompactOpenSubgroup G) := ⟨H⟩
  let W := rightTranslateSpan f
  let ρW := W.toRepresentation
  have hfL : ∀ h ∈ H.toSubgroup, ∀ y, f (h * y) = f y := fun h hh y => by
    simpa using hH h hh 1 H.toSubgroup.one_mem y
  -- the smooth evaluations and their span `E` in the smooth dual
  let ev : G → SmoothDual ρW := fun x => ⟨evalFunctional f x, isSmoothVector_evalFunctional H hfL x⟩
  let E : Submodule ℂ (SmoothDual ρW) := Submodule.span ℂ (Set.range ev)
  let ρc := smoothContragredient ρW
  have hρc : IsSmooth ρc := isSmooth_smoothContragredient ρW
  have hev_g : ∀ (g x : G), ρc g (ev x) = ev (x * g⁻¹) := by
    intro g x
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl
  have hEstable : ∀ (g : G) (e : SmoothDual ρW), e ∈ E → ρc g e ∈ E := by
    intro g e he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      rw [hev_g]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [map_zero]; exact E.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact E.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact E.smul_mem c ha
  -- a compact open subgroup fixing `ℓ`
  obtain ⟨K₀, hK₀⟩ := ℓ.property
  obtain ⟨K, hKc, hKK₀⟩ := CompactOpenSubgroup.cofinal K₀
  have hℓK : ℓ ∈ fixedVectors ρc K.toSubgroup := by
    intro k
    apply Subtype.ext
    exact hK₀ ⟨k, hKK₀ k.2⟩
  have : Module.Finite ℂ (fixedVectors ρW K.toSubgroup) := hW.2 K
  set F := fixedVectors ρW K.toSubgroup
  set res := smoothDualFixedRestriction ρW K.toSubgroup
  have hres := smoothDualFixedRestriction_bijective ρW hW.1 K hKc
  set P := averageMap ρc hρc K hKc
  have hPfix : ∀ e, P e ∈ fixedVectors ρc K.toSubgroup := fun e =>
    averageMap_mem_fixedVectors ρc hρc K hKc e
  have hPval : ∀ (e : SmoothDual ρW) (w : F), (P e).val w = e.val w := by
    intro e w
    let := finite_orbit_of_smooth ρc hρc K hKc e
    let φ : SmoothDual ρW →ₗ[ℂ] ℂ := (LinearMap.applyₗ (w : W.toSubmodule)).comp
      (smoothVectors ρW.dual).subtype
    refine map_orbitMean_of_forall_eq (ρc.comp K.toSubgroup.subtype) e φ (e.val w) fun k => ?_
    change (ρW.dual (k : G) e.val) w = e.val w
    change e.val (ρW (k : G)⁻¹ w) = e.val w
    congr 1
    exact w.2 ⟨(k : G)⁻¹, K.toSubgroup.inv_mem k.2⟩
  have hPE : ∀ e ∈ E, P e ∈ E := by
    intro e he
    let := finite_orbit_of_smooth ρc hρc K hKc e
    exact Jacquet.Localization.orbitMean_mem (ρc.comp K.toSubgroup.subtype) e E
      fun k => hEstable k e he
  -- the restrictions of the averaged evaluations span `F^*`
  let T : E →ₗ[ℂ] Module.Dual ℂ F :=
    res.comp ((LinearMap.codRestrict (fixedVectors ρc K.toSubgroup) P hPfix).comp E.subtype)
  have hT : ∀ (e : E) (w : F), T e w = (e : SmoothDual ρW).val w := fun e w => hPval e w
  have hsep : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have h := hw (T ⟨ev x, Submodule.subset_span ⟨x, rfl⟩⟩) ⟨_, rfl⟩
    rw [hT] at h
    exact h
  have hFfd : FiniteDimensional ℂ F := this
  have hFfree : Module.Free ℂ F := Module.Free.of_divisionRing ℂ F
  have hFproj : Module.Projective ℂ F := Module.Projective.of_free
  have hDfd : FiniteDimensional ℂ (Module.Dual ℂ F) := Module.dual_finite
  have hRfd : FiniteDimensional ℂ (LinearMap.range T) :=
    FiniteDimensional.finiteDimensional_submodule _
  have htop : LinearMap.range T = ⊤ := by
    have key := Subspace.dualCoannihilator_dualAnnihilator_eq (K := ℂ) (V := F)
      (W := LinearMap.range T)
    rw [hsep, Submodule.dualAnnihilator_bot] at key
    exact key.symm
  obtain ⟨e, he⟩ : res ⟨ℓ, hℓK⟩ ∈ LinearMap.range T := by rw [htop]; exact Submodule.mem_top
  have hPe : P (e : SmoothDual ρW) = ℓ := congrArg Subtype.val (hres.1 he)
  have hℓE : ℓ ∈ E := hPe ▸ hPE e.1 e.2
  have hmap := Submodule.mem_map_of_mem (f := (smoothVectors ρW.dual).subtype) hℓE
  rw [Submodule.map_span, ← Set.range_comp] at hmap
  exact hmap

/-- The smooth representation `ρ_f` of right translation on `V_ρ(f)`, for `f ∈ A_ρ`. -/
abbrev rightTranslateRep {f : G → ℂ} (hf : IsRightAdmissible f) : SmoothRep.{0, u, u} ℂ G :=
  SmoothRep.of (rightTranslateSpan f).toRepresentation hf.2.1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The functions `g ↦ v(x g)`, `v ∈ V_ρ(f)`, are two-sided translates of `f`. -/
theorem translate_mem_twoSidedTranslateSpan {f : G → ℂ} (x : G) {v : G → ℂ}
    (hv : v ∈ (rightTranslateSpan f).toSubmodule) :
    (fun g => v (x * g)) ∈ twoSidedTranslateSpan f := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨h, rfl⟩ := hw
    refine Submodule.subset_span ⟨(h, x⁻¹), ?_⟩
    funext g
    simp only [translate_apply, rightTranslation_apply', inv_inv, mul_assoc]
  | zero => exact (twoSidedTranslateSpan f).zero_mem
  | add a b _ _ ha hb => exact (twoSidedTranslateSpan f).add_mem ha hb
  | smul c a _ ha => exact (twoSidedTranslateSpan f).smul_mem c ha

/-- **Waldspurger, Lemma I.6.1 (1)** (the part for `ρ`): for `f ∈ A_ρ`,
`V_{ρ×λ}(f) = A(ρ_f)`. -/
theorem twoSidedTranslateSpan_eq_coefficientFunctionSpace {f : G → ℂ}
    (hf : IsRightAdmissible f) :
    twoSidedTranslateSpan f = coefficientFunctionSpace (rightTranslateRep hf) := by
  obtain ⟨⟨H, hH⟩, -⟩ := id hf
  have hfL : ∀ h ∈ H.toSubgroup, ∀ y, f (h * y) = f y := fun h hh y => by
    simpa using hH h hh 1 H.toSubgroup.one_mem y
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
    let ev : SmoothDual (rightTranslateSpan f).toRepresentation :=
      ⟨evalFunctional f g₂⁻¹, isSmoothVector_evalFunctional H hfL g₂⁻¹⟩
    have h := matrixCoefficient_mem_coefficientFunctionSpace (rightTranslateRep hf) ev
      ⟨_, rightTranslation_mem_rightTranslateSpan f g₁⟩
    have e : translate g₁ g₂ f = matrixCoefficient (rightTranslateRep hf).representation ev.val
        ⟨_, rightTranslation_mem_rightTranslateSpan f g₁⟩ := by
      funext x
      simp only [translate_apply]
      rfl
    change translate g₁ g₂ f ∈ (coefficientFunctionSpace (rightTranslateRep hf) : Set (G → ℂ))
    rw [e]
    exact h
  · refine iSup_le fun ℓ => ?_
    rintro _ ⟨v, rfl⟩
    have key : ∀ ψ ∈ Submodule.span ℂ (Set.range (evalFunctional f)),
        matrixCoefficient (rightTranslateSpan f).toRepresentation ψ v ∈
          twoSidedTranslateSpan f := by
      intro ψ hψ
      induction hψ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨x, rfl⟩ := hφ
        exact translate_mem_twoSidedTranslateSpan x v.2
      | zero => rw [map_zero, LinearMap.zero_apply]; exact zero_mem _
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ c ha
    exact key ℓ.val (mem_span_evalFunctional hf ℓ)

end Evaluations

section Admissibility

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- An intertwiner maps the orbit span of `x` onto the orbit span of its image. -/
def orbitSpanMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (Φ : ρ.IntertwiningMap σ) (x : V) :
    (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation.IntertwiningMap
      (FiniteVectors.orbitSubrepresentation σ (Φ x)).toRepresentation where
  toLinearMap := Φ.toLinearMap.restrict
    (p := (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule)
    (q := (FiniteVectors.orbitSubrepresentation σ (Φ x)).toSubmodule) (fun v hv => by
      induction hv using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        change Φ (ρ g x) ∈ _
        rw [Φ.isIntertwining]
        exact FiniteVectors.action_mem_orbitSpan σ g (Φ x)
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Φ.isIntertwining (g := g) (v := v.1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem orbitSpanMap_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (Φ : ρ.IntertwiningMap σ) (x : V) : Function.Surjective (orbitSpanMap Φ x) := by
  have hle : (FiniteVectors.orbitSubrepresentation σ (Φ x)).toSubmodule ≤
      (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule.map Φ.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨ρ g x, FiniteVectors.action_mem_orbitSpan ρ g x, ?_⟩
    exact Φ.isIntertwining (g := g) (v := x)
  intro y
  obtain ⟨v, hv, hvy⟩ := hle y.2
  exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The inclusion of a smaller subrepresentation into a larger one. -/
def inclusionOfLe {σ : Representation ℂ G W} {W₁ W₂ : Subrepresentation σ}
    (h : W₁ ≤ W₂) :
    W₁.toRepresentation.IntertwiningMap W₂.toRepresentation where
  toLinearMap := Submodule.inclusion (show W₁.toSubmodule ≤ W₂.toSubmodule from h)
  isIntertwining' _ := LinearMap.ext fun _ => rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem inclusionOfLe_injective {σ : Representation ℂ G W}
    {W₁ W₂ : Subrepresentation σ} (h : W₁ ≤ W₂) : Function.Injective (inclusionOfLe h) :=
  Submodule.inclusion_injective (show W₁.toSubmodule ≤ W₂.toSubmodule from h)

variable [Nonempty (CompactOpenSubgroup G)]

/-- The sum of two admissible subrepresentations is admissible. -/
theorem isAdmissible_sup {σ : Representation ℂ G W} {W₁ W₂ : Subrepresentation σ}
    (h₁ : IsAdmissible W₁.toRepresentation) (h₂ : IsAdmissible W₂.toRepresentation) :
    IsAdmissible (W₁ ⊔ W₂).toRepresentation := by
  have hmem : ∀ v : (W₁ ⊔ W₂).toSubmodule, ∃ a ∈ W₁.toSubmodule, ∃ b ∈ W₂.toSubmodule,
      a + b = (v : W) := fun v => by
    have hv : (v : W) ∈ W₁.toSubmodule ⊔ W₂.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup]
      exact v.2
    exact Submodule.mem_sup.1 hv
  have hs : IsSmooth (W₁ ⊔ W₂).toRepresentation := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := hmem v
    obtain ⟨K₁, hK₁⟩ := h₁.1 ⟨a, ha⟩
    obtain ⟨K₂, hK₂⟩ := h₂.1 ⟨b, hb⟩
    refine ⟨K₁ ⊓ K₂, fun k => ?_⟩
    apply Subtype.ext
    change σ k (v : W) = v
    have e₁ := congrArg Subtype.val (hK₁ ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩)
    have e₂ := congrArg Subtype.val (hK₂ ⟨k, (OpenSubgroup.mem_inf.1 k.2).2⟩)
    change σ k a = a at e₁
    change σ k b = b at e₂
    rw [← hab, map_add, e₁, e₂]
  refine ⟨hs, fun K => ?_⟩
  obtain ⟨K', hK'c, hK'K⟩ := CompactOpenSubgroup.cofinal K
  suffices h : Module.Finite ℂ (fixedVectors (W₁ ⊔ W₂).toRepresentation K'.toSubgroup) from
    finite_fixedVectors_of_le (show K'.toSubgroup ≤ K.toSubgroup from hK'K)
  have : Module.Finite ℂ (fixedVectors W₁.toRepresentation K'.toSubgroup) := h₁.2 K'
  have : Module.Finite ℂ (fixedVectors W₂.toRepresentation K'.toSubgroup) := h₂.2 K'
  have hle₁ : W₁ ≤ W₁ ⊔ W₂ := le_sup_left
  have hle₂ : W₂ ≤ W₁ ⊔ W₂ := le_sup_right
  let ι : (fixedVectors W₁.toRepresentation K'.toSubgroup) ×
      (fixedVectors W₂.toRepresentation K'.toSubgroup) →ₗ[ℂ] (W₁ ⊔ W₂).toSubmodule :=
    (inclusionOfLe hle₁).toLinearMap.comp ((fixedVectors _ _).subtype.comp
      (LinearMap.fst ℂ _ _)) +
    (inclusionOfLe hle₂).toLinearMap.comp ((fixedVectors _ _).subtype.comp
      (LinearMap.snd ℂ _ _))
  have hle : fixedVectors (W₁ ⊔ W₂).toRepresentation K'.toSubgroup ≤ LinearMap.range ι := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := hmem v
    set P := averageMap (W₁ ⊔ W₂).toRepresentation hs K' hK'c
    set P₁ := averageMap W₁.toRepresentation h₁.1 K' hK'c
    set P₂ := averageMap W₂.toRepresentation h₂.1 K' hK'c
    have c₁ := LinearMap.congr_fun
      (averageMap_commute _ _ h₁.1 hs K' hK'c (inclusionOfLe hle₁))
      ⟨a, ha⟩
    have c₂ := LinearMap.congr_fun
      (averageMap_commute _ _ h₂.1 hs K' hK'c (inclusionOfLe hle₂))
      ⟨b, hb⟩
    refine ⟨(⟨P₁ ⟨a, ha⟩, averageMap_mem_fixedVectors _ h₁.1 K' hK'c _⟩,
      ⟨P₂ ⟨b, hb⟩, averageMap_mem_fixedVectors _ h₂.1 K' hK'c _⟩), ?_⟩
    change inclusionOfLe hle₁ (P₁ ⟨a, ha⟩) + inclusionOfLe hle₂ (P₂ ⟨b, hb⟩) = v
    simp only [LinearMap.comp_apply] at c₁ c₂
    change inclusionOfLe hle₁ (P₁ ⟨a, ha⟩) = P (inclusionOfLe hle₁ ⟨a, ha⟩) at c₁
    change inclusionOfLe hle₂ (P₂ ⟨b, hb⟩) = P (inclusionOfLe hle₂ ⟨b, hb⟩) at c₂
    rw [c₁, c₂, ← map_add]
    have hsum : inclusionOfLe hle₁ ⟨a, ha⟩ + inclusionOfLe hle₂ ⟨b, hb⟩ = v :=
      Subtype.ext hab
    rw [hsum]
    exact averageMap_id _ hs K' hK'c v hv
  have : FiniteDimensional ℂ (LinearMap.range ι) := LinearMap.finiteDimensional_range ι
  exact Submodule.finiteDimensional_of_le hle

/-- A coefficient `g ↦ ℓ(ρ(g) x)` of an admissible representation lies in `A_ρ`. -/
theorem isRightAdmissible_matrixCoefficient {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
    (ℓ : SmoothDual ρ) (x : V) : IsRightAdmissible (matrixCoefficient ρ ℓ.val x) := by
  constructor
  · obtain ⟨K₁, hK₁⟩ := hρ.1 x
    have hℓs : IsSmoothVector ρ.dual ℓ.val := ℓ.property
    obtain ⟨K₂, hK₂⟩ := hℓs
    obtain ⟨H, hHc, hH⟩ := CompactOpenSubgroup.cofinal (K₁ ⊓ K₂)
    refine ⟨⟨H, hHc⟩, fun h₁ hh₁ h₂ hh₂ g => ?_⟩
    have hx : ρ h₂ x = x := hK₁ ⟨h₂, (OpenSubgroup.mem_inf.1 (hH hh₂)).1⟩
    have hℓ : ∀ y, ℓ.val (ρ h₁ y) = ℓ.val y := fun y => by
      have h := congrArg (fun φ : Module.Dual ℂ V => φ y)
        (hK₂ ⟨h₁⁻¹, K₂.toSubgroup.inv_mem (OpenSubgroup.mem_inf.1 (hH hh₁)).2⟩)
      simpa [Module.Dual.transpose_apply] using h
    change ℓ.val (ρ (h₁ * g * h₂) x) = ℓ.val (ρ g x)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx, hℓ]
  · have hS : IsAdmissible (FiniteVectors.orbitSubrepresentation ρ x).toRepresentation :=
      isAdmissible_of_injective
        (ProductFactorization.subrepresentationInclusion (FiniteVectors.orbitSubrepresentation ρ x))
        (ProductFactorization.subrepresentationInclusion_injective _) hρ
    exact Langlands.Unramified.SphericalExistence.isAdmissible_of_surjective
      CompactOpenSubgroup.cofinal
      (orbitSpanMap (coefficientIntertwiningMap ρ ℓ.val) x)
      (orbitSpanMap_surjective _ x) hS

omit [IsTopologicalGroup G] in
theorem isRightAdmissible_zero : IsRightAdmissible (0 : G → ℂ) := by
  obtain ⟨H⟩ := ‹Nonempty (CompactOpenSubgroup G)›
  refine ⟨⟨H, fun _ _ _ _ _ => rfl⟩, ?_⟩
  have hbot : ∀ v ∈ (rightTranslateSpan (0 : G → ℂ)).toSubmodule, v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem w hw => obtain ⟨g, rfl⟩ := hw; exact map_zero _
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul c a _ ha => rw [ha, smul_zero]
  refine ⟨fun v => ⟨⊤, fun k => Subtype.ext ?_⟩, fun K => ?_⟩
  · change Whittaker.rightTranslation ℂ G k (v : G → ℂ) = v
    rw [hbot v v.2, map_zero]
  · have : Subsingleton (rightTranslateSpan (0 : G → ℂ)).toSubmodule :=
      ⟨fun a b => Subtype.ext ((hbot a a.2).trans (hbot b b.2).symm)⟩
    infer_instance

omit [IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)] in
theorem isRightAdmissible_smul {f : G → ℂ} (hf : IsRightAdmissible f) (c : ℂ) :
    IsRightAdmissible (c • f) := by
  obtain ⟨⟨H, hH⟩, hW⟩ := hf
  refine ⟨⟨H, fun h₁ hh₁ h₂ hh₂ g => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, hH h₁ hh₁ h₂ hh₂ g]
  · have hle : rightTranslateSpan (c • f) ≤ rightTranslateSpan f := by
      change Submodule.span ℂ _ ≤ Submodule.span ℂ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      change Whittaker.rightTranslation ℂ G g (c • f) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c (FiniteVectors.action_mem_orbitSpan _ g f)
    exact isAdmissible_of_injective (inclusionOfLe hle) (inclusionOfLe_injective hle) hW

theorem isRightAdmissible_add {f₁ f₂ : G → ℂ} (h₁ : IsRightAdmissible f₁)
    (h₂ : IsRightAdmissible f₂) : IsRightAdmissible (f₁ + f₂) := by
  obtain ⟨⟨H₁, hH₁⟩, hW₁⟩ := h₁
  obtain ⟨⟨H₂, hH₂⟩, hW₂⟩ := h₂
  refine ⟨⟨H₁.inf H₂, fun a ha b hb g => ?_⟩, ?_⟩
  · have ha₁ := CompactOpenSubgroup.inf_le_left H₁ H₂ ha
    have ha₂ := CompactOpenSubgroup.inf_le_right H₁ H₂ ha
    have hb₁ := CompactOpenSubgroup.inf_le_left H₁ H₂ hb
    have hb₂ := CompactOpenSubgroup.inf_le_right H₁ H₂ hb
    simp only [Pi.add_apply, hH₁ a ha₁ b hb₁ g, hH₂ a ha₂ b hb₂ g]
  · have hle : rightTranslateSpan (f₁ + f₂) ≤ rightTranslateSpan f₁ ⊔ rightTranslateSpan f₂ := by
      intro v hv
      change v ∈ (rightTranslateSpan f₁ ⊔ rightTranslateSpan f₂).toSubmodule
      rw [Subrepresentation.toSubmodule_sup]
      change v ∈ Submodule.span ℂ _ at hv
      refine (Submodule.span_le.2 ?_) hv
      rintro _ ⟨g, rfl⟩
      change Whittaker.rightTranslation ℂ G g (f₁ + f₂) ∈ _
      rw [map_add]
      exact Submodule.add_mem_sup (FiniteVectors.action_mem_orbitSpan _ g f₁)
        (FiniteVectors.action_mem_orbitSpan _ g f₂)
    exact isAdmissible_of_injective (inclusionOfLe hle) (inclusionOfLe_injective hle)
      (isAdmissible_sup hW₁ hW₂)

/-- Every element of `A(π)`, `π` admissible, lies in `A_ρ`. -/
theorem isRightAdmissible_of_mem_coefficientFunctionSpace {A : SmoothRep.{0, u, u} ℂ G}
    (hA : IsAdmissible A.representation) {f : G → ℂ} (hf : f ∈ coefficientFunctionSpace A) :
    IsRightAdmissible f := by
  refine Submodule.iSup_induction _ (motive := IsRightAdmissible) hf (fun ℓ y hy => ?_)
    isRightAdmissible_zero (fun a b ha hb => isRightAdmissible_add ha hb)
  obtain ⟨x, rfl⟩ := hy
  exact isRightAdmissible_matrixCoefficient hA ℓ x

/-- **Waldspurger, Lemma I.6.1 (2)** (the part for `ρ`): `A_ρ = A(G)`, where `A(G)` is the union
of the coefficient spaces `A(π)` of the admissible representations `π` (on types in the universe
of `G`). -/
theorem isRightAdmissible_iff (f : G → ℂ) :
    IsRightAdmissible f ↔
      ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
        f ∈ coefficientFunctionSpace A := by
  constructor
  · intro hf
    refine ⟨rightTranslateRep hf, hf.2, ?_⟩
    rw [← twoSidedTranslateSpan_eq_coefficientFunctionSpace hf]
    refine Submodule.subset_span ⟨(1, 1), ?_⟩
    exact translate_one_one f
  · rintro ⟨A, hA, hf⟩
    exact isRightAdmissible_of_mem_coefficientFunctionSpace hA hf

/-- `A(G) = ⋃_π A(π)` is closed under addition, hence equals `Σ_π A(π)` (Waldspurger I.6). -/
theorem exists_admissible_coefficient_add {f₁ f₂ : G → ℂ}
    (h₁ : ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      f₁ ∈ coefficientFunctionSpace A)
    (h₂ : ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      f₂ ∈ coefficientFunctionSpace A) :
    ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      f₁ + f₂ ∈ coefficientFunctionSpace A :=
  (isRightAdmissible_iff _).1
    (isRightAdmissible_add ((isRightAdmissible_iff _).2 h₁) ((isRightAdmissible_iff _).2 h₂))

end Admissibility

section Tempered

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Two-sided translates of a function of tempered growth have tempered growth (Lemma II.1.2). -/
theorem HasTemperedGrowth.translate (hw : TranslationWeights Ξ σ) {f : G → ℂ}
    (hf : HasTemperedGrowth Ξ σ f) (g₁ g₂ : G) :
    HasTemperedGrowth Ξ σ (HarishChandraSchwartz.translate g₁ g₂ f) := by
  rw [hasTemperedGrowth_iff hw.pos hw.nonneg] at hf ⊢
  obtain ⟨s, hs⟩ := hf
  obtain ⟨d, hd⟩ := hw.nu_translate_le g₁ g₂
  obtain ⟨c, -, hc⟩ := hd (s - d)
  refine ⟨s - d, ne_top_of_le_ne_top ?_ (hc f)⟩
  rw [sub_add_cancel]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `V_{ρ×λ}(f) ⊂ C^w_lisse(G)` for `f` of tempered growth. -/
theorem hasTemperedGrowth_of_mem_twoSidedTranslateSpan (hw : TranslationWeights Ξ σ)
    {f : G → ℂ} (hf : HasTemperedGrowth Ξ σ f) {φ : G → ℂ}
    (hφ : φ ∈ twoSidedTranslateSpan f) : HasTemperedGrowth Ξ σ φ := by
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨⟨g₁, g₂⟩, rfl⟩ := hψ
    exact hf.translate hw g₁ g₂
  | zero => exact ⟨0, 0, fun g => by simp⟩
  | add a b _ _ ha hb => exact ha.add hw.pos hw.nonneg hb
  | smul c a _ ha => exact ha.smul c

omit [IsTopologicalGroup G] in
/-- The elements of `A(π)` have tempered growth when `π` has tempered coefficients. -/
theorem hasTemperedGrowth_of_mem_coefficientFunctionSpace (hw : TranslationWeights Ξ σ)
    {A : SmoothRep.{0, u, u} ℂ G} (hT : HasTemperedCoefficients Ξ σ A.representation)
    {f : G → ℂ} (hf : f ∈ coefficientFunctionSpace A) : HasTemperedGrowth Ξ σ f := by
  refine Submodule.iSup_induction _ (motive := HasTemperedGrowth Ξ σ) hf (fun ℓ y hy => ?_)
    ⟨0, 0, fun g => by simp⟩ (fun a b ha hb => ha.add hw.pos hw.nonneg hb)
  obtain ⟨x, rfl⟩ := hy
  exact hT x ℓ

variable [Nonempty (CompactOpenSubgroup G)]

/-- **Waldspurger, Lemma III.2.1** (the union): `A^w(G) = A(G) ∩ C^w_lisse(G)` is the union of
the coefficient spaces `A(π)` of the admissible representations `π` with tempered coefficients
(on types in the universe of `G`). -/
theorem temperedCoefficient_iff (hw : TranslationWeights Ξ σ) (f : G → ℂ) :
    ((∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
        f ∈ coefficientFunctionSpace A) ∧ HasTemperedGrowth Ξ σ f) ↔
      ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
        HasTemperedCoefficients Ξ σ A.representation ∧ f ∈ coefficientFunctionSpace A := by
  constructor
  · rintro ⟨hA, hT⟩
    have hf := (isRightAdmissible_iff f).2 hA
    have hEq := twoSidedTranslateSpan_eq_coefficientFunctionSpace hf
    refine ⟨rightTranslateRep hf, hf.2, fun v ℓ => ?_, ?_⟩
    · refine hasTemperedGrowth_of_mem_twoSidedTranslateSpan hw hT ?_
      rw [hEq]
      exact matrixCoefficient_mem_coefficientFunctionSpace (rightTranslateRep hf) ℓ v
    · rw [← hEq]
      exact Submodule.subset_span ⟨(1, 1), translate_one_one f⟩
  · rintro ⟨A, hA, hT, hf⟩
    exact ⟨⟨A, hA, hf⟩, hasTemperedGrowth_of_mem_coefficientFunctionSpace hw hT hf⟩

/-- The union in Lemma III.2.1 is closed under addition, hence equals the sum
`Σ_π A(π)` over the admissible `π` with tempered coefficients. -/
theorem exists_tempered_coefficient_add (hw : TranslationWeights Ξ σ) {f₁ f₂ : G → ℂ}
    (h₁ : ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      HasTemperedCoefficients Ξ σ A.representation ∧ f₁ ∈ coefficientFunctionSpace A)
    (h₂ : ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      HasTemperedCoefficients Ξ σ A.representation ∧ f₂ ∈ coefficientFunctionSpace A) :
    ∃ A : SmoothRep.{0, u, u} ℂ G, IsAdmissible A.representation ∧
      HasTemperedCoefficients Ξ σ A.representation ∧ f₁ + f₂ ∈ coefficientFunctionSpace A := by
  obtain ⟨a₁, t₁⟩ := (temperedCoefficient_iff hw f₁).2 h₁
  obtain ⟨a₂, t₂⟩ := (temperedCoefficient_iff hw f₂).2 h₂
  exact (temperedCoefficient_iff hw _).1
    ⟨exists_admissible_coefficient_add a₁ a₂, t₁.add hw.pos hw.nonneg t₂⟩

end Tempered

end Langlands.HarishChandraSchwartz
