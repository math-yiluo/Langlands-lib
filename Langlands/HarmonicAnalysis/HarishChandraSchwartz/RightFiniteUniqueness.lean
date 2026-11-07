import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence

/-!
# Right-finite functions are determined by their values on cones

Waldspurger, proof of Proposition I.6.2 (printed p. 250): two `A_M`-finite functions that
coincide on a "cone" of `A_M` are equal. Here a function `φ` on a group `M` is *right finite*
for a subgroup `A` (`IsRightFinite A φ`) if it lies in a finite-dimensional space of functions
stable under right translation by `A`. A cone is a nonempty subset `C` of `A` with `C S ⊆ C` for
a subset `S` generating `A`.

* `eq_zero_of_eqOn_cone`: a function in a finite-dimensional space of functions on a group,
  stable under right translations, which vanishes on such a cone, is zero;
* `IsRightFinite.eq_of_eqOn_cones`: two right-finite functions on `M` that coincide on
  `m C_m` for a cone `C_m` for every `m ∈ M` are equal;
* `isRightFinite_of_mem_coefficientFunctionSpace`: the elements of `A(π)` for an admissible `π`
  are right finite for every central subgroup;
* `eq_of_mem_coefficientFunctionSpace_of_eqOn_cones`: the uniqueness statement of
  Proposition I.6.2 for elements of `A(M)`.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

universe u v w

section Cone

variable {A : Type u} [Group A]

/-- A function in a finite-dimensional space `W` of functions on a group, stable under right
translations, which vanishes on a nonempty set `C` with `C S ⊆ C` for a set `S` generating the
group, is zero. -/
theorem eq_zero_of_eqOn_cone (W : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ x : A, ∀ φ ∈ W, (fun a => φ (a * x)) ∈ W)
    {S : Set A} (hS : Subgroup.closure S = ⊤)
    {C : Set A} (hC : C.Nonempty) (hCS : ∀ c ∈ C, ∀ s ∈ S, c * s ∈ C)
    {φ : A → ℂ} (hφ : φ ∈ W) (hφC : ∀ c ∈ C, φ c = 0) : φ = 0 := by
  let W₀ : Submodule ℂ (A → ℂ) :=
    { carrier := {ψ | ψ ∈ W ∧ ∀ c ∈ C, ψ c = 0}
      add_mem' := fun {ψ ψ'} hψ hψ' =>
        ⟨W.add_mem hψ.1 hψ'.1, fun c hc => by simp [hψ.2 c hc, hψ'.2 c hc]⟩
      zero_mem' := ⟨W.zero_mem, fun c _ => rfl⟩
      smul_mem' := fun r ψ hψ => ⟨W.smul_mem r hψ.1, fun c hc => by simp [hψ.2 c hc]⟩ }
  have hW₀ : W₀ ≤ W := fun ψ hψ => hψ.1
  have : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_of_le hW₀
  have hR : ∀ s ∈ S, ∀ ψ ∈ W₀, (fun a => ψ (a * s)) ∈ W₀ := fun s hs ψ hψ =>
    ⟨hW s ψ hψ.1, fun c hc => hψ.2 _ (hCS c hc s hs)⟩
  let R : ∀ s ∈ S, W₀ →ₗ[ℂ] W₀ := fun s hs =>
    { toFun := fun ψ => ⟨fun a => ψ.1 (a * s), hR s hs ψ.1 ψ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : ∀ s (hs : s ∈ S), Function.Injective (R s hs) := by
    intro s hs ψ ψ' h
    apply Subtype.ext
    funext a
    have h1 : ψ.1 (a * s⁻¹ * s) = ψ'.1 (a * s⁻¹ * s) :=
      congrFun (congrArg Subtype.val h) (a * s⁻¹)
    rwa [inv_mul_cancel_right] at h1
  have hRinv : ∀ s ∈ S, ∀ ψ ∈ W₀, (fun a => ψ (a * s⁻¹)) ∈ W₀ := by
    intro s hs ψ hψ
    obtain ⟨ψ', hψ'⟩ := (LinearMap.injective_iff_surjective.mp (hinj s hs)) ⟨ψ, hψ⟩
    have e : (fun a => ψ (a * s⁻¹)) = ψ'.1 := by
      funext a
      have h1 : ψ'.1 (a * s⁻¹ * s) = ψ (a * s⁻¹) :=
        congrFun (congrArg Subtype.val hψ') (a * s⁻¹)
      rw [inv_mul_cancel_right] at h1
      exact h1.symm
    rw [e]
    exact ψ'.2
  have hall : ∀ x : A, ∀ ψ ∈ W₀, (fun a => ψ (a * x)) ∈ W₀ := by
    intro x
    have hx : x ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction'' with
    | mem s hs => exact hR s hs
    | inv_mem s hs => exact hRinv s hs
    | one => intro ψ hψ; simpa using hψ
    | mul x y _ _ hx hy =>
      intro ψ hψ
      have h := hx _ (hy ψ hψ)
      simpa [mul_assoc] using h
  obtain ⟨c, hc⟩ := hC
  funext a
  have h := (hall (c⁻¹ * a) φ ⟨hφ, hφC⟩).2 c hc
  simpa using h

end Cone

section RightFinite

variable {M : Type v} [Group M]

/-- A function `φ` on `M` is *right finite* for a subgroup `A` if it lies in a
finite-dimensional space of functions on `M` that is stable under right translation by the
elements of `A`. For `A = A_M` this is Waldspurger's `A_M`-finiteness (I.6, proof of
Proposition I.6.2). -/
def IsRightFinite (A : Subgroup M) (φ : M → ℂ) : Prop :=
  ∃ V : Submodule ℂ (M → ℂ), FiniteDimensional ℂ V ∧ φ ∈ V ∧
    ∀ x ∈ A, ∀ ψ ∈ V, (fun m => ψ (m * x)) ∈ V

theorem isRightFinite_zero (A : Subgroup M) : IsRightFinite A 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun x _ ψ hψ => by
    rw [Submodule.mem_bot] at hψ ⊢
    subst hψ
    rfl⟩

theorem IsRightFinite.add {A : Subgroup M} {φ φ' : M → ℂ} (hφ : IsRightFinite A φ)
    (hφ' : IsRightFinite A φ') : IsRightFinite A (φ + φ') := by
  obtain ⟨V, hV, hφV, hVA⟩ := hφ
  obtain ⟨V', hV', hφV', hVA'⟩ := hφ'
  refine ⟨V ⊔ V', inferInstance, Submodule.add_mem_sup hφV hφV', fun x hx ψ hψ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hψ
  exact Submodule.add_mem_sup (hVA x hx y hy) (hVA' x hx z hz)

theorem IsRightFinite.smul {A : Subgroup M} {φ : M → ℂ} (hφ : IsRightFinite A φ) (c : ℂ) :
    IsRightFinite A (c • φ) := by
  obtain ⟨V, hV, hφV, hVA⟩ := hφ
  exact ⟨V, hV, V.smul_mem c hφV, hVA⟩

theorem IsRightFinite.sub {A : Subgroup M} {φ φ' : M → ℂ} (hφ : IsRightFinite A φ)
    (hφ' : IsRightFinite A φ') : IsRightFinite A (φ - φ') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ φ']
  exact hφ.add (hφ'.smul (-1))

/-- **Uniqueness in Proposition I.6.2, abstract form.** Let `A` be a subgroup of `M` and `S` a
subset generating `A`. Two right-finite functions `f`, `f'` such that for every `m ∈ M` there is
a nonempty `C ⊆ A` with `C S ⊆ C` and `f (m c) = f' (m c)` for all `c ∈ C` are equal. -/
theorem IsRightFinite.eq_of_eqOn_cones {A : Subgroup M} {f f' : M → ℂ}
    (hf : IsRightFinite A f) (hf' : IsRightFinite A f')
    {S : Set A} (hS : Subgroup.closure S = ⊤)
    (h : ∀ m : M, ∃ C : Set A, C.Nonempty ∧ (∀ c ∈ C, ∀ s ∈ S, c * s ∈ C) ∧
      ∀ c ∈ C, f (m * c) = f' (m * c)) :
    f = f' := by
  obtain ⟨V, hV, hgV, hVA⟩ := hf.sub hf'
  funext m
  obtain ⟨C, hC, hCS, hfC⟩ := h m
  let Φ : (M → ℂ) →ₗ[ℂ] (A → ℂ) :=
    { toFun := fun ψ a => ψ (m * a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hW : ∀ x : A, ∀ φ ∈ V.map Φ, (fun a => φ (a * x)) ∈ V.map Φ := by
    rintro x _ ⟨ψ, hψ, rfl⟩
    refine ⟨fun m' => ψ (m' * x), hVA x x.property ψ hψ, ?_⟩
    funext a
    change ψ (m * a * x) = ψ (m * (a * x))
    rw [mul_assoc]
  have h0 := eq_zero_of_eqOn_cone (V.map Φ) hW hS hC hCS (Submodule.mem_map_of_mem hgV)
    (fun c hc => by
      change (f - f') (m * c) = 0
      rw [Pi.sub_apply, hfC c hc, sub_self])
  have h1 := congrFun h0 1
  change (f - f') (m * 1) = 0 at h1
  rw [mul_one, Pi.sub_apply, sub_eq_zero] at h1
  exact h1

/-- A coefficient `m ↦ ℓ(π(m) v)` of a representation is right finite for `A` when the vectors
`π(a) v`, `a ∈ A`, span a finite-dimensional space. Here `ℓ` is any linear functional. -/
theorem isRightFinite_coefficient {X : Type w} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ M X) (A : Subgroup M) (ℓ : Module.Dual ℂ X) (v : X)
    (hv : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : A => π a v))) :
    IsRightFinite A (fun m => ℓ (π m v)) := by
  set E := Submodule.span ℂ (Set.range fun a : A => π a v) with hE
  have hEinv : ∀ x ∈ A, ∀ u ∈ E, π x u ∈ E := by
    intro x hx u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      refine Submodule.subset_span ⟨⟨x * a, A.mul_mem hx a.property⟩, ?_⟩
      change π (x * a) v = π x (π a v)
      rw [map_mul, Module.End.mul_apply]
    | zero => rw [map_zero]; exact E.zero_mem
    | add y z _ _ hy hz => rw [map_add]; exact E.add_mem hy hz
    | smul c y _ hy => rw [map_smul]; exact E.smul_mem c hy
  refine ⟨E.map (matrixCoefficient π ℓ), inferInstance, ?_, ?_⟩
  · refine ⟨v, Submodule.subset_span ⟨1, by simp⟩, ?_⟩
    rfl
  · rintro x hx _ ⟨u, hu, rfl⟩
    refine ⟨π x u, hEinv x hx u hu, ?_⟩
    funext m
    change ℓ (π m (π x u)) = ℓ (π (m * x) u)
    rw [map_mul, Module.End.mul_apply]

end RightFinite

section Coefficients

variable {M : Type u} [Group M] [TopologicalSpace M]

/-- The elements of `A(π)` for an admissible `π` are right finite for every central subgroup
`Z`: the translates `π(z) x` of a vector `x` fixed by an open subgroup `U` stay in the
finite-dimensional space of `U`-fixed vectors. -/
theorem isRightFinite_of_mem_coefficientFunctionSpace {B : SmoothRep.{0, u, v} ℂ M}
    (hB : IsAdmissible B.representation) (Z : Subgroup M)
    (hZ : ∀ z ∈ Z, ∀ m : M, z * m = m * z) {f : M → ℂ}
    (hf : f ∈ coefficientFunctionSpace B) : IsRightFinite Z f := by
  unfold coefficientFunctionSpace at hf
  induction hf using Submodule.iSup_induction' with
  | mem ℓ φ hφ =>
    obtain ⟨x, rfl⟩ := hφ
    obtain ⟨U, hU⟩ := hB.1 x
    have hle : Submodule.span ℂ (Set.range fun a : Z => B.representation a x) ≤
        fixedVectors B.representation U.toSubgroup := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩ k
      change B.representation k (B.representation a x) = B.representation a x
      rw [← Module.End.mul_apply, ← map_mul, ← hZ a a.property k, map_mul, Module.End.mul_apply]
      exact congrArg (B.representation a) (hU k)
    have : FiniteDimensional ℂ (fixedVectors B.representation U.toSubgroup) := hB.2 U
    have := Submodule.finiteDimensional_of_le hle
    exact isRightFinite_coefficient B.representation Z ℓ.val x inferInstance
  | zero => exact isRightFinite_zero Z
  | add φ φ' _ _ hφ hφ' => exact hφ.add hφ'

/-- **Uniqueness in Waldspurger's Proposition I.6.2** for elements of `A(M)`: let `Z` be a
central subgroup of `M` and `S` a subset generating `Z`. Two elements `f`, `f'` of `A(M)` (each
in `A(π)` for some admissible `π`) such that for every `m ∈ M` there is a nonempty `C ⊆ Z` with
`C S ⊆ C` and `f (m c) = f' (m c)` for all `c ∈ C` are equal. -/
theorem eq_of_mem_coefficientFunctionSpace_of_eqOn_cones (Z : Subgroup M)
    (hZ : ∀ z ∈ Z, ∀ m : M, z * m = m * z) {f f' : M → ℂ}
    (hf : ∃ B : SmoothRep.{0, u, v} ℂ M, IsAdmissible B.representation ∧
      f ∈ coefficientFunctionSpace B)
    (hf' : ∃ B : SmoothRep.{0, u, w} ℂ M, IsAdmissible B.representation ∧
      f' ∈ coefficientFunctionSpace B)
    {S : Set Z} (hS : Subgroup.closure S = ⊤)
    (h : ∀ m : M, ∃ C : Set Z, C.Nonempty ∧ (∀ c ∈ C, ∀ s ∈ S, c * s ∈ C) ∧
      ∀ c ∈ C, f (m * c) = f' (m * c)) :
    f = f' := by
  obtain ⟨B, hB, hfB⟩ := hf
  obtain ⟨B', hB', hfB'⟩ := hf'
  exact (isRightFinite_of_mem_coefficientFunctionSpace hB Z hZ hfB).eq_of_eqOn_cones
    (isRightFinite_of_mem_coefficientFunctionSpace hB' Z hZ hfB') hS h

end Coefficients

end Langlands.HarishChandraSchwartz
