import Langlands.Representation.CuspidalSupport.NormalHeckeCenter
import Langlands.Algebra.RankOneGradedLagrangian

/-!
# Stabilizers of lines in `Hom(ρ, Res π)` through `End(ind_H^G ρ)`

Let `H` be an open normal subgroup of `G`, `ρ` an irreducible smooth representation of `H`,
`p : G → ι` a degree for `H`, and `π` a smooth representation of `G`. Frobenius reciprocity
`e : Hom(ind_H^G ρ, π) ≃ Hom_H(ρ, π)` turns the right action of `End(ind_H^G ρ)` into an
action on `Hom_H(ρ, π)`; for `α` in the piece of degree `p g`,
`e(α ≫ φ)(w) = π(g⁻¹) (e φ (φ_α(g) w))` (`hom_inducedLiftHomEquiv_comp`).

For an injective `j : ρ → π|_H` with image `W`, this translates the conditions of Renard
VI.4.4, Lemma, into the line `ℂ e⁻¹(j)`:

* `inN_iff`: `ρ^g ≅ ρ` iff the piece of degree `p g` is nonzero;
* `inH_iff`: `π(g) W = W` iff that piece is nonzero and acts on `e⁻¹(j)` by scalars;
* `mul_comm_of_inHtilde`, `inHtilde_of_commute`: `ρ_H^g ≅ ρ_H` iff the piece of degree `p g`
  is nonzero and commutes (in its action on `Hom(ind_H^G ρ, π)`) with the pieces stabilizing
  the line.

`lineStabilizer` combines these with `Langlands.RankOneGraded.IsRankOneGrading.stab` and
`perp` (module `Langlands.Algebra.RankOneGradedLagrangian`) to prove Renard VI.4.4, Lemma, for
an open normal subgroup with a degree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Subgroup G} (ρ : SmoothRep.{0, uG, uV} ℂ H) (hH : IsOpen (H : Set G))
variable {ι : Type*} [AddCommGroup ι] {p : G → ι} (hp : IsDegree H p)

section Values

include hp

/-- A nonzero element of the piece of degree `p g` has a nonzero value at `g`. -/
theorem endValue_ne_zero_of_mem_component {g : G} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p (p g)) (h0 : α ≠ 0) : endValue H ρ hH α g ≠ 0 := by
  intro hg
  apply h0
  refine end_ext H ρ hH fun x w => ?_
  rw [endValue_zero]
  by_cases hx : p x = p g
  · have hk := hp.inv_mul_mem hx
    have hgk : x = g * ((⟨g⁻¹ * x, hk⟩ : H) : G) := by simp
    rw [hgk, endValue_mul_right, hg, LinearMap.zero_apply, LinearMap.zero_apply]
  · rw [hα x hx, LinearMap.zero_apply]

variable [hN : H.Normal]

/-- An element of the piece of degree `p g` with a prescribed value `A` at `g`, for `A`
intertwining `ρ^g` (`ρ^g(y) = ρ(g⁻¹ y g)`) with `ρ`, written as `A ρ(y) = ρ(x) A` whenever
`y = g⁻¹ x g`. -/
theorem exists_mem_component_endValue_eq (g : G) (A : Module.End ℂ ρ)
    (hA : ∀ x y : H, (y : G) = g⁻¹ * x * g →
      A * ρ.representation y = ρ.representation x * A) :
    ∃ α ∈ component H ρ hH p (p g), endValue H ρ hH α g = A := by
  classical
  have hT : ∀ h k : H, (k : G) = g⁻¹⁻¹ * h * g⁻¹ →
      ρ.representation k * A = A * ρ.representation h :=
    fun h k hk => (hA k h (by rw [hk]; group)).symm
  let α := endOfHecke H ρ hH ⟨_, inverseFunction_mem g⁻¹ A hT⟩
  have hα : ∀ x, endValue H ρ hH α x =
      if hx : x * g⁻¹ ∈ H then ρ.representation ⟨x * g⁻¹, hx⟩ * A else 0 :=
    fun x => LinearMap.ext fun w => endValue_endOfHecke H ρ hH _ x w
  refine ⟨α, fun x hx => ?_, ?_⟩
  · have hnot : x * g⁻¹ ∉ H := fun hmem => hx (by
      have h1 := hp.map_mem hmem
      rw [hp.map_mul, hp.map_inv] at h1
      exact add_neg_eq_zero.mp h1)
    rw [hα, dite_eq_right_iff.mpr fun h => absurd h hnot]
  · have hmem : g * g⁻¹ ∈ H := by rw [mul_inv_cancel]; exact H.one_mem
    have h1 : (⟨g * g⁻¹, hmem⟩ : H) = 1 := Subtype.ext (mul_inv_cancel g)
    simp only [hα, hmem, dite_true, h1, map_one, one_mul]

end Values

section Frobenius

variable (π : SmoothRep.{0, uG, uV} ℂ G)

include hp in
/-- **Frobenius reciprocity and the grading.** For `α` in the piece of degree `p g`,
`e(α ≫ φ)(w) = π(g⁻¹) (e φ (φ_α(g) w))`. -/
theorem hom_inducedLiftHomEquiv_comp {g : G} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p (p g))
    (φ : inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) (w : ρ) :
    SmoothRep.hom (inducedLiftHomEquiv H ρ hH π (α ≫ φ)) w =
      π.representation g⁻¹
        (SmoothRep.hom (inducedLiftHomEquiv H ρ hH π φ) (endValue H ρ hH α g w)) := by
  have hF : ∀ x, x * g⁻¹ ∉ H → eval H ρ.representation
      (SmoothRep.hom α (unitFunction H hH ρ.representation ρ.isSmooth w)).1 x = 0 := by
    intro x hx
    refine congrArg (fun T : Module.End ℂ ρ => T w) (hα x fun hpx => hx ?_)
    rw [← hp.eq_zero_iff, hp.map_mul, hp.map_inv, hpx, add_neg_cancel]
  rw [hom_inducedLiftHomEquiv_apply, hom_inducedLiftHomEquiv_apply]
  change (SmoothRep.hom φ (SmoothRep.hom α _)).down = _
  rw [hom_of_support hH φ _ hF]
  rfl

variable {π}

omit [IsTopologicalGroup G] in
theorem smul_hom_apply (c : ℂ) (f : ρ ⟶ SmoothRep.restrictSubgroup H π) (w : ρ) :
    SmoothRep.hom (c • f) w = c • SmoothRep.hom f w :=
  rfl

omit [IsTopologicalGroup G] in
theorem restrict_hom_ext {f f' : ρ ⟶ SmoothRep.restrictSubgroup H π}
    (h : ∀ w, SmoothRep.hom f w = SmoothRep.hom f' w) : f = f' := by
  rw [← SmoothRep.ofHom_hom f, ← SmoothRep.ofHom_hom f']
  congr 1
  exact Representation.IntertwiningMap.ext (LinearMap.ext h)

omit [IsTopologicalGroup G] in
theorem hom_restrict_apply (j : ρ ⟶ SmoothRep.restrictSubgroup H π) (y : H) (w : ρ) :
    SmoothRep.hom j (ρ.representation y w) = π.representation y (SmoothRep.hom j w) :=
  LinearMap.congr_fun ((SmoothRep.hom j).isIntertwining' y) w

variable [hN : H.Normal] [ρ.representation.IsIrreducible]

include hp in
/-- If `π(k)` maps the image of an injective `j` into itself, some element `α` of the piece of
degree `p k` satisfies `j(φ_α(k) w) = π(k) j(w)` and fixes `e⁻¹(j)`. -/
theorem exists_mem_component_comp_eq_self (j : ρ ⟶ SmoothRep.restrictSubgroup H π)
    (hj : Function.Injective (SmoothRep.hom j)) {k : G}
    (hk : ∀ w, ∃ w', SmoothRep.hom j w' = π.representation k (SmoothRep.hom j w)) :
    ∃ α ∈ component H ρ hH p (p k), α ≠ 0 ∧
      (∀ w, SmoothRep.hom j (endValue H ρ hH α k w) =
        π.representation k (SmoothRep.hom j w)) ∧
      α ≫ (inducedLiftHomEquiv H ρ hH π).symm j = (inducedLiftHomEquiv H ρ hH π).symm j := by
  choose r hr using hk
  let R : Module.End ℂ ρ :=
    { toFun := r
      map_add' := fun a b => hj (by
        simp only [hr, map_add]
        exact map_add (π.representation k) _ _)
      map_smul' := fun c a => hj (by
        simp only [hr, map_smul, RingHom.id_apply]
        exact map_smul (π.representation k) _ _) }
  have hR : ∀ w, SmoothRep.hom j (R w) = π.representation k (SmoothRep.hom j w) := hr
  have hA : ∀ x y : H, (y : G) = k⁻¹ * x * k →
      R * ρ.representation y = ρ.representation x * R := by
    intro x y hy
    refine LinearMap.ext fun w => hj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hR, hom_restrict_apply,
      hom_restrict_apply, hR]
    have hky : k * (y : G) = x * k := by rw [hy]; group
    rw [← Module.End.mul_apply (π.representation k), ← map_mul, hky, map_mul,
      Module.End.mul_apply]
  obtain ⟨α, hα, hαk⟩ := exists_mem_component_endValue_eq ρ hH hp k R hA
  have hval : ∀ w, SmoothRep.hom j (endValue H ρ hH α k w) =
      π.representation k (SmoothRep.hom j w) := fun w => by rw [hαk]; exact hR w
  refine ⟨α, hα, ?_, hval, ?_⟩
  · rintro rfl
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
    have h1 := hval w
    rw [endValue_zero, LinearMap.zero_apply, map_zero] at h1
    apply hw
    apply hj
    rw [map_zero, ← Representation.inv_self_apply π.representation k (SmoothRep.hom j w), ← h1]
    exact map_zero (π.representation k⁻¹)
  · apply (inducedLiftHomEquiv H ρ hH π).injective
    refine restrict_hom_ext ρ fun w => ?_
    rw [hom_inducedLiftHomEquiv_comp ρ hH hp π hα, LinearEquiv.apply_symm_apply, hval,
      Representation.inv_self_apply]

end Frobenius

section Line

variable {π : SmoothRep.{0, uG, uV} ℂ G}

omit [IsTopologicalGroup G] in
theorem zero_hom_apply (w : ρ) :
    SmoothRep.hom (0 : ρ ⟶ SmoothRep.restrictSubgroup H π) w = 0 :=
  rfl

omit [IsTopologicalGroup G] in
theorem rep_mul_apply (a b : G) (v : π) :
    π.representation a (π.representation b v) = π.representation (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

omit [IsTopologicalGroup G] in
theorem eq_zero_of_rep_apply_eq_zero {g : G} {v : π} (h : π.representation g v = 0) : v = 0 := by
  rw [← Representation.inv_self_apply π.representation g v, h]
  exact map_zero (π.representation g⁻¹)

omit [IsTopologicalGroup G] in
/-- `π(k) W = W` for `k ∈ H` and `W` the image of a map `ρ → π|_H`. -/
theorem inH_of_mem (j : ρ ⟶ SmoothRep.restrictSubgroup H π) {k : G} (hk : k ∈ H) (v : π) :
    (∃ w, SmoothRep.hom j w = v) ↔ ∃ w, SmoothRep.hom j w = π.representation k v := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨ρ.representation ⟨k, hk⟩ w, hom_restrict_apply ρ j ⟨k, hk⟩ w⟩
  · rintro ⟨w, hw⟩
    refine ⟨ρ.representation ⟨k⁻¹, H.inv_mem hk⟩ w, ?_⟩
    rw [hom_restrict_apply, hw]
    exact Representation.inv_self_apply π.representation k v

variable [hN : H.Normal] [ρ.representation.IsIrreducible]

omit [IsTopologicalGroup G] hN in
/-- A nonzero map out of the irreducible `ρ` is injective. -/
theorem injective_of_ne_zero (j : ρ ⟶ SmoothRep.restrictSubgroup H π) (hj : j ≠ 0) :
    Function.Injective (SmoothRep.hom j) := by
  intro a b hab
  by_contra hne
  apply hj
  have h0 : SmoothRep.hom j (a - b) = 0 := by rw [map_sub, hab, sub_self]
  refine restrict_hom_ext ρ fun v => ?_
  have hv := mem_of_isIrreducible ρ.representation (LinearMap.ker (SmoothRep.hom j).toLinearMap)
    (fun k v hv => ?_) (LinearMap.mem_ker.mpr h0) (sub_ne_zero.mpr hne) v
  · exact LinearMap.mem_ker.mp hv
  · rw [LinearMap.mem_ker] at hv ⊢
    change SmoothRep.hom j (ρ.representation k v) = 0
    rw [hom_restrict_apply]
    change π.representation k (SmoothRep.hom j v) = 0
    rw [show SmoothRep.hom j v = 0 from hv]
    exact map_zero (π.representation k)

include hp in
/-- **The stabilizer `N` of the class of `ρ`.** `ρ^g ≅ ρ` if and only if the piece of degree
`p g` is nonzero. -/
theorem inN_iff (g : G) :
    (∃ A : ρ ≃ₗ[ℂ] ρ, ∀ x y : H, (y : G) = g⁻¹ * x * g →
      ∀ w : ρ, A (ρ.representation y w) = ρ.representation x (A w)) ↔
    ∃ α ∈ component H ρ hH p (p g), α ≠ 0 := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨α, hα, hαA⟩ := exists_mem_component_endValue_eq ρ hH hp g A.toLinearMap
      fun x y hy => LinearMap.ext fun w => hA x y hy w
    refine ⟨α, hα, ?_⟩
    rintro rfl
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
    have h1 := LinearMap.congr_fun hαA w
    rw [endValue_zero, LinearMap.zero_apply] at h1
    exact hw (A.injective (h1.symm.trans (map_zero A).symm))
  · rintro ⟨α, hα, hα0⟩
    have h0 := endValue_ne_zero_of_mem_component ρ hH hp hα hα0
    refine ⟨LinearEquiv.ofBijective _ (bijective_endValue H ρ hH α g h0), fun x y hy w => ?_⟩
    exact endValue_conj H ρ hH α g y x (by rw [hy]; group) w

omit hN [ρ.representation.IsIrreducible] in
include hp in
theorem hom_comp_symm_apply {g : G} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p (p g)) (j : ρ ⟶ SmoothRep.restrictSubgroup H π) (w : ρ) :
    SmoothRep.hom (inducedLiftHomEquiv H ρ hH π (α ≫ (inducedLiftHomEquiv H ρ hH π).symm j)) w =
      π.representation g⁻¹ (SmoothRep.hom j (endValue H ρ hH α g w)) := by
  rw [hom_inducedLiftHomEquiv_comp ρ hH hp π hα, LinearEquiv.apply_symm_apply]

variable (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0)

include hp hrank in
/-- **The stabilizer `H` of the image.** For injective `j` with image `W`, `π(g) W = W` if and
only if the piece of degree `p g` is nonzero and acts on `e⁻¹(j)` by scalars. -/
theorem inH_iff (j : ρ ⟶ SmoothRep.restrictSubgroup H π)
    (hj : Function.Injective (SmoothRep.hom j)) (g : G) :
    (∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔ ∃ w, SmoothRep.hom j w = π.representation g v) ↔
      (∃ α ∈ component H ρ hH p (p g), α ≠ 0) ∧ ∀ u ∈ component H ρ hH p (p g), ∃ c : ℂ,
        u ≫ (inducedLiftHomEquiv H ρ hH π).symm j =
          c • (inducedLiftHomEquiv H ρ hH π).symm j := by
  classical
  constructor
  · intro h
    obtain ⟨α, hα, hα0, -, hαx⟩ := exists_mem_component_comp_eq_self ρ hH hp j hj
      fun w => (h (SmoothRep.hom j w)).mp ⟨w, rfl⟩
    refine ⟨⟨α, hα, hα0⟩, fun u hu => ?_⟩
    let _ := gradedAlgebra ρ hH hp
    obtain ⟨c, rfl⟩ := (isRankOneGrading ρ hH hp hrank).exists_smul_eq hα hα0 hu
    exact ⟨c, by rw [Linear.smul_comp, hαx]⟩
  · rintro ⟨⟨α, hα, hα0⟩, hu⟩
    obtain ⟨c, hc⟩ := hu α hα
    have h0 := endValue_ne_zero_of_mem_component ρ hH hp hα hα0
    obtain ⟨-, hsurj⟩ := bijective_endValue H ρ hH α g h0
    have hkey : ∀ w, SmoothRep.hom j (endValue H ρ hH α g w) =
        c • π.representation g (SmoothRep.hom j w) := by
      intro w
      have h1 := hom_comp_symm_apply ρ hH hp hα j w
      rw [hc, map_smul, smul_hom_apply, LinearEquiv.apply_symm_apply] at h1
      have h2 := congrArg (π.representation g) h1
      rw [Representation.self_inv_apply] at h2
      rw [← h2]
      exact map_smul (π.representation g) c (SmoothRep.hom j w)
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply h0
      refine LinearMap.ext fun w => hj ?_
      rw [hkey, zero_smul, LinearMap.zero_apply, map_zero]
      rfl
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨c⁻¹ • endValue H ρ hH α g w, ?_⟩
      rw [map_smul, hkey]
      change c⁻¹ • c • π.representation g (SmoothRep.hom j w) = _
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rintro ⟨w, hw⟩
      obtain ⟨w₀, hw₀⟩ := hsurj (c • w)
      refine ⟨w₀, ?_⟩
      have h1 := hkey w₀
      rw [hw₀, map_smul, hw] at h1
      have h4 := smul_right_injective _ hc0 h1
      rw [← Representation.inv_self_apply π.representation g v, h4]
      exact (Representation.inv_self_apply π.representation g _).symm

omit [IsTopologicalGroup G] hN [ρ.representation.IsIrreducible] in
/-- If `ρ_H^g ≅ ρ_H` through `A`, then `ρ^g ≅ ρ` through `A`. -/
theorem inN_of_inHtilde (j : ρ ⟶ SmoothRep.restrictSubgroup H π)
    (hj : Function.Injective (SmoothRep.hom j)) {g : G} (A : ρ ≃ₗ[ℂ] ρ)
    (hA : ∀ k : G, (∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔
        ∃ w, SmoothRep.hom j w = π.representation k v) →
      ∀ w w' : ρ, SmoothRep.hom j w' = π.representation (g⁻¹ * k * g) (SmoothRep.hom j w) →
        π.representation k (SmoothRep.hom j (A w)) = SmoothRep.hom j (A w'))
    (x y : H) (hy : (y : G) = g⁻¹ * x * g) (w : ρ) :
    A (ρ.representation y w) = ρ.representation x (A w) := by
  apply hj
  rw [hom_restrict_apply]
  refine (hA x (inH_of_mem ρ j x.2) w (ρ.representation y w) ?_).symm
  rw [hom_restrict_apply, hy]

omit [IsTopologicalGroup G] in
theorem rep_apply_congr {a b : G} (h : a = b) (v : π) :
    π.representation a v = π.representation b v := by
  rw [h]

omit [IsTopologicalGroup G] in
theorem eq_rep_apply_of_rep_apply_eq {a b : G} {v w : π}
    (h : π.representation a v = π.representation b w) :
    v = π.representation (a⁻¹ * b) w := by
  rw [← rep_mul_apply, ← h, Representation.inv_self_apply]

include hp hrank in
/-- **`H̃` commutes with `H`.** If `ρ_H^g ≅ ρ_H` (through `A`), then every element of the piece of
degree `p g` commutes with every element of the piece of degree `p k`, for `π(k) W = W`. -/
theorem mul_comm_of_inHtilde (j : ρ ⟶ SmoothRep.restrictSubgroup H π)
    (hj : Function.Injective (SmoothRep.hom j)) {g : G} (A : ρ ≃ₗ[ℂ] ρ)
    (hA : ∀ k : G, (∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔
        ∃ w, SmoothRep.hom j w = π.representation k v) →
      ∀ w w' : ρ, SmoothRep.hom j w' = π.representation (g⁻¹ * k * g) (SmoothRep.hom j w) →
        π.representation k (SmoothRep.hom j (A w)) = SmoothRep.hom j (A w'))
    {k : G} (hk : ∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔
        ∃ w, SmoothRep.hom j w = π.representation k v)
    {u v : End (inducedRep H ρ)} (hu : u ∈ component H ρ hH p (p g))
    (hv : v ∈ component H ρ hH p (p k)) : u * v = v * u := by
  classical
  have hAN := inN_of_inHtilde ρ j hj A hA
  obtain ⟨α, hα, hαA⟩ := exists_mem_component_endValue_eq ρ hH hp g A.toLinearMap
    fun x y hy => LinearMap.ext fun w => hAN x y hy w
  obtain ⟨w₀, hw₀⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 := LinearMap.congr_fun hαA w₀
    rw [endValue_zero, LinearMap.zero_apply] at h1
    exact hw₀ (A.injective (h1.symm.trans (map_zero A).symm))
  obtain ⟨β, hβ, hβ0, hβk, hβx⟩ := exists_mem_component_comp_eq_self ρ hH hp j hj
    fun w => (hk (SmoothRep.hom j w)).mp ⟨w, rfl⟩
  have hαx : ∀ w, SmoothRep.hom (inducedLiftHomEquiv H ρ hH π
      (α ≫ (inducedLiftHomEquiv H ρ hH π).symm j)) w =
        π.representation g⁻¹ (SmoothRep.hom j (A w)) := by
    intro w
    rw [hom_comp_symm_apply ρ hH hp hα j w, hαA]
    rfl
  have hpk : p (g * k * g⁻¹) = p k := by
    rw [hp.map_mul, hp.map_mul, hp.map_inv]
    abel
  have hk' := (inH_iff ρ hH hp hrank j hj (g * k * g⁻¹)).mpr
    (by rw [hpk]; exact (inH_iff ρ hH hp hrank j hj k).mp hk)
  have hβα : β ≫ (α ≫ (inducedLiftHomEquiv H ρ hH π).symm j) =
      α ≫ (inducedLiftHomEquiv H ρ hH π).symm j := by
    apply (inducedLiftHomEquiv H ρ hH π).injective
    refine restrict_hom_ext ρ fun w => ?_
    rw [hom_inducedLiftHomEquiv_comp ρ hH hp π hβ, hαx, hαx]
    have hgk : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    have h1 := hA (g * k * g⁻¹) hk' w (endValue H ρ hH β k w) (by rw [hgk, hβk])
    rw [← h1]
    simp only [rep_mul_apply]
    exact rep_apply_congr (by group) _
  let _ := gradedAlgebra ρ hH hp
  have h𝒜 := isRankOneGrading ρ hH hp hrank
  have hab : α * β ∈ component H ρ hH p (p g + p k) := mul_mem_component hH hp hα hβ
  have hba : β * α ∈ component H ρ hH p (p g + p k) := by
    rw [add_comm]
    exact mul_mem_component hH hp hβ hα
  obtain ⟨c, hc⟩ := h𝒜.exists_smul_eq hab (h𝒜.mul_ne_zero hα hα0 hβ0) hba
  have hx0 : α ≫ (inducedLiftHomEquiv H ρ hH π).symm j ≠ 0 := by
    intro h0
    apply hw₀
    apply A.injective
    apply hj
    have h1 := hαx w₀
    rw [h0, map_zero, zero_hom_apply] at h1
    have h2 : SmoothRep.hom j (A w₀) = 0 :=
      eq_zero_of_rep_apply_eq_zero (π := π) (g := g⁻¹) h1.symm
    rw [h2, map_zero, map_zero]
  have hc1 : c = 1 := by
    have h1 : c • (α ≫ (inducedLiftHomEquiv H ρ hH π).symm j) =
        α ≫ (inducedLiftHomEquiv H ρ hH π).symm j := by
      have h2 : (c • (α * β)) ≫ (inducedLiftHomEquiv H ρ hH π).symm j =
          (β * α) ≫ (inducedLiftHomEquiv H ρ hH π).symm j := by rw [hc]
      rw [Linear.smul_comp, End.mul_def, End.mul_def, Category.assoc, Category.assoc, hβx,
        hβα] at h2
      exact h2
    exact smul_left_injective ℂ hx0 (h1.trans (one_smul ℂ _).symm)
  have hαβ : α * β = β * α := by rw [← hc, hc1, one_smul]
  obtain ⟨a, rfl⟩ := h𝒜.exists_smul_eq hα hα0 hu
  obtain ⟨b, rfl⟩ := h𝒜.exists_smul_eq hβ hβ0 hv
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hαβ, mul_comm a b]

include hp hrank in
/-- **Commuting with `H` gives `H̃`.** If a nonzero `α` of degree `p g` commutes, in its action on
`Hom(ind_H^G ρ, π)`, with the pieces of degree `p k` for every `k` with `π(k) W = W`, then
`ρ_H^g ≅ ρ_H` through `φ_α(g)`. -/
theorem inHtilde_of_commute (j : ρ ⟶ SmoothRep.restrictSubgroup H π)
    (hj : Function.Injective (SmoothRep.hom j)) {g : G} {α : End (inducedRep H ρ)}
    (hα : α ∈ component H ρ hH p (p g)) (hα0 : α ≠ 0)
    (hcomm : ∀ k : G, (∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔
        ∃ w, SmoothRep.hom j w = π.representation k v) →
      ∀ v ∈ component H ρ hH p (p k),
        homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) α *
            homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) v =
          homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) v *
            homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) α) :
    ∃ A : ρ ≃ₗ[ℂ] ρ, ∀ k : G, (∀ v : π, (∃ w, SmoothRep.hom j w = v) ↔
        ∃ w, SmoothRep.hom j w = π.representation k v) →
      ∀ w w' : ρ, SmoothRep.hom j w' = π.representation (g⁻¹ * k * g) (SmoothRep.hom j w) →
        π.representation k (SmoothRep.hom j (A w)) = SmoothRep.hom j (A w') := by
  have h0 := endValue_ne_zero_of_mem_component ρ hH hp hα hα0
  refine ⟨LinearEquiv.ofBijective _ (bijective_endValue H ρ hH α g h0), fun k hk w w' hw => ?_⟩
  simp only [LinearEquiv.ofBijective_apply]
  have hpk : p (g⁻¹ * k * g) = p k := by
    rw [hp.map_mul, hp.map_mul, hp.map_inv]
    abel
  have hk' := (inH_iff ρ hH hp hrank j hj (g⁻¹ * k * g)).mpr
    (by rw [hpk]; exact (inH_iff ρ hH hp hrank j hj k).mp hk)
  obtain ⟨β, hβ, -, hβk, hβx⟩ := exists_mem_component_comp_eq_self ρ hH hp j hj
    fun w => (hk' (SmoothRep.hom j w)).mp ⟨w, rfl⟩
  have hw' : w' = endValue H ρ hH β (g⁻¹ * k * g) w := hj (by rw [hw, hβk])
  subst hw'
  have h1 := LinearMap.congr_fun (hcomm _ hk' β hβ) ((inducedLiftHomEquiv H ρ hH π).symm j)
  simp only [Module.End.mul_apply, homAction_apply, hβx] at h1
  have h2 := congrArg (fun φ => SmoothRep.hom (inducedLiftHomEquiv H ρ hH π φ) w) h1
  rw [hom_inducedLiftHomEquiv_comp ρ hH hp π hβ, hom_comp_symm_apply ρ hH hp hα,
    hom_comp_symm_apply ρ hH hp hα, rep_mul_apply] at h2
  rw [eq_rep_apply_of_rep_apply_eq h2, rep_mul_apply]
  refine (rep_apply_congr (b := 1) (by group) _).trans ?_
  rw [map_one]
  rfl

end Line

section Degree

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The degree `p`, as a homomorphism to `Multiplicative ι`. -/
def degreeHom : G →* Multiplicative ι where
  toFun g := Multiplicative.ofAdd (p g)
  map_one' := by rw [hp.map_one]; rfl
  map_mul' x y := by rw [hp.map_mul]; rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_comap_degreeHom (S : AddSubgroup ι) (g : G) :
    g ∈ (AddSubgroup.toSubgroup S).comap (degreeHom hp) ↔ p g ∈ S :=
  Iff.rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Relative indices of subgroups of degrees pull back along `p` when the larger one consists of
values of `p`. -/
theorem relIndex_comap_degreeHom (S S' : AddSubgroup ι) (hS' : ∀ a ∈ S', ∃ g, p g = a) :
    ((AddSubgroup.toSubgroup S).comap (degreeHom hp)).relIndex
      ((AddSubgroup.toSubgroup S').comap (degreeHom hp)) = S.relIndex S' := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self, AddSubgroup.relIndex_toSubgroup]
  intro a ha
  obtain ⟨g, hg⟩ := hS' _ ha
  exact ⟨g, congrArg Multiplicative.ofAdd hg⟩

end Degree

section Main

variable [DecidableEq ι] [hN : H.Normal] [ρ.representation.IsIrreducible]
  (hrank : Module.rank ℂ ρ ≤ Cardinal.aleph0)

include hH hp hrank in
/-- **Renard VI.4.4, Lemma, for an open normal subgroup with a degree.** Let `π` be a smooth
representation of `G` such that `Hom(ind_H^G ρ, π)` is finite-dimensional and cyclic over
`End(ind_H^G ρ)`, and twists of `π` are detected on it (`hcyc`, `hiso`, as in
`NormalHecke.mem_radical_iff`), and let `T` be the twist group of `π`. If `ρ` embeds in `π|_H`,
then a good embedding `j` exists, and for every good `j` the stabilizer `H'` of its image
satisfies `T ≤ H' ≤ N`, `[N : H'] = [H' : T] = m = dim Hom_H(ρ, π)`, every map `ρ → π|_H` is
`T`-equivariant for the action of `T` on `ρ` through `j`, and every irreducible `T`-stable
subspace of `π` receiving a nonzero map from `ρ` is isomorphic to `ρ` with that action. -/
theorem lineStabilizer (π : SmoothRep.{0, uG, uV} ℂ G)
    [FiniteDimensional ℂ (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π)]
    (hcyc : ∀ φ : inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π,
      φ ≠ 0 → ∀ ψ : inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π,
        ∃ α : End (inducedRep H ρ), α ≫ φ = ψ)
    (hiso : ∀ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)), H ≤ ω.ker →
      ∀ Ψ : (inducedRep H ρ ⟶
          ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π).twist ω hω) ≃ₗ[ℂ]
          (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π),
        (∀ (α : End (inducedRep H ρ)) φ, Ψ (α ≫ φ) = α ≫ Ψ φ) →
          Nonempty (((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π).twist ω hω ≅
            (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π))
    {T : Subgroup G} (hT : ∀ g, g ∈ T ↔ ∀ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)),
      H ≤ ω.ker → Nonempty (((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π).twist ω hω ≅
        (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) → ω g = 1)
    (hex : ∃ j : ρ ⟶ SmoothRep.restrictSubgroup H π, Function.Injective (SmoothRep.hom j)) :
    let Res := SmoothRep.restrictSubgroup H π
    let InN : G → Prop := fun g =>
      ∃ A : ρ ≃ₗ[ℂ] ρ, ∀ x y : H, (y : G) = g⁻¹ * x * g →
        ∀ w : ρ, A (ρ.representation y w) = ρ.representation x (A w)
    let InH : (ρ ⟶ Res) → G → Prop := fun j g =>
      ∀ v : π, (∃ w : ρ, SmoothRep.hom j w = v) ↔
        ∃ w : ρ, SmoothRep.hom j w = π.representation g v
    let InHtilde : (ρ ⟶ Res) → G → Prop := fun j g =>
      ∃ A : ρ ≃ₗ[ℂ] ρ, ∀ k : G, InH j k →
        ∀ w w' : ρ,
          SmoothRep.hom j w' = π.representation (g⁻¹ * k * g) (SmoothRep.hom j w) →
            π.representation k (SmoothRep.hom j (A w)) = SmoothRep.hom j (A w')
    let Good : (ρ ⟶ Res) → Prop := fun j =>
      Function.Injective (SmoothRep.hom j) ∧ ∀ g, InHtilde j g → InH j g
    let TStable : Submodule ℂ π → Prop := fun E =>
      ∀ t ∈ T, ∀ v ∈ E, π.representation t v ∈ E
    (∃ j : ρ ⟶ Res, Good j) ∧
    ∀ j : ρ ⟶ Res, Good j →
      ∃ (m : ℕ) (H' N : Subgroup G),
        Module.rank ℂ (ρ ⟶ Res) = m ∧
        (∀ g, g ∈ H' ↔ InH j g) ∧ (∀ g, g ∈ N ↔ InN g) ∧
        T ≤ H' ∧ H' ≤ N ∧ H'.relIndex N = m ∧ T.relIndex H' = m ∧
        (∀ ψ : ρ ⟶ Res, ∀ t ∈ T, ∀ w w' : ρ,
          SmoothRep.hom j w' = π.representation t (SmoothRep.hom j w) →
            SmoothRep.hom ψ w' = π.representation t (SmoothRep.hom ψ w)) ∧
        ∀ E : Submodule ℂ π, TStable E → E ≠ ⊥ →
          (∀ E' : Submodule ℂ π, E' ≤ E → TStable E' → E' = ⊥ ∨ E' = E) →
          (∃ ψ : ρ ⟶ Res, ψ ≠ 0 ∧ ∀ w : ρ, SmoothRep.hom ψ w ∈ E) →
          ∃ A : ρ ≃ₗ[ℂ] E, ∀ t ∈ T, ∀ w w' : ρ,
            SmoothRep.hom j w' = π.representation t (SmoothRep.hom j w) →
              ((A w' : E) : π) = π.representation t (A w) := by
  intro Res InN InH InHtilde Good TStable
  classical
  obtain ⟨j₀, hj₀⟩ := hex
  have hsymm0 : ∀ j : ρ ⟶ SmoothRep.restrictSubgroup H π,
      Function.Injective (SmoothRep.hom j) → (inducedLiftHomEquiv H ρ hH π).symm j ≠ 0 := by
    intro j hj h0
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
    apply hw
    apply hj
    have hj0 : j = 0 := by
      rw [← LinearEquiv.apply_symm_apply (inducedLiftHomEquiv H ρ hH π) j, h0, map_zero]
    rw [hj0, zero_hom_apply, map_zero]
  have : Nontrivial
      (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) :=
    ⟨⟨_, 0, hsymm0 j₀ hj₀⟩⟩
  have hinj : ∀ x : inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π,
      x ≠ 0 → Function.Injective (SmoothRep.hom (inducedLiftHomEquiv H ρ hH π x)) :=
    fun x hx => injective_of_ne_zero ρ _
      fun h => hx ((inducedLiftHomEquiv H ρ hH π).map_eq_zero_iff.mp h)
  let _ := gradedAlgebra ρ hH hp
  have := nontrivial_end H ρ hH
  have h𝒜 := isRankOneGrading ρ hH hp hrank
  have hρ1 := homAction_one H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π)
  have hρm := isMulOrAntiMul_homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π)
  have hsurj := surjective_homAction H ρ _ hcyc
  have hdeg : ∀ a ∈ h𝒜.support, ∃ g, p g = a := fun a ha => by
    obtain ⟨α, hα, hα0⟩ := h𝒜.mem_support_iff.mp ha
    exact exists_degree_eq ρ hH hα hα0
  have hstab : ∀ j : ρ ⟶ SmoothRep.restrictSubgroup H π, Function.Injective (SmoothRep.hom j) →
      ∀ g, InH j g ↔ p g ∈ h𝒜.stab (homAction H ρ _) hρ1 hρm
        ((inducedLiftHomEquiv H ρ hH π).symm j) := by
    intro j hj g
    rw [h𝒜.mem_stab_iff, Submodule.ne_bot_iff]
    exact inH_iff ρ hH hp hrank j hj g
  have hNiff : ∀ g, InN g ↔ p g ∈ h𝒜.support := fun g =>
    (inN_iff ρ hH hp g).trans h𝒜.mem_support_iff.symm
  have hrad : ∀ g, g ∈ T ↔ p g ∈ h𝒜.radical :=
    fun g => (hT g).trans (mem_radical_iff ρ hH hp hrank _ hcyc hiso g).symm
  have hperp1 : ∀ j : ρ ⟶ SmoothRep.restrictSubgroup H π, Function.Injective (SmoothRep.hom j) →
      ∀ g, InHtilde j g → p g ∈ RankOneGraded.IsRankOneGrading.perp (component H ρ hH p)
        (homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π))
        (h𝒜.stab (homAction H ρ _) hρ1 hρm ((inducedLiftHomEquiv H ρ hH π).symm j)) := by
    rintro j hj g ⟨A, hA⟩
    refine RankOneGraded.IsRankOneGrading.mem_perp_iff.mpr ⟨?_, fun b hb u hu v hv => ?_⟩
    · obtain ⟨α, hα, hα0⟩ := (inN_iff ρ hH hp g).mp ⟨A, inN_of_inHtilde ρ j hj A hA⟩
      exact (Submodule.ne_bot_iff _).mpr ⟨α, hα, hα0⟩
    · obtain ⟨k, rfl⟩ := hdeg b (h𝒜.stab_le_support hρ1 hρm _ hb)
      have hk := (hstab j hj k).mpr hb
      rw [← homAction_mul, ← homAction_mul, mul_comm_of_inHtilde ρ hH hp hrank j hj A hA hk hu hv]
  have hperp2 : ∀ j : ρ ⟶ SmoothRep.restrictSubgroup H π, Function.Injective (SmoothRep.hom j) →
      (∀ g, InHtilde j g → InH j g) →
        RankOneGraded.IsRankOneGrading.perp (component H ρ hH p)
          (homAction H ρ ((SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π))
          (h𝒜.stab (homAction H ρ _) hρ1 hρm ((inducedLiftHomEquiv H ρ hH π).symm j)) ⊆
        h𝒜.stab (homAction H ρ _) hρ1 hρm ((inducedLiftHomEquiv H ρ hH π).symm j) := by
    intro j hj hgood a ha
    have ha' := RankOneGraded.IsRankOneGrading.mem_perp_iff.mp ha
    obtain ⟨g, rfl⟩ := hdeg a (h𝒜.mem_support_iff.mpr ((Submodule.ne_bot_iff _).mp ha'.1))
    obtain ⟨α, hα, hα0⟩ := (Submodule.ne_bot_iff _).mp ha'.1
    refine (hstab j hj g).mp (hgood g (inHtilde_of_commute ρ hH hp hrank j hj hα hα0
      fun k hk v hv => ?_))
    exact ha'.2 (p k) ((hstab j hj k).mp hk) α hα v hv
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx0, hx⟩ := h𝒜.exists_perp_subset_stab hρ1 hρm hsurj
    have hj := hinj x hx0
    refine ⟨inducedLiftHomEquiv H ρ hH π x, hj, fun g hg => ?_⟩
    have h1 := hperp1 _ hj g hg
    rw [LinearEquiv.symm_apply_apply] at h1
    refine (hstab _ hj g).mpr ?_
    rw [LinearEquiv.symm_apply_apply]
    exact hx h1
  rintro j ⟨hj, hgood⟩
  have hx0 := hsymm0 j hj
  have hperp := hperp2 j hj hgood
  have : FiniteDimensional ℂ (ρ ⟶ SmoothRep.restrictSubgroup H π) :=
    Module.Finite.equiv (inducedLiftHomEquiv H ρ hH π)
  have hm : Module.finrank ℂ
      (inducedRep H ρ ⟶ (SmoothRep.universeLiftFunctor.{uG, uG, uV} G).obj π) =
        Module.finrank ℂ (ρ ⟶ SmoothRep.restrictSubgroup H π) :=
    (inducedLiftHomEquiv H ρ hH π).finrank_eq
  have hTH : ∀ t ∈ T, InH j t := fun t ht =>
    (hstab j hj t).mpr (h𝒜.radical_le_stab hρ1 hρm hsurj _ ((hrad t).mp ht))
  have hT5 : ∀ t ∈ T, ∀ ψ : ρ ⟶ SmoothRep.restrictSubgroup H π, ∀ w w' : ρ,
      SmoothRep.hom j w' = π.representation t (SmoothRep.hom j w) →
        SmoothRep.hom ψ w' = π.representation t (SmoothRep.hom ψ w) := by
    intro t ht
    obtain ⟨u, hu, hu1⟩ := h𝒜.exists_mem_map_eq_one hρ1 hρm hsurj ((hrad t).mp ht)
    have hval : ∀ ψ : ρ ⟶ SmoothRep.restrictSubgroup H π, ∀ w,
        SmoothRep.hom ψ (endValue H ρ hH u t w) = π.representation t (SmoothRep.hom ψ w) := by
      intro ψ w
      have h1 := hom_comp_symm_apply ρ hH hp hu ψ w
      have h2 : u ≫ (inducedLiftHomEquiv H ρ hH π).symm ψ =
          (inducedLiftHomEquiv H ρ hH π).symm ψ :=
        LinearMap.congr_fun hu1 _
      rw [h2, LinearEquiv.apply_symm_apply] at h1
      rw [h1, Representation.self_inv_apply]
    intro ψ w w' hw
    have hw' : w' = endValue H ρ hH u t w := hj (by rw [hw, hval])
    rw [hw', hval]
  have hTeq : T = (AddSubgroup.toSubgroup h𝒜.radical).comap (degreeHom hp) :=
    Subgroup.ext fun g => (hrad g).trans (mem_comap_degreeHom hp _ g).symm
  refine ⟨Module.finrank ℂ (ρ ⟶ SmoothRep.restrictSubgroup H π),
    (AddSubgroup.toSubgroup (h𝒜.stab (homAction H ρ _) hρ1 hρm
      ((inducedLiftHomEquiv H ρ hH π).symm j))).comap (degreeHom hp),
    (AddSubgroup.toSubgroup h𝒜.support).comap (degreeHom hp),
    (Module.finrank_eq_rank ℂ _).symm,
    fun g => (mem_comap_degreeHom hp _ g).trans (hstab j hj g).symm,
    fun g => (mem_comap_degreeHom hp _ g).trans (hNiff g).symm, ?_, ?_, ?_, ?_,
    fun ψ t ht => hT5 t ht ψ, ?_⟩
  · intro g hg
    exact (mem_comap_degreeHom hp _ g).mpr
      (h𝒜.radical_le_stab hρ1 hρm hsurj _ ((hrad g).mp hg))
  · intro g hg
    exact (mem_comap_degreeHom hp _ g).mpr
      (h𝒜.stab_le_support hρ1 hρm _ ((mem_comap_degreeHom hp _ g).mp hg))
  · rw [relIndex_comap_degreeHom hp _ _ hdeg, h𝒜.relIndex_stab_support hρ1 hρm hsurj hx0 hperp,
      hm]
  · rw [hTeq, relIndex_comap_degreeHom hp _ _ fun a ha => hdeg a (h𝒜.stab_le_support hρ1 hρm _ ha),
      h𝒜.relIndex_radical_stab hρ1 hρm hsurj hx0 hperp, hm]
  · rintro E - - hmin ⟨ψ, hψ0, hψE⟩
    have hψ := injective_of_ne_zero ρ ψ hψ0
    let E' : Submodule ℂ π :=
      { carrier := {v | ∃ w, SmoothRep.hom ψ w = v}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, map_add (SmoothRep.hom ψ) a b⟩
        zero_mem' := ⟨0, map_zero (SmoothRep.hom ψ)⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          exact ⟨c • a, map_smul (SmoothRep.hom ψ) c a⟩ }
    have hE'E : E' ≤ E := by
      rintro _ ⟨w, rfl⟩
      exact hψE w
    have hE'T : TStable E' := by
      rintro t ht _ ⟨w, rfl⟩
      obtain ⟨w', hw'⟩ := (hTH t ht (SmoothRep.hom j w)).mp ⟨w, rfl⟩
      exact ⟨w', hT5 t ht ψ w w' hw'⟩
    have hE'0 : E' ≠ ⊥ := by
      obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible ρ.representation
      intro h
      have hmem : (show π from SmoothRep.hom ψ w) ∈ E' := ⟨w, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hw (hψ (hmem.trans (map_zero (SmoothRep.hom ψ)).symm))
    have hEq : E' = E := (hmin E' hE'E hE'T).resolve_left hE'0
    let f : ρ →ₗ[ℂ] E :=
      { toFun := fun w => ⟨SmoothRep.hom ψ w, hψE w⟩
        map_add' := fun a b => Subtype.ext (map_add (SmoothRep.hom ψ) a b)
        map_smul' := fun c a => Subtype.ext (map_smul (SmoothRep.hom ψ) c a) }
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => hψ (congrArg Subtype.val hab), fun v => ?_⟩
      have hv : (v : π) ∈ E' := by
        rw [hEq]
        exact v.2
      obtain ⟨w, hw⟩ := hv
      exact ⟨w, Subtype.ext hw⟩
    exact ⟨LinearEquiv.ofBijective f hf, fun t ht w w' hw => hT5 t ht ψ w w' hw⟩

end Main

end Langlands.CuspidalSupport.NormalHecke
