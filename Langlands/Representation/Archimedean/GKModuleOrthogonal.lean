import Langlands.Representation.Archimedean.ComplexPermutationEndomorphism
import Langlands.Representation.Archimedean.GKModule
import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal complements and a commutant criterion for algebraic GK modules

This module isolates the algebraic projection argument from
`ComplexTemperedComplement` without importing any Langlands quotient result.
A separating orbit functional and finite vectors give finite-dimensional
saturations; an invariant diagonally anisotropic sesquilinear form then gives
orthogonal complements of invariant subspaces.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexTemperedComplement

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Orthogonal complements for an invariant positive definite form -/

section Abstract

open ComplexPermutation Module

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G W} (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ)

/-- The vectors `x` with `B x y = 0` for every `y ∈ U`. -/
def orth (U : Submodule ℂ W) : Submodule ℂ W where
  carrier := {x | ∀ y ∈ U, B x y = 0}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {x x'} hx hx' y hy => by
    simp only [Set.mem_ofPred_eq] at hx hx'
    simp [hx y hy, hx' y hy]
  smul_mem' := fun c x hx y hy => by
    simp only [Set.mem_ofPred_eq] at hx
    simp [hx y hy]

theorem mem_orth {U : Submodule ℂ W} {x : W} : x ∈ orth B U ↔ ∀ y ∈ U, B x y = 0 :=
  Iff.rfl

/-- Orthogonality to a basis gives orthogonality to the span. -/
theorem mem_orth_of_basis (V : Submodule ℂ W) [FiniteDimensional ℂ V] {x : W}
    (hx : ∀ i, B x (Module.finBasis ℂ V i : W) = 0) : x ∈ orth B V := by
  intro y hy
  set b := Module.finBasis ℂ V
  have hy' : (⟨y, hy⟩ : V) = ∑ i, b.repr ⟨y, hy⟩ i • b i := (b.sum_repr _).symm
  have hyW : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : W) := by
    calc y = ((⟨y, hy⟩ : V) : W) := rfl
      _ = ((∑ i, b.repr ⟨y, hy⟩ i • b i : V) : W) := by rw [← hy']
      _ = ∑ i, b.repr ⟨y, hy⟩ i • (b i : W) := by
        simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [hyW, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, hx i, smul_zero]

/-- For an invariant form, the orthogonal of an invariant subspace is invariant. -/
theorem orth_invariant (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
    (U : Submodule ℂ W) (hU : ∀ (g : G), ∀ x ∈ U, ρ g x ∈ U) :
    ∀ (g : G), ∀ x ∈ orth B U, ρ g x ∈ orth B U := by
  intro g x hx y hy
  have h1 : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← h1, hBinv]
  exact hx _ (hU g⁻¹ y hy)

variable (hBpos : ∀ x : W, B x x = 0 → x = 0)
include hBpos

theorem inf_orth_eq_bot (U : Submodule ℂ W) : U ⊓ orth B U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  exact hBpos x (hx.2 x hx.1)

/-- **Orthogonal projection onto a finite-dimensional subspace.** Every `x` is `p + (x - p)` with
`p ∈ V` and `x - p` orthogonal to `V`: the map `v ↦ (B v (bᵢ))ᵢ` from `V` to `ℂ^{dim V}` is
injective by positivity, hence surjective. -/
theorem exists_orthProj (V : Submodule ℂ W) [FiniteDimensional ℂ V] (x : W) :
    ∃ p ∈ V, x - p ∈ orth B V := by
  set b := Module.finBasis ℂ V
  let Λ : V →ₗ[ℂ] (Fin (finrank ℂ V) → ℂ) := pairingMap B (fun i => (b i : W)) ∘ₗ V.subtype
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    have hv' : (v : W) ∈ orth B V := mem_orth_of_basis B V fun i => congrFun hv i
    exact Subtype.ext (hBpos _ (hv' _ v.2))
  have hsurj : Function.Surjective Λ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨p, hp⟩ := hsurj (pairingMap B (fun i => (b i : W)) x)
  refine ⟨p, p.2, mem_orth_of_basis B V fun i => ?_⟩
  have h := congrFun hp i
  change B (p : W) (b i : W) = B x (b i : W) at h
  rw [map_sub, LinearMap.sub_apply, h, sub_self]

theorem orthProj_unique (V : Submodule ℂ W) {x p p' : W} (hp : p ∈ V) (hp' : p' ∈ V)
    (hxp : x - p ∈ orth B V) (hxp' : x - p' ∈ orth B V) : p = p' := by
  have hd : p' - p ∈ orth B V := by
    have := (orth B V).sub_mem hxp hxp'
    rwa [sub_sub_sub_cancel_left] at this
  have := hBpos _ (hd _ (V.sub_mem hp' hp))
  exact (sub_eq_zero.mp this).symm

/-- The orthogonal projection onto a finite-dimensional subspace. -/
def orthProj (V : Submodule ℂ W) [FiniteDimensional ℂ V] : W →ₗ[ℂ] W where
  toFun x := (exists_orthProj B hBpos V x).choose
  map_add' x y := by
    have hx := (exists_orthProj B hBpos V x).choose_spec
    have hy := (exists_orthProj B hBpos V y).choose_spec
    have hxy := (exists_orthProj B hBpos V (x + y)).choose_spec
    refine orthProj_unique B hBpos V hxy.1 (V.add_mem hx.1 hy.1) hxy.2 ?_
    have := (orth B V).add_mem hx.2 hy.2
    convert this using 1
    abel
  map_smul' c x := by
    have hx := (exists_orthProj B hBpos V x).choose_spec
    have hcx := (exists_orthProj B hBpos V (c • x)).choose_spec
    rw [RingHom.id_apply]
    refine orthProj_unique B hBpos V hcx.1 (V.smul_mem c hx.1) hcx.2 ?_
    have := (orth B V).smul_mem c hx.2
    rwa [smul_sub] at this

theorem orthProj_mem (V : Submodule ℂ W) [FiniteDimensional ℂ V] (x : W) :
    orthProj B hBpos V x ∈ V :=
  (exists_orthProj B hBpos V x).choose_spec.1

theorem sub_orthProj_mem (V : Submodule ℂ W) [FiniteDimensional ℂ V] (x : W) :
    x - orthProj B hBpos V x ∈ orth B V :=
  (exists_orthProj B hBpos V x).choose_spec.2

/-- The orthogonal projection onto an invariant subspace is equivariant. -/
theorem orthProj_equivariant (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
    (V : Submodule ℂ W) [FiniteDimensional ℂ V] (hV : ∀ (g : G), ∀ x ∈ V, ρ g x ∈ V)
    (g : G) (x : W) : orthProj B hBpos V (ρ g x) = ρ g (orthProj B hBpos V x) := by
  refine orthProj_unique B hBpos V (orthProj_mem B hBpos V _) (hV g _ (orthProj_mem B hBpos V x))
    (sub_orthProj_mem B hBpos V _) ?_
  rw [← map_sub]
  exact orth_invariant B hBinv V hV g _ (sub_orthProj_mem B hBpos V x)

omit hBpos

/-! ### The saturation of a vector -/

variable (ρ) in
/-- The saturation of `h`: the sum of the images of all equivariant maps from the orbit span of
`h` into `W`. It contains `h` and is stable under every equivariant endomorphism of `W`. -/
def saturation (h : W) : Submodule ℂ W :=
  ⨆ φ : eqvHom ρ (FiniteVectors.orbitSpan ρ h),
    LinearMap.range (φ : FiniteVectors.orbitSpan ρ h →ₗ[ℂ] W)

theorem self_mem_saturation (h : W) : h ∈ saturation ρ h := by
  have hφ : (FiniteVectors.orbitSpan ρ h).subtype ∈ eqvHom ρ (FiniteVectors.orbitSpan ρ h) :=
    subtype_mem_eqvHom ρ _
  exact Submodule.mem_iSup_of_mem (⟨_, hφ⟩ : eqvHom ρ _)
    ⟨⟨h, FiniteVectors.self_mem_orbitSpan ρ h⟩, rfl⟩

theorem map_mem_saturation (E : W →ₗ[ℂ] W) (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w))
    (h : W) {x : W} (hx : x ∈ saturation ρ h) : E x ∈ saturation ρ h := by
  refine Submodule.iSup_induction _ (motive := fun x => E x ∈ saturation ρ h) hx ?_ ?_ ?_
  · rintro φ _ ⟨y, rfl⟩
    exact Submodule.mem_iSup_of_mem
      (⟨E ∘ₗ (φ : FiniteVectors.orbitSpan ρ h →ₗ[ℂ] W), comp_mem_eqvHom ρ E hE φ.2⟩ :
        eqvHom ρ _) ⟨y, rfl⟩
  · simp
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

variable (ev : W →ₗ[ℂ] ℂ) (hsep : ∀ w : W, (∀ g : G, ev (ρ g w) = 0) → w = 0)
  (hfin : ∀ w : W, FiniteVectors.IsFiniteVector ρ w)

include hsep hfin in
/-- The saturation is finite-dimensional: it is spanned by the images of a basis of the
finite-dimensional space of equivariant maps out of the orbit span. -/
theorem finiteDimensional_saturation (h : W) : FiniteDimensional ℂ (saturation ρ h) := by
  set F := FiniteVectors.orbitSpan ρ h
  have : FiniteDimensional ℂ F := hfin h
  have : FiniteDimensional ℂ (eqvHom ρ F) :=
    finiteDimensional_eqvHom ev hsep F (orbitSpan_invariant h)
  set b := Module.finBasis ℂ (eqvHom ρ F)
  have hle : saturation ρ h ≤ ⨆ i, LinearMap.range ((b i : eqvHom ρ F) : F →ₗ[ℂ] W) := by
    refine iSup_le fun φ => ?_
    rintro _ ⟨y, rfl⟩
    have hφ : (φ : F →ₗ[ℂ] W) = ∑ i, b.repr φ i • ((b i : eqvHom ρ F) : F →ₗ[ℂ] W) := by
      conv_lhs => rw [← b.sum_repr φ]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hφ, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ => by
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ⟨y, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

include hsep hfin hBpos in
/-- **Orthogonal complements of invariant subspaces.** If every vector is a finite vector, `ev`
separates orbits and `B` is invariant and positive definite, then `U + U^⊥ = W` for every
invariant subspace `U`. For `h ∈ W` let `S` be its (finite-dimensional) saturation and `u` the
orthogonal projection of `h` onto `U ∩ S`. For `f ∈ U` let `P` be the orthogonal projection onto
the orbit span `V ⊆ U` of `f`; it is equivariant, so `P(h - u) ∈ U ∩ S`, whence
`B(P(h-u), P(h-u)) = 0`, `P(h - u) = 0` and `B(h - u, f) = 0`. -/
theorem sup_orth_eq_top (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
    (U : Submodule ℂ W) (hU : ∀ (g : G), ∀ x ∈ U, ρ g x ∈ U) : U ⊔ orth B U = ⊤ := by
  rw [eq_top_iff]
  intro h _
  have := finiteDimensional_saturation ev hsep hfin h
  have : FiniteDimensional ℂ ↥(U ⊓ saturation ρ h) :=
    Submodule.finiteDimensional_of_le inf_le_right
  set u := orthProj B hBpos (U ⊓ saturation ρ h) h
  have hu : u ∈ U ⊓ saturation ρ h := orthProj_mem B hBpos _ h
  have hc : h - u ∈ orth B (U ⊓ saturation ρ h) := sub_orthProj_mem B hBpos _ h
  have hcS : h - u ∈ saturation ρ h := Submodule.sub_mem _ (self_mem_saturation h) hu.2
  have hcU : h - u ∈ orth B U := by
    intro f hf
    have : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ f) := hfin f
    have hVinv : ∀ (g : G), ∀ x ∈ FiniteVectors.orbitSpan ρ f,
        ρ g x ∈ FiniteVectors.orbitSpan ρ f := orbitSpan_invariant f
    have hVU : FiniteVectors.orbitSpan ρ f ≤ U :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hU g f hf)
    set P := orthProj B hBpos (FiniteVectors.orbitSpan ρ f)
    have hP : ∀ (g : G) (w : W), P (ρ g w) = ρ g (P w) :=
      orthProj_equivariant B hBpos hBinv _ hVinv
    have h1 : P (h - u) ∈ saturation ρ h := map_mem_saturation P hP h hcS
    have h2 : P (h - u) ∈ FiniteVectors.orbitSpan ρ f := orthProj_mem B hBpos _ _
    have h3 : B (h - u) (P (h - u)) = 0 := hc _ ⟨hVU h2, h1⟩
    have h4 : B (h - u - P (h - u)) (P (h - u)) = 0 := sub_orthProj_mem B hBpos _ _ _ h2
    rw [map_sub, LinearMap.sub_apply, h3, zero_sub, neg_eq_zero] at h4
    have h5 : P (h - u) = 0 := hBpos _ h4
    have h6 := sub_orthProj_mem B hBpos (FiniteVectors.orbitSpan ρ f) (h - u) f
      (FiniteVectors.self_mem_orbitSpan ρ f)
    change B (h - u - P (h - u)) f = 0 at h6
    rwa [h5, sub_zero] at h6
  have heq : h = u + (h - u) := by abel
  rw [heq]
  exact Submodule.add_mem_sup hu.1 hcU

include hsep hfin hBpos in
theorem isCompl_orth (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
    (U : Submodule ℂ W) (hU : ∀ (g : G), ∀ x ∈ U, ρ g x ∈ U) : IsCompl U (orth B U) :=
  IsCompl.of_eq (inf_orth_eq_bot B hBpos U) (sup_orth_eq_top B hBpos ev hsep hfin hBinv U hU)

end Abstract

/-- The projection along a complement commutes with every endomorphism preserving both
summands. -/
theorem projection_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {W W' : Submodule ℂ V}
    (hc : IsCompl W W') (T : V →ₗ[ℂ] V) (hT : ∀ w ∈ W, T w ∈ W) (hT' : ∀ w ∈ W', T w ∈ W')
    (f : V) : W.projection W' hc (T f) = T (W.projection W' hc f) := by
  have hf := Submodule.projection_add_projection_eq_self hc f
  calc W.projection W' hc (T f)
      = W.projection W' hc (T (W.projection W' hc f + W'.projection W hc.symm f)) := by
        rw [hf]
    _ = T (W.projection W' hc f) := by
        rw [map_add, map_add,
          Submodule.projection_apply_of_mem_left hc (hT _ (Submodule.projection_apply_mem hc f)),
          Submodule.projection_apply_of_mem_right hc
            (hT' _ (Submodule.projection_apply_mem hc.symm f)), add_zero]


end Langlands.Archimedean.ComplexTemperedComplement

namespace Langlands.Archimedean.GKModuleOrthogonal

attribute [local instance 100] LieRing.ofAssociativeRing

open ComplexTemperedComplement

section Irreducibility

variable {K : Type*} [Group K] {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Every simultaneous group/Lie intertwiner is multiplication by a complex scalar. -/
def EndomorphismsAreScalar (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∀ E : V →ₗ[ℂ] V,
    (∀ (k : K) (v : V), E (ρ k v) = ρ k (E v)) →
    (∀ (X : L) (v : V), E (π X v) = π X (E v)) →
    ∃ c : ℂ, ∀ v : V, E v = c • v

/-- Every simultaneous group/Lie invariant subspace admits an invariant complement. -/
def HasInvariantComplements (ρ : Representation ℂ K V)
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∀ U : Submodule ℂ V,
    (∀ (k : K), ∀ v ∈ U, ρ k v ∈ U) →
    (∀ (X : L), ∀ v ∈ U, π X v ∈ U) →
    ∃ U' : Submodule ℂ V,
      (∀ (k : K), ∀ v ∈ U', ρ k v ∈ U') ∧
      (∀ (X : L), ∀ v ∈ U', π X v ∈ U') ∧ IsCompl U U'

/-- A nonzero module with invariant complements and scalar commutant is irreducible.
The projection onto any invariant subspace is scalar and is therefore zero or invertible. -/
theorem isIrreducible_of_complements_of_endScalar
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hne : Nontrivial V) (hc : HasInvariantComplements ρ π)
    (hE : EndomorphismsAreScalar ρ π) : IsIrreducibleGKModule ρ π := by
  refine ⟨hne, fun U hUK hUL => ?_⟩
  obtain ⟨U', hU'K, hU'L, hcompl⟩ := hc U hUK hUL
  obtain ⟨c, hcP⟩ := hE (U.projection U' hcompl)
    (fun k v => projection_comm hcompl _ (hUK k) (hU'K k) v)
    (fun X v => projection_comm hcompl _ (hUL X) (hU'L X) v)
  by_cases h0 : c = 0
  · left
    have htop : U' = ⊤ := eq_top_iff.mpr fun v _ => by
      rw [← Submodule.projection_apply_eq_zero_iff hcompl, hcP, h0, zero_smul]
    have := hcompl.inf_eq_bot
    rwa [htop, inf_top_eq] at this
  · right
    refine eq_top_iff.mpr fun v _ => ?_
    have hv : v = c⁻¹ • U.projection U' hcompl v := by
      rw [hcP, smul_smul, inv_mul_cancel₀ h0, one_smul]
    rw [hv]
    exact U.smul_mem _ (Submodule.projection_apply_mem hcompl v)

/-- Orthogonals are Lie invariant if each Lie operator has an adjoint in the
Lie action up to a scalar. No positivity or symmetry is needed for this step. -/
theorem orth_lie_invariant {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadj : ∀ X : L, ∃ (Y : L) (c : ℂ), ∀ v w : V,
      B (π X v) w = B v (π Y w) + c * B v w)
    (U : Submodule ℂ V) (hU : ∀ X : L, ∀ v ∈ U, π X v ∈ U) :
    ∀ X : L, ∀ v ∈ orth B U, π X v ∈ orth B U := by
  intro X v hv w hw
  obtain ⟨Y, c, h⟩ := hadj X
  rw [h, hv _ (hU Y w hw), hv w hw, mul_zero, add_zero]

/-- An invariant form with finite vectors, a separating functional and adjoints
supplies invariant complements for the simultaneous group and Lie actions. -/
theorem hasInvariantComplements_of_form
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ v : V, B v v = 0 → v = 0)
    (ev : V →ₗ[ℂ] ℂ) (hsep : ∀ v : V, (∀ k : K, ev (ρ k v) = 0) → v = 0)
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hBK : ∀ (k : K) (v w : V), B (ρ k v) (ρ k w) = B v w)
    (hadj : ∀ X : L, ∃ (Y : L) (c : ℂ), ∀ v w : V,
      B (π X v) w = B v (π Y w) + c * B v w) :
    HasInvariantComplements ρ π := by
  intro U hUK hUL
  exact ⟨orth B U, orth_invariant B hBK U hUK,
    orth_lie_invariant B hadj U hUL,
    isCompl_orth B hB ev hsep hfin hBK U hUK⟩

end Irreducibility

end Langlands.Archimedean.GKModuleOrthogonal
