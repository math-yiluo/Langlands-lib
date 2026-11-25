/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import WeilConjectures.FieldTheory.IntersectionSubfieldsDifferentialsKernel
import WeilConjectures.FieldTheory.IntersectionSubfieldsDifferentialsPowers

/-! # Intersection of subfields and differentials

Source: Stacks Project, More on Algebra, Tag 07P4 (`lemma-intersection-subfields`),
`literature/stacks-project/more-algebra.tex`.
(blueprint: lem-weil-pbc-intersection-subfields-differentials)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace FieldTheory

/-- The prime-field algebra structure used in Stacks Project, More on Algebra, Tag 07P4.
This registers Mathlib's existing `ZMod.algebra` locally.
(blueprint: lem-weil-pbc-intersection-subfields-differentials) -/
local instance zmodAlgebra (p : ℕ) (K : Type u) [Field K] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra (R := K) p

/-- A directed intersection of subfields between `K^p` and `K` detects differentials and
p-th powers in finite extensions. Source: Stacks Project, More on Algebra, Tag 07P4
(`lemma-intersection-subfields`). The subfields of `K` are written as intermediate fields
over the prime field `ZMod p` (every subfield contains it), and the map
`Ω[K⁄ZMod p] → Ω[K⁄Kα]` with `da ↦ da` is Mathlib's `KaehlerDifferential.map`.
(blueprint: lem-weil-pbc-intersection-subfields-differentials)

Proof (five steps):

1. Frobenius is an injective ring homomorphism, so `K^p` and `L^p` are subfields, and the
prime field lies in `K^p`. Choose a p-basis `x_i` of `K` over the prime field using
`lem-weil-pbc-p-basis-exists`. Its p-monomials form a basis over `K^p`, and `dx_i` form a
basis of the absolute differentials by `lem-weil-pbc-p-basis-differentials-basis`.

2. If a nonzero differential dies in every relative module, express it with finite nonempty
support in the `dx_i`. By `lem-weil-pbc-p-independent-differentials-independent`, its
support's p-monomials have a nontrivial relation over each `Kα`. The space of relations
therefore meets every `Kα^N` nontrivially. The index family is nonempty: otherwise the
intersection condition makes `K` perfect, contradicting the nonempty p-basis support.
Apply `theorem-finite-etale-covers-proper-henselian--2` to obtain a nontrivial relation over
`K^p`, contradicting the p-basis monomials' independence. This proves the first clause.

3. For the second clause, containment of `L^p` in the intersection is immediate. Prove the
reverse containment by strong induction on `[L:K]`, simultaneously for every base field
and family. Degree one is the intersection hypothesis. For a proper intermediate field
`M`, use `lem-weil-pbc-field-degree-multiplicativity` and induction first for `M/K`, then
for `L/M` with the family `M^p Kα`; this family satisfies the same three conditions, and
`L^p (M^p Kα) = L^p Kα`. Thus reduce to an extension with no proper intermediate field,
which is simple, say `L = K(θ)`; split according to whether `θ^p` belongs to `K`.

4. If `φ = θ^p` does not belong to `K`, then `K(φ) = L`. By
`lem-weil-pbc-simple-algebraic-extension-power-basis`, the powers of `θ` and of `φ` up to
`d-1` are `K`-bases, where `d = [L:K]`. Frobenius identifies `L^p` with the `K^p`-span of
those powers of `φ`. Their `Kα`-span is a finite-dimensional subring and hence a field:
multiplication by a nonzero element is an injective, hence surjective, linear endomorphism.
It is exactly `L^p Kα`. Uniqueness of coefficients in the `K`-basis and the intersection
hypothesis then identify the intersection of these spans with `L^p`.

5. If `t = θ^p` belongs to `K`, then `t` is not in `K^p`, by injectivity of Frobenius.
The same power-basis lemma gives `L^p = K^p[t]`, spanned by `1,t,...,t^(p-1)`.
The `Kα`-span of these powers is again a finite-dimensional subring, hence the field
`L^p Kα`; this span need not be direct. Choose `α₀` with `t` outside `Kα₀`. The minimal
polynomial of `t` over `Kα₀` divides `(X-t)^p`; if its degree `e` were less than `p`,
its coefficient `-e*t` would force `t` into `Kα₀`. Thus its degree is `p` and those powers
are independent over `Kα₀`. Write an element of the intersection in that basis. For any
`α`, directedness supplies `γ` contained in both `Kα` and `Kα₀`; uniqueness of coefficients
forces the coefficients into `Kα`. They lie in every `Kα`, hence in `K^p`, proving the claim.
This uses the corrected non-direct-span argument for the intersection of subfields, rather
than the source's direct-sum assertion when `t` belongs to some `Kα`. -/
theorem intersection_subfields_differentials
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    {ι : Type v} (Kα : ι → IntermediateField (ZMod p) K)
    (h₁ : ∀ α : ι, Set.range (fun x : K => x ^ p) ⊆ (Kα α : Set K))
    (h₂ : Set.range (fun x : K => x ^ p) = ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K))
    (h₃ : ∀ α β : ι, ∃ γ : ι, Kα γ ≤ Kα α ⊓ Kα β) :
    (∀ ω : Ω[K⁄ZMod p],
      (∀ α : ι, KaehlerDifferential.map (ZMod p) (Kα α) K K ω = 0) → ω = 0) ∧
    (∀ (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L],
      Set.range (fun x : L => x ^ p) =
        ⋂ α : ι, ((Subfield.closure (Set.range (fun x : L => x ^ p) ∪
          (algebraMap K L '' (Kα α : Set K))) : Set L))) := by
  exact ⟨intersection_subfields_differentials_kernel p K Kα h₁ h₂ h₃,
    intersection_subfields_differentials_powers p K Kα h₁ h₂ h₃⟩

end FieldTheory
