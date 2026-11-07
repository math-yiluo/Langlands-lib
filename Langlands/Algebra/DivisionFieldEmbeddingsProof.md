# Proof: field embeddings in a central division algebra are conjugate

This module proves
`Langlands.CentralDivision.FieldEmbeddingsConjugateStatement.{uK, uL, uD}`
from `Langlands.Algebra.DivisionFieldEmbeddingsStatement`. The target theorem
is `Langlands.CentralDivision.fieldEmbeddingsConjugate`. The module adds some
auxiliary declarations, listed below. None of them is a new mathematical
concept; they only set up the module structures the proof uses.

## Setting

Throughout, `K : Type uK` is a field and `D : Type uD` is a division ring with
`[Algebra K D]`. `L : Type uL` is a field with `[Algebra K L]`. As in the
statement, the three universes are independent. No characteristic or
separability hypothesis appears anywhere in the module. The hypotheses
`[FiniteDimensional K D] [Algebra.IsCentral K D] [FiniteDimensional K L]` are
added only for the last two lemmas and the target theorem.

## Auxiliary declarations

- `rightMulHom K D L h : L →ₐ[K] Module.End K D`, for `h : L →ₐ[K] D`, sends
  `a` to right multiplication `x ↦ x * h a`. In general, right multiplication
  reverses products. Here it is multiplicative because `L` is commutative,
  and the proof of `map_mul'` uses `mul_comm a b`.
- `twistRep K D L h : L ⊗[K] D →ₐ[K] Module.End K D` is
  `Algebra.TensorProduct.lift` of `rightMulHom K D L h` and the
  left-multiplication map `Algebra.lmul K D`. The images of the two maps
  commute (`LinearMap.commute_mulLeft_right`). The simp lemma
  `twistRep_tmul_apply` records
  `twistRep K D L h (a ⊗ₜ d) x = d * x * h a`.
- `Twist K D L h` is a type synonym for `D`. It carries the additive group,
  `K`-module, nontriviality and finite-dimensionality of `D`. Its
  `L ⊗[K] D`-module structure is `Module.compHom` along `twistRep K D L h`, so
  `b • x = twistRep K D L h b x` (`Twist.smul_def`, which holds by `rfl`).
  An `IsScalarTower K (L ⊗[K] D) (Twist K D L h)` instance follows because
  `twistRep` is `K`-linear. This synonym lets the two maps `f` and `g` give
  two different module structures on the same set `D`.
- `exists_twist_linearMap_ne_zero K D L f g` says: under the three
  finiteness and centrality hypotheses, there is a nonzero
  `L ⊗[K] D`-linear map `φ : Twist K D L f →ₗ[L ⊗[K] D] Twist K D L g`.
- `exists_unit_conj K D L f g` is the conclusion for fixed `K`, `D`, `L`,
  `f` and `g`: there is `u : Dˣ` with
  `f a = (u : D) * g a * ((u⁻¹ : Dˣ) : D)` for all `a : L`.
- `fieldEmbeddingsConjugate : FieldEmbeddingsConjugateStatement.{uK, uL, uD}`
  introduces the statement's binders and applies `exists_unit_conj`.

## Proof

Write `B := L ⊗[K] D`.

1. **`B` is simple and Artinian.** Simplicity is the published theorem
   `Langlands.CentralSimple.isSimpleRing_baseChange K D L` from
   `Langlands.Algebra.CentralSimpleScalarExtension`. Its hypotheses are
   `[FiniteDimensional K D] [Algebra.IsCentral K D] [IsSimpleRing D]`, and a
   division ring is a simple ring. `B` is finite-dimensional over `K`, so it is
   Artinian by `IsArtinianRing.of_finite K B`.
2. **Both twisted modules are finite over `B`.** Each `Twist K D L h` is
   finite-dimensional over `K`. The scalar tower `K → B → Twist K D L h`
   then gives `Module.Finite B (Twist K D L h)`, by
   `Module.Finite.of_restrictScalars_finite`.
3. **A nonzero intertwiner.** Let `P := Twist K D L f × Twist K D L g`. Every
   module over a simple Artinian ring is isotypic, so `P` is isotypic
   (`IsSimpleRing.isIsotypic`). `P` is finite and nontrivial, so
   `IsIsotypic.linearEquiv_fun` yields a simple submodule `S` of `P`. `P` is
   then isotypic of type `S`. Pulling this back along the injective maps
   `LinearMap.inl` and `LinearMap.inr`
   (`IsIsotypicOfType.of_injective`) shows that both `Twist K D L f` and
   `Twist K D L g` are isotypic of type `S`. Since both are finite,
   `IsIsotypicOfType.linearEquiv_fun` gives `B`-linear equivalences
   `ef : Twist K D L f ≃ₗ[B] (Fin p → S)` and
   `eg : Twist K D L g ≃ₗ[B] (Fin q → S)`. Both `p` and `q` are positive,
   since a module equivalent to `Fin 0 → S` is a subsingleton and `D` is
   nontrivial. Define
   `φ := eg.symm ∘ₗ single 0 ∘ₗ proj 0 ∘ₗ ef`, which copies the first
   coordinate into the first coordinate. To see `φ ≠ 0`, choose `s ≠ 0` in the
   simple, hence nontrivial, module `S`. Then `φ (ef.symm (fun _ => s))` is
   `eg.symm (single 0 s)`, which is nonzero because `eg.symm` is injective.
4. **The conjugating element.** Put `u := φ 1 ∈ D`. For `d : D`,
   `(1 ⊗ₜ d) • 1 = d * 1 * f 1 = d` in `Twist K D L f`. Linearity of `φ` gives
   `φ d = (1 ⊗ₜ d) • u = d * u * g 1 = d * u`. For `a : L`,
   `(a ⊗ₜ 1) • 1 = f a` in `Twist K D L f`, so
   `φ (f a) = (a ⊗ₜ 1) • u = u * g a`. Taking `d = f a` in the first identity
   gives `f a * u = u * g a`.
5. **`u` is a unit.** If `u = 0`, then `φ d = d * u = 0` for every `d`, so
   `φ = 0`, which contradicts step 3. So `u ≠ 0`. Since `D` is a division ring,
   `Units.mk0 u hu` is a unit with inverse `u⁻¹`. Multiplying
   `f a * u = u * g a` on the right by `u⁻¹` gives
   `f a = u * g a * u⁻¹`, which is the required identity. The Lean proof
   rewrites with `Units.val_inv_eq_inv_val`, `Units.val_mk0`, `mul_assoc` and
   `mul_inv_cancel₀`.

The proof never shows that the two twisted modules are isomorphic, and it uses
no dimension count. A single nonzero intertwiner is enough: its value at `1`
is a nonzero element of the division ring `D`, hence invertible. The argument
uses only that `B` is simple and Artinian, that the two modules are finite
over `B`, and that they are nontrivial.

## Relation to the literature

The statement is from J. S. Milne, *Class Field Theory*, version 4.03 (2020),
Chapter IV, section 2, Theorem 2.10 (Skolem, Noether), printed page 129
(PDF page 138), registered as `milne-2020-class-field-theory`. See the
statement's Markdown for the specialization. The implemented route differs
from Milne's. Milne first proves the full-matrix case: the two maps make
`kⁿ` into two modules of the same dimension, which are isomorphic by his
1.21. For a general central simple target `B`, he applies the matrix case to
`f ⊗ 1` and `g ⊗ 1` with values in the matrix algebra `B ⊗ Bᵒᵖ`. The
centralizer of `k ⊗ Bᵒᵖ` (his 2.3) then puts the conjugator in `B ⊗ 1`.
This proof instead works directly with the two module structures on `D` over
`L ⊗[K] D`. It uses the division-ring hypothesis to avoid both the module
isomorphism with its dimension count and the passage through `D ⊗ Dᵒᵖ`.
Beyond the statement's citation, no literature is used.

## Scope

The module proves exactly the published proposition, with all three universes
arbitrary and no additional premise. In particular, no conjugating unit,
module isomorphism, splitting chart or Skolem–Noether conclusion is assumed.
It does not prove the general Skolem–Noether theorem for simple source
algebras or central simple targets with nontrivial matrix factors.

## Checks

The development `lean_check` reports 0 errors and 0 warnings. The target
`fieldEmbeddingsConjugate` is a theorem with level parameters `uK`, `uL`, `uD`,
the same order as the statement's. It uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The statement pair and the modules it
imports are unchanged.

## Attribution

Worker 1791 wrote the Lean proof and this explanation.
