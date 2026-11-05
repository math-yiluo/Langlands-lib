# Linear algebra of the rational-character tensor parameter

Module: `Langlands.Representation.Plancherel.RationalCharacterTensorParameterReduction`,
namespace `Langlands.Plancherel`.

## Setting

Fix a nonarchimedean local field `F` (arbitrary universe `u`, with the
instances `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField`) and a group scheme `G` over `Spec F`. The
module uses these existing objects:

- `X := GroupScheme.rationalCharacters G`, the rational characters `X^*(G)`;
- `Λ := rationalDiscreteValuationImage G`, the actual valuation image (the
  range of `rationalCharacterValuation G : G(F) →* Multiplicative (X →+ ℤ)`);
- `ι := rationalImageIntegerDual G : Additive Λ →ₗ[ℤ] (X →ₗ[ℤ] ℤ)`, which sends
  `a` to `χ ↦ a(χ)` and is injective (`rationalImageIntegerDual_injective`);
- `T := rationalCharacterTensorParameter G :
  ℂ ⊗[ℤ] X →ₗ[ℂ] (Additive Λ →+ ℂ)`, given on pure tensors by
  `T (s ⊗ χ) a = s * a(χ)`.

The target statement `RationalCharacterTensorParameterStatement` asserts that
`T` is bijective for every connected reductive `G`. This module proves
surjectivity outright. It proves injectivity, and so bijectivity, from one
extra input, *valuation detection*. Detection is where the structural theory
of reductive groups comes in, and this module does not prove it.

## Definition

```lean
def RationalValuationDetects : Prop :=
  ∀ χ : GroupScheme.rationalCharacters G, χ ≠ 0 →
    ∃ g : GroupScheme.rationalPoints G, (rationalCharacterValuation G g).toAdd χ ≠ 0
```

Every nonzero rational character `χ` has a rational point `g` at which the
integer valuation `v_F(χ(g))` is nonzero. Equivalently, the map
`X → Hom(Λ, ℤ)`, `χ ↦ (a ↦ a(χ))`, has zero kernel. The module proves only
the direction it uses, that detection makes this map injective
(`rationalImageIntegerDual_flip_injective`).

**Provenance (derived).** The source does not name this predicate.
Renard 2026, V.3.19 (printed page 115 / PDF page 121), uses that the
cocharacter lattice of the split component `A`, the image `Λ(M)` and the
cocharacter lattice of `M` are nested lattices of the same rank. V.3.20
(printed pages 115–116 / PDF pages 121–122) then identifies
`𝔞_ℂ^* = Hom_ℤ(Λ(M), ℂ)` with `X^*(M) ⊗_ℤ ℂ`. Detection is the part of the
same-rank fact that this complex identification actually needs. Since `ι`
is injective, detection says that the pairing between `X` and `Λ` is
nondegenerate on the character side as well. In the source this
nondegeneracy comes from the split component: a nonzero character
restricts nontrivially to `A`, and evaluating it on a uniformizer
cocharacter gives a nonzero valuation.

## Results

1. `rationalCharacterTensorParameter_comm_rTensor_evalEquiv` (needs
   `Module.Free ℤ X` and `Module.Finite ℤ X`). For
   `t : Dual (Dual X) ⊗[ℤ] ℂ`, write `t♭` for the image of `t` in `ℂ ⊗[ℤ] X`
   under `(evalEquiv ℤ X).symm` followed by tensor commutation. Then
   `T t♭ a = dualTensorHom ℤ (Dual X) ℂ t (ι a)`. The proof is by induction on
   `t`. For a pure tensor, write `φ = eval χ`; both sides reduce to
   `c * a(χ)` and `a(χ) • c`.

2. `rationalCharacterTensorParameter_surjective (hG : IsConnectedReductive G)`,
   which is **unconditional**. The published `GroupScheme.rationalCharacterLattice`
   makes `X` free and finite. Let `f : Additive Λ →+ ℂ`.
   - `ℂ` is divisible (`divisibleByIntOfCharZero`), hence a Baer ℤ-module
     (`Module.Baer.of_divisible`). Since `ι` is injective, `f` extends to some
     `f' : Dual X →+ ℂ` with `f' ∘ ι = f`
     (`Module.Baer.extension_property_addMonoidHom`).
   - `Dual X` is finite projective, so `dualTensorHomEquiv ℤ (Dual X) ℂ` is a
     bijection, and `f'` is `dualTensorHom t` for some
     `t : Dual (Dual X) ⊗ ℂ`.
   - By result 1, `T t♭ = f' ∘ ι = f`.

3. `rationalCharacterTensorParameter_apply_eq_dualTensorHom`. For every
   `t : ℂ ⊗[ℤ] X`,
   `T t a = dualTensorHom ℤ (Additive Λ) ℂ (comm ((ι.flip).lTensor ℂ t)) a`,
   where `ι.flip : X →ₗ[ℤ] Dual (Additive Λ)` sends `χ` to `a ↦ a(χ)`. The
   proof is by induction on `t`.

4. `rationalImageIntegerDual_flip_injective (h : RationalValuationDetects G)`.
   If `ι.flip χ = 0`, evaluate at the image point
   `⟨rationalCharacterValuation G g, g, rfl⟩`. This shows that every
   valuation of `χ` vanishes, so `χ = 0` by detection.

5. `rationalCharacterTensorParameter_injective_of_detects (hG) (h)`.
   `ℂ` is torsion-free over the Dedekind domain `ℤ`, hence flat, and Mathlib
   finds this instance. So `(ι.flip).lTensor ℂ` is injective
   (`Module.Flat.lTensor_preserves_injective_linearMap`). Tensor commutation
   is a bijection. `rationalReductiveImage_free_finite` makes `Λ` free and
   finite, so `dualTensorHomEquiv ℤ (Additive Λ) ℂ` is a bijection too. By
   result 3, `T t = T t'` makes these composites agree, so `t = t'`.

6. `rationalCharacterTensorParameter_bijective_of_detects (hG) (h)` combines
   results 5 and 2.

7. `rationalCharacterTensorParameterStatement_of_detects`. If valuation
   detection holds for every connected reductive group over every
   nonarchimedean local field in universe `u`, then
   `RationalCharacterTensorParameterStatement.{u}` holds.

## Scope

This module does not prove the target statement. It reduces the target to
`RationalValuationDetects`, which is structural input: it comes from central
split torus detection (task 4f432abe), central torus detection or full
character restriction, combined with the uniformizer cocharacter evaluation
formula. No rank, splitting or characteristic hypothesis appears anywhere.
Surjectivity uses only that `G` is connected reductive.

All declarations use only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.
