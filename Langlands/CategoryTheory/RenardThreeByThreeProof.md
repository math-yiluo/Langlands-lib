# Proof of Renard's three-by-three bottom-row construction

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement`
(module `Langlands.CategoryTheory.RenardThreeByThreeStatement`, by Worker 691
and Worker 6), which is unchanged and imported by its Lean name.

## Theorem

Module `Langlands.CategoryTheory.RenardThreeByThreeProof` contains

```lean
theorem Langlands.CategoryTheory.renardThreeByThreeBottomRowStatement_proof
    (C : Type u) [Category.{v} C] [Abelian C] :
    RenardThreeByThreeBottomRowStatement C
```

It holds for every abelian category `C`, with independent object universe `u`
and morphism universe `v`, and has no hypotheses beyond the statement's own.
Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

The statement quantifies over two short complexes `S₁ S₂ : ShortComplex C`,
a morphism `τ : S₁ ⟶ S₂`, three arbitrary objects `Z₁ Z₂ Z₃`, three maps
`pᵢ : S₂.Xᵢ ⟶ Zᵢ` and witnesses `wᵢ : τ.τᵢ ≫ pᵢ = 0`. It assumes that both
rows `S₁`, `S₂` and the three columns `ShortComplex.mk τ.τᵢ pᵢ wᵢ` are short
exact. It concludes that there are `a : Z₁ ⟶ Z₂`, `b : Z₂ ⟶ Z₃` and
`w : a ≫ b = 0` with `p₁ ≫ a = S₂.f ≫ p₂`, `p₂ ≫ b = S₂.g ≫ p₃` and
`(ShortComplex.mk a b w).ShortExact`. The proof constructs `a` and `b` on the
given objects `Zᵢ` and maps `pᵢ`. It does not replace them by chosen
cokernels or take a bottom row as input.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix A.VI.2(8) ("Lemme des 3 × 3"), printed
page 262 / one-based PDF page 268. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 267–268 were read, and PDF268 was rendered and inspected. The
diagram has exact rows `0 → A → A′ → A″ → 0` and `0 → B → B′ → B″ → 0`,
vertical maps `A → B → C`, `A′ → B′ → C′` and `A″ → B″ → C″` with exact
columns, and no arrows between `C`, `C′` and `C″`. The text says that one can
complete the diagram by a monomorphism `C → C′` and an epimorphism `C′ → C″`
so that the enlarged diagram still commutes and `0 → C → C′ → C″ → 0` is
exact. The source gives no proof. The appendix part (PDF18–19) of the older
errata `renard-2010-corrections-complements` (SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) was
read too. It contains no correction to this lemma; the 2026 edition governs.

The Lean proof is not a transcription of a printed argument. It reuses
Mathlib's snake lemma and universal properties, as described below.

## Implemented proof

The proof introduces the data and the five hypotheses `hS₁ hS₂ hc₁ hc₂ hc₃`
(rows, then columns).

1. **The arrow `a`.** Since `C` is abelian, `ShortExact.gIsCokernel` applied
   to `hc₁` shows that `p₁` is a cokernel of `τ.τ₁`. The map `S₂.f ≫ p₂`
   vanishes on `τ.τ₁`: by the upper-left square `τ.comm₁₂`,
   `τ.τ₁ ≫ S₂.f ≫ p₂ = S₁.f ≫ τ.τ₂ ≫ p₂`, which is `0` by `w₂`.
   `CokernelCofork.IsColimit.desc'` then gives `a : Z₁ ⟶ Z₂` with
   `p₁ ≫ a = S₂.f ≫ p₂`.
2. **The arrow `b`.** In the same way, `hc₂.gIsCokernel`, the upper-right
   square `τ.comm₂₃` and `w₃` give `b : Z₂ ⟶ Z₃` with
   `p₂ ≫ b = S₂.g ≫ p₃`.
3. **Zero composite.** `p₁` is an epimorphism (`hc₁.epi_g`), and
   `p₁ ≫ a ≫ b = S₂.f ≫ S₂.g ≫ p₃ = 0`. Hence `w : a ≫ b = 0`.
4. **The morphism to the bottom row.** The maps `p₁, p₂, p₃` form a morphism
   of short complexes `v₂₃ : S₂ ⟶ ShortComplex.mk a b w`. Its two squares are
   the equations of steps 1 and 2. The witnesses `w₁, w₂, w₃` show
   `τ ≫ v₂₃ = 0`, componentwise.
5. **A snake input.** The proof builds a Mathlib
   `ShortComplex.SnakeInput C` with rows `L₀ = kernel τ` (the kernel in
   `ShortComplex C`, with `v₀₁ = kernel.ι τ` and `h₀ = kernelIsKernel τ`),
   `L₁ = S₁`, `L₂ = S₂` and `L₃ = ShortComplex.mk a b w`, and with
   `v₁₂ = τ` and `v₂₃` from step 4. Its field `h₃` says that `v₂₃` is a
   cokernel of `τ` in `ShortComplex C`. By `ShortComplex.isColimitOfIsColimitπ`,
   it suffices that each component is a cokernel. Through
   `CokernelCofork.isColimitMapCoconeEquiv`, these are exactly
   `hc₁.gIsCokernel`, `hc₂.gIsCokernel` and `hc₃.gIsCokernel`. The fields on
   the rows come from `hS₁.exact`, `hS₁.epi_g`, `hS₂.exact` and
   `hS₂.mono_f`.
6. **Short exactness of the bottom row.**
   - Exactness at `Z₂` is `SnakeInput.L₃_exact`.
   - `b` is an epimorphism by `SnakeInput.epi_L₃_g`, which uses that `S₂.g`
     is an epimorphism (`hS₂.epi_g`).
   - For the monomorphism `a`, `SnakeInput.L₂'_exact` gives exactness of `L₀.X₃ ⟶ Z₁ ⟶ Z₂`, where the first map is the
     connecting morphism `δ` and the second is `a`. The object `L₀.X₃` is
     zero. Indeed, `v₀₁.τ₃ : L₀.X₃ ⟶ S₁.X₃` is a monomorphism
     (`SnakeInput.mono_v₀₁_τ₃`), and `v₀₁.τ₃ ≫ τ.τ₃ = 0`
     (`SnakeInput.w₀₂_τ₃`). Since `τ.τ₃` is a monomorphism (`hc₃.mono_f`),
     `v₀₁.τ₃ = 0`, so `IsZero.of_mono_eq_zero` applies. Thus `δ = 0`, and
     `ShortComplex.Exact.mono_g` shows that `a` is a monomorphism.

   These three facts form `(ShortComplex.mk a b w).ShortExact`. Together
   with steps 1–3 they give the existential conclusion.

The route does not use that `S₁.f`, `τ.τ₁` and `τ.τ₂` are monomorphisms.
These hypotheses remain part of the unchanged target.

## Reused results and the source assertion

The source assertion A.VI.2(8) is the published statement; the theorem above
is its only proof here. The argument reuses these Mathlib results (commit
`5ed2965256430c3649e86755f9576b54eca72435`) and no Library result other than
the statement:

- `CategoryTheory.ShortComplex.ShortExact.gIsCokernel`, `.epi_g`, `.mono_f`,
  `.exact`: the second map of a short exact complex is a cokernel of the
  first;
- `CategoryTheory.Limits.CokernelCofork.IsColimit.desc'`: the universal
  property of a cokernel;
- `CategoryTheory.ShortComplex.isColimitOfIsColimitπ` and
  `CategoryTheory.Limits.CokernelCofork.isColimitMapCoconeEquiv`: cokernels in
  `ShortComplex C` are computed componentwise;
- `CategoryTheory.Limits.kernel`, `kernel.ι`, `kernel.condition`,
  `kernelIsKernel` in `ShortComplex C`;
- the snake lemma API `CategoryTheory.ShortComplex.SnakeInput` and its
  `L₃_exact`, `epi_L₃_g`, `L₂'_exact`, `mono_v₀₁_τ₃` and `w₀₂_τ₃`;
- `CategoryTheory.Limits.IsZero.of_mono_eq_zero`, `IsZero.eq_of_src` and
  `CategoryTheory.ShortComplex.Exact.mono_g`.

## Scope

This proves only A.VI.2(8). It adds no axiom and no hypothesis. It does not
assume modules, a faithful embedding, smallness, finite length, splitting, a
given factorization or a given connecting morphism. Uniqueness of `a` and `b`
is not part of the target and is not stated here. The seven-axiom bridge
`Langlands.CategoryTheory.RenardAbelian`, the image/coimage results and the
other A.VI.2 assertions keep their existing modules and owners. The file
imports only the statement module and
`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`, and adds no other file.
