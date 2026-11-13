# Descending a smooth factorization from a localization

`Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentStatement`
(universe `u`). Let `R`, `A`, `Λ` be commutative rings in `Type u`, with `A` and `Λ`
`R`-algebras and `A` finitely presented over `R`, and let `f : A →ₐ[R] Λ`. Let
`S : Submonoid R`, let `R'` be a localization of `R` at `S` (`IsLocalization S R'`) and
`Λ'` a localization of `Λ` at the image of `S`
(`IsLocalization (Algebra.algebraMapSubmonoid Λ S) Λ'`), where `Λ'` is an `R'`-, `Λ`- and
`R`-algebra with `R → R' → Λ'` and `R → Λ → Λ'` scalar towers. Let `B' : Type u` be a
smooth `R'`-algebra (also an `R`-algebra through `R → R'`), and let `u : A →ₐ[R] B'` and
`v : B' →ₐ[R'] Λ'` satisfy `v ∘ u = (Λ → Λ') ∘ f` as `R`-algebra maps `A → Λ'`. Then there
are an `R`-algebra `B : Type u`, finitely presented over `R`, and `R`-algebra maps
`g : A →ₐ[R] B`, `h : B →ₐ[R] Λ` with `h.comp g = f`, and an `s ∈ S` such that
`algebraMap R B s` is strictly standard in `B` over `R` (`IsStrictlyStandard R _`).

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 8.3 (Tag 07F4, printed p. 21):
"Let R → A → Λ be ring maps with A of finite presentation over R. Let S ⊂ R be a
multiplicative set. Let S⁻¹A → B′ → S⁻¹Λ be a factorization with B′ smooth over S⁻¹R.
Then we can find a factorization A → B → Λ such that some s ∈ S maps to an elementary
standard element (Definition 2.3) in B over R."

## Encoding

- `S⁻¹R` and `S⁻¹Λ` are given abstractly as `R'` and `Λ'` by the `IsLocalization`
  predicates; `S⁻¹Λ` is the localization of `Λ` at the image of `S` in `Λ`. The scalar
  towers say that the `R`-algebra structure of `Λ'` is the one through `R'` and through
  `Λ`, so `Λ'` is `S⁻¹Λ` as an `S⁻¹R`-algebra.
- `S⁻¹A = S⁻¹R ⊗_R A`, so `S⁻¹R`-algebra maps `S⁻¹A → B'` correspond bijectively to
  `R`-algebra maps `A → B'` (`B'` being an `S⁻¹R`-algebra). The first map of the
  factorization is therefore given by `u : A →ₐ[R] B'`. The factorization condition
  "`S⁻¹A → B' → S⁻¹Λ` composes to `S⁻¹f`" is, by the same universal property, equivalent
  to the equality `(v.restrictScalars R).comp u = (IsScalarTower.toAlgHom R Λ Λ').comp f`
  of `R`-algebra maps `A → Λ'`.
- "`B′` smooth over `S⁻¹R`" is `Algebra.Smooth R' B'`.
- The factorization `A → B → Λ` is `g`, `h` with `h.comp g = f`. The source defines
  elementary standard elements only for finitely presented algebras (Definition 2.3,
  "Let R → A be a ring map of finite presentation"), so finite presentation of `B` over
  `R`, stated explicitly here, is part of the source conclusion; the `B` constructed in
  the source proof is `R[x_1, …, x_{n+m}]/(s'_1 f_1, …, s'_c f_c, g_1, …, g_t)`.
- Weakening: the conclusion asks for a *strictly* standard element (`IsStrictlyStandard`,
  Definition 2.3, Tag 07C7; see `Langlands/CommutativeAlgebra/Popescu/Basic.md`) rather
  than an elementary standard one. Every elementary standard element is strictly
  standard for the same presentation and the same `c`: condition (2.3.1)
  `a = a′ det(∂f_j/∂x_i)_{i,j=1..c}` gives (2.3.3) by taking `a_I = a′` for
  `I = {1, …, c}` and `a_I = 0` otherwise, and (2.3.2) is (2.3.4). So the statement is
  implied by the source lemma. Its only use, in the proof of Lemma 8.4 (Tag 07F5), passes
  immediately to "hence strictly standard in A".
- All rings are in one universe `u`.
