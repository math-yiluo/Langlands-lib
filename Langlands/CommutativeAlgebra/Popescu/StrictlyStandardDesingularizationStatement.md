# Desingularization along a strictly standard element

`Langlands.CommutativeAlgebra.Popescu.StrictlyStandardDesingularizationStatement`
(universe `u`). Let `R` be a Noetherian commutative ring, `A`, `Λ` commutative
`R`-algebras with `A` finitely presented, all in `Type u`, and `π : R` such that
`π² x = 0 → π x = 0` for all `x : R` and `π² y = 0 → π y = 0` for all `y : Λ` (with `π`
acting through `algebraMap R Λ`). Let `f : A →ₐ[R] Λ` and assume
`IsStrictlyStandard R (algebraMap R A π)`. Let `C : Type u` be a commutative
`R ⧸ (π⁸)`-algebra, finitely presented over `R ⧸ (π⁸)` (and an `R`-algebra through the
scalar tower `R → R ⧸ (π⁸) → C`), with `R`-algebra maps `u : A →ₐ[R] C` and
`v : C →ₐ[R] Λ ⧸ (π⁸)Λ` such that `v.comp u` is `f` followed by the quotient map. Then
there are an `R`-algebra `B : Type u`, finitely presented over `R`, and `R`-algebra maps
`g : A →ₐ[R] B`, `h : B →ₐ[R] Λ` with `h.comp g = f`, such that
`Localization.Away (algebraMap R B π)` is smooth over `R` and
`(singularIdeal (R ⧸ (π⁸)) C).map v ≤ (singularRadical R h).map (Ideal.Quotient.mk ((π⁸)Λ))`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 7.3 (Tag 07F0, printed p. 20):
"Let R be a Noetherian ring. Let Λ be an R-algebra. Let π ∈ R and assume that
Ann_R(π) = Ann_R(π²) and Ann_Λ(π) = Ann_Λ(π²). Let A → Λ be an R-algebra map with A of
finite presentation and assume π is strictly standard in A over R. Let
A/π⁸A → C̄ → Λ/π⁸Λ be a factorization with C̄ of finite presentation. Then we can find a
factorization A → B → Λ with B of finite presentation such that R_π → B_π is smooth and
such that H_{C̄/(R/π⁸R)} · Λ/π⁸Λ ⊂ √(H_{B/R} Λ) mod π⁸Λ."

## Encoding

- `Ann(π) = Ann(π²)`: since `Ann(π) ⊆ Ann(π²)` always holds, the equality is the stated
  implication `π² x = 0 → π x = 0`.
- "π is strictly standard in A" means its image `algebraMap R A π` is
  (`IsStrictlyStandard`, Definition 2.3, Tag 07C7; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`).
- The factorization `A/π⁸A → C̄ → Λ/π⁸Λ` of the map induced by `f` is given by
  `R`-algebra maps `u : A → C` and `v : C → Λ/π⁸Λ` with `v ∘ u = (quotient) ∘ f`; since
  `π⁸ = 0` in `C`, `u` is the same as an `R/π⁸R`-algebra map `A/π⁸A → C`, and `R`-algebra
  maps out of `C` are the same as `R/π⁸R`-algebra maps. `C̄` is finitely presented over
  `R/π⁸R`, the base over which its singular ideal is formed; as `R/π⁸R` is finitely
  presented over `R`, this is equivalent to finite presentation over `R`.
- "`R_π → B_π` is smooth" is stated as `Algebra.Smooth R (Localization.Away (algebraMap R B π))`.
  This is equivalent: `R → R_π` is a localization (formally étale and finitely
  presented), so `B_π` is formally smooth over `R` iff over `R_π`, and `B_π` is finitely
  presented over `R` iff over `R_π` (using that `B` is finitely presented over `R`).
- `H_{C̄/(R/π⁸R)} · Λ/π⁸Λ` is `(singularIdeal (R ⧸ (π⁸)) C).map v`; `√(H_{B/R}Λ) mod π⁸Λ` is
  the image `(singularRadical R h).map (Ideal.Quotient.mk _)` of `h_B = √(H_{B/R}Λ)` in
  `Λ/π⁸Λ`.
- All rings are in one universe `u`.
