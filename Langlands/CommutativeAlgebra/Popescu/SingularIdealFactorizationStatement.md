# Factorization when the singular ideal generates the unit ideal

`Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationStatement` (universe `u`):
for commutative rings `R`, `A`, `Λ` in `Type u`, `R`-algebra structures on `A` and `Λ`
with `A` finitely presented over `R`, and an `R`-algebra map `f : A →ₐ[R] Λ`, if
`(singularIdeal R A).map f = ⊤`, then there are a smooth `R`-algebra `B : Type u` and
`R`-algebra maps `g : A →ₐ[R] B`, `h : B →ₐ[R] Λ` with `h.comp g = f`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 2.8 (Tag 07EU, printed p. 4):
"Let R → A → Λ be ring maps with A of finite presentation over R. Assume that
H_{A/R} Λ = Λ. Then there exists a factorization A → B → Λ with B smooth over R."

## Encoding

- `H_{A/R}` is `singularIdeal R A` (Definition 2.1, Tag 07C5; see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`), and `H_{A/R} Λ` is its extension
  `Ideal.map f`; "`= Λ`" is `= ⊤`.
- "Ring maps R → A → Λ" are encoded by `R`-algebra structures on `A`, `Λ` and an
  `R`-algebra map `f`; the factorization consists of `R`-algebra maps whose composite
  is `f`. All rings are in one universe `u`.
