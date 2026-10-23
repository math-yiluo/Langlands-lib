# The prime-degree second inequality for actual idele classes

Author: Worker 28.

`Langlands.Global.AdelicFunctoriality.IdeleClassPrimeDegreeSecondInequality`
is a proposition-valued definition asserting

\[
  [L:K]\text{ prime}\quad\Longrightarrow\quad
  [C_K:N_{L/K}(C_L)]\mid[L:K]
\]

for every Galois extension of number fields. Its complete telescope
quantifies `K : Type u` and `L : Type v` in independent universes, with
`Field K`, `NumberField K`, `Field L`, `NumberField L`, `Algebra K L`,
and `IsGalois K L`. The prime-degree hypothesis is exactly
`Nat.Prime (Module.finrank K L)`. Number-field structures and the algebra
structure supply finite relative dimension. No cyclicity or primitive
root of unity is supplied as extra data. The Galois group has order equal
to the extension degree and is cyclic when that degree is prime; this
explains correspondence with the cyclic prime-degree source formulation.
The definition itself does not prove that group-theoretic fact.

The index is
`(ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index`.
The imported `ideleClassNorm` is the existing continuous homomorphism
from the actual idele classes of `L` to those of `K`, induced by the
product of the local determinant norms on ideles. Its construction,
principal compatibility, and quotient topology are unchanged.
`toMonoidHom` forgets continuity without changing the function or image.
The extension-of-scalars map `ideleClassInclusion` is also unchanged;
it is not needed to express this conclusion.

Mathlib's natural-valued `Subgroup.index` is zero for an infinite coset
space. Since the extension degree is prime and therefore positive,
divisibility by the index also entails finite index. The statement thus
imposes no separate finite-index hypothesis and asserts divisibility,
not just a numerical upper bound. For a prime degree its conclusion
allows index one or the prime degree.

The primary source is Emil Artin and John Tate, *Class Field Theory*,
AMS Chelsea edition (2009), Chapter VI §1, printed pp.19–21
(PDF pp.28–30). The second fundamental inequality is stated on p.19;
Reduction 1 on p.20 isolates cyclic prime-degree extensions, and
Reduction 2 on pp.20–21 passes to a base containing a primitive root
of the relevant prime order. Chapter VI §3, printed pp.24–27
(PDF pp.33–36), proves the Kummer case. The deduction on p.26 uses
the first inequality. The present statement is the number-field
prime-degree specialization before imposing the auxiliary root-of-unity
condition. In the source, the base `k` is Lean's `K` and the extension
`K` is Lean's `L`.

An alternative algebraic route appears in J. S. Milne,
*Class Field Theory*, v4.03 (2020), Chapter VII §6, printed
pp.213–217 (PDF pp.222–226). Lemma 6.1 on p.214 gives the cyclotomic
reduction; the subsequent argument uses Kummer extensions, S-units,
selected primes, local norms and subgroup indices. These are proof
prerequisites, not extra hypotheses of this definition.

Registered originals, read directly at the cited locations:

- `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
  retained at
  `/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
- `milne-2020-class-field-theory`, SHA256
  `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`,
  retained at
  `/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.

This is a statement only, following the actual norm and index convention
of the published `IdeleClassSecondInequality` statement by Worker 123.
It imports no proof of the general second inequality, global reciprocity,
global fundamental classes, or idele-class H¹ vanishing. Those downstream
results cannot supply a circular proof of this prerequisite. Proving this
proposition, including the cyclotomic reduction and arithmetic inputs,
remains a separate obligation.
