# Ordered monomials in the universal enveloping algebra

Author: Worker 1431.

For a field `k : Type u`, a Lie ring `L : Type v` with `LieAlgebra k L`,
a natural number `n`, and a supplied basis `b : Module.Basis (Fin n) k L`,
`Langlands.Algebra.UniversalEnveloping.orderedPBWMonomial b e` is the element

```text
ι(b 0) ^ e 0 * ι(b 1) ^ e 1 * ... * ι(b (n-1)) ^ e (n-1)
```

of Mathlib's actual `UniversalEnvelopingAlgebra k L`. Here `ι` is
`UniversalEnvelopingAlgebra.ι k`, not a separately supplied generator map.
The independent universes `u` and `v` impose no size relation between the field
and the Lie algebra.

The exact Lean formula is

```lean
(List.ofFn fun i : Fin n => UniversalEnvelopingAlgebra.ι k (b i) ^ e i).prod
```

`List.ofFn` lists the indices in ascending `Fin n` order; `List.prod` preserves
that multiplication order in this possibly noncommutative algebra.
`orderedPBWMonomial_eq_orderedProduct` exposes this formula by reflexivity.
`orderedPBWMonomial_empty` proves by simplification that `n = 0` gives one.
`orderedPBWMonomial_zero` simplifies zero powers and the resulting list of ones
to show that every zero exponent vector gives one.

No characteristic hypothesis is imposed, including in characteristic two.
Mathlib's `LieRing` requires an alternating bracket, so this uses the source's
condition `[x,x] = 0` even in that characteristic. No independence certificate,
normal form, or injectivity of `ι` enters the construction.

The mathematical source is Anne V. Shepler and Sarah Witherspoon,
*Poincare-Birkhoff-Witt Theorems*, retained 2014 author PDF, Section 2,
printed/PDF pages 2–3: the field and alternating-bracket conventions on page 2,
the tensor-quotient enveloping algebra and displayed PBW Basis Theorem on page 3.
The source's indices `1,...,n` are represented by `Fin n` starting at zero.
Its monomials are precisely the ordered powers constructed here.
The explicit empty and zero-exponent formulas are elementary consequences of
this product definition. This module constructs the monomials; it proves no
PBW independence or spanning theorem.

Registered source: `shepler-witherspoon-2014-pbw-theorems`, retained at
`literature/Poincare-Birkhoff-Witt Theorems.pdf`, SHA256
`4a7ac216c3ff4214ff953d2f8bd1643db8213822b68a5585155de2c5a1682d4a`.
