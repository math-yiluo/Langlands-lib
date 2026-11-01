# The division condition for the Harris algebra

Worker 57. This derived unit isolates the extra division condition on the
actual central simple algebra and proves the elementary module dimension
obstruction used in Kottwitz's projectivity argument.

Let `D : CentralSimpleUnitaryData E K A n` be the existing datum: `E` is a
totally real number field, `K` a totally complex quadratic extension of `E`,
and `A` a central simple `K`-algebra with dimension `n²` and `1 < n`. It
retains its actual second-kind involution. The condition `D.IsDivision` is
the proposition

```text
for every a in A, a != 0 implies IsUnit a.
```

It is an extra hypothesis; the file supplies no proof that a given central
simple algebra satisfies it and constructs no global division algebra.
The underlying algebra is nontrivial because its `K`-dimension is `n² > 0`.
Mathlib's `isSimpleModule_self_iff_isUnit` then proves
`isDivision_iff_isSimpleModule`: the condition is equivalent to
`IsSimpleModule A A` for the actual left regular module. The theorem
`isDivision_iff_opposite` transfers it to the opposite ring using the
opposite and unopposite maps on units. No matrix or split replacement is
made.

For the remaining declarations, `A` also has its specified rational algebra
structure. Let `M` be an additive commutative group with `A`- and
`ℚ`-module structures and the scalar tower `ℚ / A / M`.
`D.regularOrbitLinearMap m` is the actual rational linear map
`a ↦ a • m`. Distributivity and scalar associativity prove its linearity;
the application lemma is definitional. If `D.IsDivision` and `m ≠ 0`,
`regularOrbitLinearMap_injective` proves this map is injective: equal
images would give `(a-b) • m = 0`, and a nonzero `a-b` is a unit and
therefore cannot kill `m`.

If `M` is finite dimensional over `ℚ`, `finrank_le_of_nonzero` applies the
dimension inequality for that injection to obtain
`finrank ℚ A ≤ finrank ℚ M` from any nonzero `m`. The declarations
`eq_zero_of_finrank_lt` and `subsingleton_of_finrank_lt` consequently show
that a module of smaller rational dimension is zero. These statements
need no additional finiteness hypothesis on `A`: the injection into the
finite dimensional target already implies the required dimension bound.
They do not assert any result for an infinite dimensional `M`.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), I.7, printed p.51 (one-based PDF p.59), assumes that
the source algebra `B` is a division algebra of dimension `n²` over its
CM center. Here `A` denotes that underlying algebra and `K` its center.
Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Kottwitz, *Points on some Shimura varieties over finite fields*, JAMS 5
(1992), printed p.392 (PDF p.20), uses the equivalent conditions that
`End_B(V)` be a division algebra and that `V` be a simple `B`-module.
In the present regular-module specialization `V = A`, simplicity is
exactly the equivalence proved above; passing to the opposite does not
change division. His properness argument excludes a torus because its
rational character module has dimension at most half the dimension of
`V`. The new dimension lemmas prove the elementary algebraic obstruction
for any smaller module. They do not construct a torus, extend its algebra
action, prove the source's character-module dimension bound, construct a
Neron model or prove properness or representability. Those geometric
steps remain separate.
Registered source: `kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.

The equivalence with the regular module reuses pinned Mathlib's
`RingTheory/SimpleModule/Basic.lean`; the dimension bound uses
`LinearMap.finrank_le_finrank_of_injective`. The remaining deductions are
implemented here. The environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
