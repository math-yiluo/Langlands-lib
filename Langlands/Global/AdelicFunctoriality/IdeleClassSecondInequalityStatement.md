# The second inequality for the actual idele-class norm

Author: Worker 123.

`Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequality` is a
proposition-valued definition stating

\[
  [C_K : N_{L/K}(C_L)] \mid [L:K]
\]

for every Galois extension `L/K` of number fields. The carriers have
independent universes `K : Type u` and `L : Type v`. The hypotheses are
`Field K`, `NumberField K`, `Field L`, `NumberField L`, `Algebra K L`,
and `IsGalois K L`. Mathlib supplies `FiniteDimensional K L` from the
number-field structures and the algebra structure. The right side is the
positive natural number `Module.finrank K L`. The statement includes
nonabelian Galois extensions and the degree-one extension.

The left side is the subgroup index of
`(ideleClassNorm (K := K) (L := L)).toMonoidHom.range`.
The imported, published `ideleClassNorm` is the continuous homomorphism
from `NumberField.IdeleClassGroup (𝓞 L) L` to
`NumberField.IdeleClassGroup (𝓞 K) K`. These are the actual idele groups
modulo their principal subgroups, with their quotient topologies.
The norm sends the class of an idele to the class of the product of the
local determinant norms. The existing construction and its principal
compatibility are used unchanged. Taking `toMonoidHom` forgets only
the continuity field of this map; its range is the same image subgroup.

Mathlib's `Subgroup.index` is the natural cardinality of the coset space
and is zero when the coset space is infinite. Since zero cannot divide
the positive extension degree, the stated divisibility entails finite
index. Thus no separate finite-index hypothesis is imposed. The
conclusion is divisibility, rather than merely a numerical bound.

The original source is Emil Artin and John Tate, *Class Field Theory*,
AMS Chelsea edition (2009), Chapter VI, Section 1, “Second Fundamental
Inequality,” printed p. 19 (PDF p. 28). That passage states that for any
finite normal extension of global fields, the norm index divides the
degree. The first lemma on printed p. 20 (PDF p. 29) explicitly records
finiteness of the norm index. The Lean statement is the number-field
specialization: in characteristic zero finite normal extensions are
separable, so `IsGalois K L` expresses the source's normal-extension
hypothesis in this setting. The source's base field `k` is Lean's `K`,
and its extension field `K` is Lean's `L`.

Registered source: `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The retained original is
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`;
the passages above were read directly.

This module supplies a statement only. It proves no second inequality,
norm-index formula, or reciprocity theorem. A proof of the defined
proposition is a separate obligation.
