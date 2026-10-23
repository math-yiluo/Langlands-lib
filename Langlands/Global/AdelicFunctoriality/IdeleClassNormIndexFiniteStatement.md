# Finiteness and the degree-power bound for the idele-class norm index

`Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexFinite` is a
proposition definition. For number fields `K : Type u` and `L : Type v`
with `Algebra K L`, write

`H = (ideleClassNorm (K := K) (L := L)).toMonoidHom.range`.

Here the imported `ideleClassNorm` is the published continuous norm
`C_L → C_K` on the actual idele-class groups
`C_F = NumberField.IdeleClassGroup (𝓞 F) F`. Its underlying group
homomorphism has image `H = N_{L/K}(C_L)`. The statement asserts both:

1. `H.FiniteIndex`: the quotient `C_K / H` is finite.
2. There exists a natural number `r` such that
   `H.index ∣ (Module.finrank K L) ^ r`.

The two field universes are independent. Mathlib supplies
`FiniteDimensional K L` from the number-field and algebra instances,
so `Module.finrank K L` is the finite relative degree `[L : K]`.
The statement includes nonnormal extensions and degree one. It does
not assume a Galois action, reciprocity, idele-class cohomology
vanishing, or the second fundamental inequality. The exponent `r`
may depend on the extension, and the divisibility assertion is by
some power of the degree, not necessarily the degree itself.

Mathlib defines `Subgroup.index` as the natural cardinality of the
coset quotient, with value zero when that quotient is infinite.
`Subgroup.FiniteIndex` is the proposition that this index is nonzero;
`Subgroup.finiteIndex_iff_finite_quotient` identifies it with
`Finite (C_K ⧸ H)`. Thus the first conjunct explicitly asserts
finiteness, and the second uses the usual finite index. Since the
idele-class group is commutative, the coset quotient also has its
usual quotient-group interpretation.

The source is Emil Artin and John Tate, *Class Field Theory*, AMS
Chelsea edition (2009), Chapter VI §1, the first lemma on printed
p.20 (PDF p.29). The source uses `E/k` and `m`; these correspond to
`L/K` and `Module.finrank K L`. Its assertion that the norm index
is finite and divides a power of `m` is precisely the conjunction
above, specialized from global fields to number fields. Registered
original: `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`,
retained at
`/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.

This module states the lemma and supplies no proof. Artin–Tate prove
finiteness using a normal overextension, a sufficiently large finite
set of places, and local norm indices; they then use that every
`[L : K]`-th power in `C_K` is a norm to obtain the power bound.
For the actual Lean maps, the norm-of-inclusion power law is a
separate prerequisite for that proof route. This statement leaves
both the published norm and `ideleClassInclusion` unchanged.
Milne, *Class Field Theory*, v4.03 (2020), VII §§5–6, printed
pp.212–217 (PDF pp.221–226), was consulted for the surrounding
second-inequality argument; the exact arbitrary-extension lemma
formalized here is the cited Artin–Tate lemma.
