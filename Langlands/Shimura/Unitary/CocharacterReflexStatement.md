# Actual cocharacter and Hodge-function stabilizers

`ComplexCocharacterReflexStabilizer D C` states that, for a compatible CM section
and every rational algebra automorphism `s` of the complex numbers, the transported
first-factor Kottwitz cocharacter is inner-conjugate to the original scheme
cocharacter exactly when `s` preserves `D.realHodgeFunction C` on all CM embeddings.
The explicit hypothesis `IsCMSection E K Φ` is part of the proposition. The datum,
number fields, scalar towers, and Harris signature charts are those of the
published actual group-scheme and real Hodge constructions.

The left side asserts the existence of one complex group point `g` with
`g (s μ) g⁻¹ = μ` as an equality of group-scheme morphisms. It uses the existing
Galois transport of actual cocharacters and the inner-conjugacy relation; it does
not replace scheme equality by equality of weight multiplicities or by a condition
on complex-valued points. The right side is membership in the already defined
subgroup whose condition is `f(s ∘ i) = f(i)` for every CM embedding `i`.
The cocharacter is `kottwitzCocharacter C true`, retaining conjugation before
inversion and the first-factor convention. Its inverse-weight ranks equal the
real Hodge function.

This is an internal comparison target between two independently constructed
objects. Necessity is expected to follow from Galois rank transport and rank
invariance under actual conjugacy. Sufficiency requires an actual simultaneous
group-point conjugator and equality of scheme morphisms, not just the numerical
rank calculation. The statement imposes neither result as input and supplies no
proof of either implication.

Since `realReflexField` is already the fixed field of the Hodge-function stabilizer,
this comparison is the missing identification needed to interpret that field
through the actual cocharacter conjugacy class. This file does not yet construct
a separate cocharacter stabilizer subgroup or claim the fixed-field comparison is
proved. It makes no assertion about Shimura scheme levels or canonical models.
