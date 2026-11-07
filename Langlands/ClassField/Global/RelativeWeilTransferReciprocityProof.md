# Transfer reciprocity for relative global Weil groups

`relativeWeilTransferReciprocity` proves the existing published proposition
`Langlands.ClassField.Global.RelativeWeilGroup.RelativeWeilTransferReciprocityStatement.{u}`.
The theorem retains every original quantifier, including the local invariant
families, their class-formation and arithmetic-normalization assumptions,
and the global generating, restriction, inflation and local-compatibility
predicates. Its conclusion is surjectivity of the actual
`RelativeWeilGroup.transfer c F E` and equality of its kernel with the
commutator subgroup of the actual relative Weil group, for Galois extensions
of number fields in `Type u`. The protected statement and its imports are
unchanged.

The proof uses the concrete splitting-module route. Write `G = Gal(E/F)`
and let `C` be `ClassExtension.representative (c F E)`, the very normalized
cocycle used to define the relative Weil group `W`. Its cohomology class is
`c F E`. The published global idele-class `H¹` vanishing theorem, together
with `FundamentalClass.Generates c` and `FundamentalClass.Restriction c`,
gives bijectivity of integral cup by this class in every Tate degree.
The double-boundary calculation for the actual cocycle splitting
representation therefore makes that representation Tate acyclic.

The splitting representation has carrier `Additive C_E × Ideal G` with its
explicit twisted action. Its Tate vanishings in degrees minus one and zero
make the actual norm from coinvariants to invariants bijective. The
integral augmentation ideal has no invariant vectors, so first-coordinate
projection identifies splitting invariants with the original coefficient
invariants. Actual idele-class Galois descent identifies these with `C_F`.
Thus `splittingNormToBase_bijective` gives a bijection from splitting
coinvariants to the additive form of the actual base idele class group.

`coinvariantsAbelianizationEquiv` identifies splitting coinvariants with
`Additive (Abelianization W)`. On an extension element `t = (a,g)`, its
inverse sends the abelianization class to the coinvariant class
`extensionCoinvariant C t` of `(ofMul a,e_g)`, where
`e_g = delta(g⁻¹) - delta(1)`. Surjectivity of the quotient map to
abelianization therefore proves surjectivity of `extensionCoinvariant`.

The first private lemma establishes equality between the descended
splitting norm on these classes and the actual transfer. It applies
injectivity of the actual inclusion `C_F → C_E`. On one side,
`ideleClassInclusion_splittingNormToBase` computes inclusion of the norm;
on the other, `ideleClassInclusion_transfer` computes inclusion of transfer.
The generic `splittingNorm_extensionCoinvariant_toMul` then identifies the
two values in `C_E`. That comparison expands the splitting norm as the
product `∏ h, (h · a) C(h,g)` and computes Mathlib's actual transfer with the
inverse distinguished-section transversal. The coefficient-subgroup
identification is the inverse of the same actual coefficient inclusion
in both constructions.

The second private lemma uses this equality and norm bijectivity to prove
the required algebraic conclusions. Every base idele class has a splitting
coinvariant preimage and hence an extension-element preimage, giving
transfer surjectivity. If transfer kills an extension element, injectivity
of the descended norm makes its splitting coinvariant class zero. The
abelianization equivalence then makes its abelianization class the
identity. `Abelianization.ker_of` places it in the commutator subgroup.
The reverse inclusion is the published
`commutator_le_ker_transfer`.

The final theorem instantiates this argument with the original hypotheses.
This route uses the generating and restriction predicates to supply its
arithmetic input. The original local, inflation and local-compatibility
assumptions remain quantified in the exact proved proposition.
