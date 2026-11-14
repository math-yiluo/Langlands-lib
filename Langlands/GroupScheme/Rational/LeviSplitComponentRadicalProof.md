# A rational Levi split component in the parabolic radical

Worker 709. This proof module imports the published proposition
`Langlands.GroupScheme.LeviSplitComponentRadicalStatement` and proves it exactly
as `Langlands.GroupScheme.leviSplitComponentRadical`, with universe parameter
`u`. The field is arbitrary. The connected reductive ambient group, rational
parabolic, geometric solvable radical, rational Levi and specified Levi split
component are precisely the inputs of that proposition.

The provenance is a composition of published Library theorems, implementing
the direction from Levi factors to parabolic split components recalled in
Renard V.3.1. It does not introduce an additional structural assertion or
depend on an unproved sibling statement.

The proof constructs the factor `a : A → R` using
`IsRationalLeviSubgroup.centralTorusRadicalFactor`. Its composition theorem
gives `a ≫ r = aL ≫ l`, and its closed-subgroup theorem shows that `a` remains
a closed embedding of the original split torus.

For maximality, `parabolicDynamic` supplies a cocharacter presenting the
given parabolic. The published
`IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic`
then identifies the centralizer of the entire specified Levi split component
in the ambient group with the original Levi image.

Consider any split subtorus `b : B → R` and factor `f : A → B` with
`f ≫ b = a`. Since `B` is commutative, its ambient image centralizes `A`.
The centralizer equality puts that image inside the Levi, so
`IsSplitSubtorus.factorInClosedSubgroup` constructs a split subtorus
`bL : B → L`. Cancelling the parabolic embedding gives
`bL ≫ l = b ≫ r`. The published
`IsRationalLeviSubgroup.isCentral_of_factor_solvableRadical` shows that `bL`
is central in `L`. Cancelling the ambient Levi embedding also gives
`f ≫ bL = aL`. The maximality clause of the supplied `IsSplitComponent aL`
makes `f` an isomorphism, exactly the required maximality in `R`.

All containments and centralizers used here concern subgroup functors on all
test schemes. The conclusion makes no assertion of ambient maximality in `G`.
