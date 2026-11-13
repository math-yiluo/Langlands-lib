# Actual derived-cover lifts and root intersections of unramified zero fixers

This internal unit constructs actual rational lifts of relative-root points
through a supplied simply connected derived cover over an arbitrary field.
It then proves the root part of the neutral/zero-fixer comparison for every
supplied unramified zero datum, independently of its chosen maximal torus.

Let `k : Type u` be any field, `G` affine, and `i : S.toGrp ⟶ G` a maximal
split torus. Supply `d : D ⟶ G` and `π : H ⟶ D` with
`IsSimplyConnectedDerivedCover d π`. Connected reductivity of `G` follows
from this cover predicate. For each relative root `a`, the published
rank-one factorization and reflection construction give a reflection
representative and its coroot. The existing `derivedCocharacter` is the
negative commutator of that coroot with the reflection automorphism. It
lands in the actual derived subgroup and pairs with `a` to `4`.

Factor this cocharacter through the specified `d`. Its positive pairing
places every point of the actual `a` root group in its dynamic unipotent
subgroup. The existing derived-cover unipotent lifting theorem therefore
gives a point of `H(k)` above the original root point. The definition
`rootPointDerivedCoverLift` chooses such an actual point, and
`rootPointDerivedCoverLift_map` proves its image under the originally
specified `π ≫ d` is the original point. This proof generalizes the
published local-field wrapper in `KPSharpCoverImageProof`; the algebraic
argument requires neither a valuation nor an apartment axiom.

Now take `C : MaximalUnramified.BuildingData F G` and any
`E : UnramifiedZeroDatum F G`. Apply the arbitrary-field construction over
`inertiaFixedField F` to `C.i` and `E`'s actual derived cover. Thus every
relative-root group for `C` lies in `E.simplyConnectedImage`, hence in
`E.zeroPoints`. Taking the join shows `C.sharpFixer Ω ≤ E.zeroPoints` for
every apartment subset `Ω`. No relation between `E.T` and `C.S` is needed.

Intersecting a root group with `E.zeroPoints` consequently does not change
it. The existing generic full-building-fixer/root identity then gives
`rootGroupPoints C.i a ∩ (E.zeroPoints ∩ fixer(Ω)) = rootFixer(a, Ω)`.
This holds for every subset, including the empty subset, without
nonemptiness or affine boundedness. From a supplied relative-component
model `D` with the required full one-fixer integral-point equality,
`UnramifiedNeutralRoots` identifies the neutral/root intersection with the
same root fixer. Therefore the neutral and arbitrary zero-fixer root
intersections agree exactly.

The provenance is internal: it composes the existing rank-one reflection,
derived commutator cocharacter, unipotent cover lifting, generic root/fixer
identity, and constructed neutral-root comparison. It does not identify
the entire neutral subgroup with the arbitrary zero fixer, construct the
ambient model, compare torus norm-Iwahori images, prove choice independence
of the zero datum, or prove `UnramifiedParahoricModelStatement`.
