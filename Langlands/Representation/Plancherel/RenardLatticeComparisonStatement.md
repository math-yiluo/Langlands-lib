# Actual split-component lattice and full representatives

Author: Worker 454.

This module states propositions for every nonarchimedean local field `F`
with the Library's field, valuation and topology instances, in both
characteristics. Let `Z` be an actual connected reductive group scheme
over `F`, let `T` be an actual commutative group scheme, and let
`s : T.toGrp ⟶ Z` satisfy `IsSplitComponent s`. This last predicate says
that `s` is a central split subtorus maximal among central split tori.
In the intended minimal-Levi application, `Z` is the actual algebraic
centralizer of the chosen maximal split torus `S`, and `T = S`.
Establishing connected reductivity of that centralizer and the
split-component property of `S → Z` is a separate structural comparison.
The assertions here apply to the actual split component of any connected
reductive group; they do not supply that comparison.

The valuation is the existing `rationalCharacterValuation Z`, with
coordinates `v_F(χ(z))` for the actual rational algebraic characters.
Its sign is positive and a uniformizer has order `+1`.
`rationalCharacterValuationImage Z` denotes its actual range `Λ(Z)`.
`splitValuationImage s` denotes the actual image of `T(F)` in that range.
No equality of `Λ(Z)` with a whole cocharacter lattice is assumed.

## Kernel and lattice targets

`SplitComponentKernelStatement` states

`(rationalCommonNormKernel Z).comap (rationalPoints.map s) = rationalCommonNormKernel T.toGrp`.

Thus the norm kernel on the split torus is exactly the pullback of the
ambient norm kernel. The already published valuation-kernel theorem
identifies these kernels with the respective character-valuation
kernels. This is Renard's intersection assertion, expressed without
identifying `T(F)` with a subtype by an implicit inclusion.

`SplitComponentLatticeStatement` states that `splitValuationImage s`
has finite index in `Λ(Z)` and that the valuation-image projection is a
bijection from `C0 T s` onto this subgroup. Here `C0` is the actual
cocharacter evaluation at the Library's chosen order-one uniformizer,
followed by `s` on rational points. The bijection explicitly includes
injectivity on `C0` and equality of its image with the image of all
`T(F)`. Finite index allows the latter subgroup to be proper.

## Full representative target

`FullLatticeRepresentativeStatement` asserts that a finite set `F0` of
actual points of `Z` exists whose map to `Λ(Z)/splitValuationImage s` is
bijective. It then asserts for every set satisfying this transversal
condition that `tildeC0 s F0 = C0 T s * F0` is a valuation section of all
of `Λ(Z)`. In addition the valuation map on the pairs `(c,f)` in
`C0 T s × F0` is injective. Consequently the product representatives do
not introduce repetition of valuation classes even at the pair level.
These are conclusions to be proved, rather than premises built into
`IsFiniteLatticeTransversal`.

`RenardLatticeComparisonStatement` is the conjunction of these three
closed proposition targets at the same universe. This file contains no
proof of any of them.

## Original source and derived packaging

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`:
V.2.3, printed page 105/PDF page 111, defines the positive integer
character valuation, its kernel and its actual image; V.2.5, printed
page 107/PDF page 113, defines the split-torus uniformizer section;
V.2.6, printed page 108/PDF page 114, states the kernel intersection,
lattice injection and finite index for the split component of a
connected reductive group. V.3.23, printed page 117/PDF page 123, uses
finite representatives to obtain a section `C_A F_M` of the full image
lattice. The pair-injectivity assertion spells out the uniqueness
implicit in this full section construction and its transversal choice.
This combined proposition is a derived packaging of those assertions
using the Library's actual point maps and actual image subgroups.

## Scope of the Cartan comparison

The targets stop before taking a dominant chamber. They do not assert
that a finite full-lattice transversal is chamber compatible, that it
lies in the dominant set, or that its positive products cover the
chamber. Those are additional requirements recorded separately in
`RenardRepresentativeData`. In particular the intersection
`(C0 * F0) ∩ Z_dom` and the product `C0Plus * F0` need an additional
comparison before they can be equated.

The maximal compact `K0` and the KP parahoric are absent from these
lattice statements. Relating the actual dominant valuation image to
`K0` double cosets, distinguishing it from the KP quotient by `Z(F)^0`,
and using the same `K0` in standard Levi subgroups remain separate
statement obligations of the Cartan task.
