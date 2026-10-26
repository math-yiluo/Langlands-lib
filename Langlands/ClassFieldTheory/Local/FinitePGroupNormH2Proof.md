# Relative H2 vanishing for finite p-group Galois extensions

Worker 28 authored the induction and this explanation. The upper norm-family
step reuses Worker 68's restriction-of-scalars argument from the shared finite
norm/H2 draft; Worker 68 is a coauthor for that contribution.

The theorem
`Langlands.ClassFieldTheory.Local.finitePGroupNormH2Vanishing.{u}` proves the
published proposition
`Langlands.ClassFieldTheory.Local.FinitePGroupNormH2Vanishing.{u}` from
[the statement module](FinitePGroupNormH2Statement.md). For every prime `p`
and finite Galois extension of fields `K L : Type u` in an arbitrary common
universe, assume that `Gal(L/K)` is a `p`-group and that the determinant norm
`Langlands.LocalClassField.normUnits E L` is surjective for every intermediate
field `E`. The conclusion is
`Subsingleton (relativeCohomology K L 2)`, the vanishing of the actual ordinary
relative second cohomology of the Galois action on the full field units.

## Implemented proof

The private lemma `cyclicH2_subsingleton_of_norm_surjective` handles a cyclic
finite Galois extension. It chooses a generator of its Galois group.
Surjectivity of the norm makes `normSubgroup K L` equal to the whole unit
group, so `NormQuotient K L` is a subsingleton. The published equivalence
`cyclicH2NormEquiv` identifies relative H2 with that quotient. Its injectivity
therefore gives the required subsingleton instance. This argument also covers
the trivial Galois group.

The private lemma `towerH2_subsingleton` uses the published
`finiteRelativeH2InflationExactness` for a finite Galois tower `K → E → L`.
Suppose the H2 groups for `E/K` and `L/E` are subsingletons. Every class for
`L/K` restricts to zero in the latter group. The equality of the kernel of
restriction with the image of inflation expresses that class as the inflation
of a class for `E/K`. That class is zero, so its image is zero. Thus every
class for `L/K` is zero. Only the image–kernel assertion of the existing
exactness theorem is needed.

The main proof fixes `p` and performs strong induction on
`Nat.card Gal(L/K)`, simultaneously for all field pairs in universe `u`.
In the cyclic case, the first component of the published theorem
`intermediateNormSurjectivityInheritance` supplies surjectivity of the norm
to `K`, and the cyclic lemma applies.

In the remaining case, the Galois group is nontrivial. A finite `p`-group is
nilpotent, and `p` divides its order. Mathlib's
`Group.IsNilpotent.exists_normal_index_eq_of_dvd_card` supplies a normal
subgroup `H` of index `p`. Put `E = IntermediateField.fixedField H`.
The canonical scalar tower gives finite Galois `L/E`; normality of `H`
gives Galois `E/K`.

The equivalence `IntermediateField.subgroupEquivAlgEquiv H` identifies
`Gal(L/E)` with `H`, so it is a `p`-group. Its order is strictly smaller:
`|Gal(L/K)| = |H| * p`, with `|H| > 0` and `p > 1`.
For each `F : IntermediateField E L`, the hypothesis at
`F.restrictScalars K` supplies surjectivity of the norm from `L` to `F`.
The carrier field and inclusion in `L` are unchanged by restriction of
scalars, and the canonical finite-dimensional instances give the required
type directly. This is the reused Worker 68 argument. The induction hypothesis
now gives vanishing for `L/E`.

The equivalence `IsGalois.normalAutEquivQuotient H` identifies `Gal(E/K)`
with `Gal(L/K)/H`, whose cardinality is `p`. Consequently `Gal(E/K)` is
cyclic. The second component of
`intermediateNormSurjectivityInheritance K L hn`, applied to `E`, supplies
surjectivity of the norm from `E` to `K`; the cyclic lemma gives vanishing
for `E/K`. The tower lemma combines the two vanishing results.

All scalar structures are the original algebra structure or canonical
intermediate-field structures. The finite-dimensional instances are derived
from `FiniteDimensional K L`. Norm inheritance is imported from
[its proof module](IntermediateNormSurjectivityProof.md), which establishes
the required determinant-norm transport and transitivity. The main theorem
has exactly the published proposition as its type, with no additional
norm-inheritance premise.

## Provenance

This is the finite p-group stage of the dévissage described in Jean-Pierre
Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67 (1979),
Chapter X, Section 7, Remark following Proposition 11, printed p.162
(PDF p.168). The registered source is `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The associated Proposition 11 and its proof are on printed pp.161–162
(PDF pp.167–168); Chapter IX, Section 5, Theorem 8 is on printed p.145
(PDF p.151). The implemented route uses cyclic norm comparison and
inflation–restriction, with strong induction on a finite p-group.
It proves the finite-extension proposition specified here. The general
finite-group Sylow argument belongs to its separate proof module.
