# Flatness descent along a specified local approximation system

`Langlands.Algebra.LocalApproximationFlatnessDescentStatement` is the proposition
of the Stacks Project, Lemma 10.128.3, tag
[00R6](https://stacks.math.columbia.edu/tag/00R6). It states that a specified local
algebra and module approximation system for an `R`-flat module has a component
`Mᵢ` that is flat over `Rᵢ`. This file defines the proposition; it contains no
proof of it.

The source is the registered snapshot
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
in the literature folder
`Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)`.
The exact passages read are `00R3.html`, Lemma 10.128.3 and its entire proof;
`00QL.html`, Lemma 10.127.13
([00QX](https://stacks.math.columbia.edu/tag/00QX)), all six clauses and its proof,
and the preceding Remark 10.127.12
([00QW](https://stacks.math.columbia.edu/tag/00QW)); and `00QV.html`,
Lemma 10.127.11, its proof and comments. No source-specific project errata note
was found. The 00QV snapshot includes the corrected polynomial quotient map;
its prime-localization condition is retained by the imported API.

## Ambient hypotheses and quantifiers

The proposition universally quantifies a nonempty directed preorder `ι`,
commutative local rings `R,S`, their algebra structure with
`IsLocalHom (algebraMap R S)`, and an additive commutative group `M` with an
`S`-module structure. It retains the hypotheses imported by the source phrase
“as in” 00QX: `EssFinitePresentation R S` and
`Module.FinitePresentation S M`.

It then applies to any specified
`D : LocalAlgebraSystem ι R S` and `E : LocalModuleSystem D M` satisfying
`E.IsApproximation`. Both structures are imported unchanged from
`Langlands.Algebra.LocalApproximationSystem`. The conclusion is
`∃ i : ι, Module.Flat (D.base i) (E.obj i)`, for the actual component types and
actions of this same `D,E`. It neither chooses a replacement system nor assumes
existence of an approximation as a separate theorem.

There are seven independent universe levels: `uI` for the index, `uA,uB,uN`
for component base rings, algebra rings and modules, and `uR,uS,uM` for the
three targets. No equalities or bounds among these universes are imposed by
this statement. The directed-preorder convention follows the published API;
antisymmetry is unnecessary for its transition and colimit data.

## Actual scalar restrictions

The target `R`-action on `M` is explicitly installed as
`Module.compHom M (algebraMap R S)`. Thus `r • m` means
`algebraMap R S r • m` using the given `S`-module structure. There is no
independently chosen `R`-module structure.

Inside the existential conclusion, the `D.base i`-action on `E.obj i` is
explicitly installed as
`Module.compHom (E.obj i) (algebraMap (D.base i) (D.alg i))`.
The algebra map uses `D.componentAlgebra i`, and its target action is the
stored `E.objModule i`. Thus both occurrences of flatness use the canonical
restriction along the actual local structure maps. Flatness of an unrelated
action cannot satisfy either occurrence.

## The six approximation clauses

The single assumption `E.IsApproximation` expands to exactly these six
conditions from 00QX:

1. `E.IsColimit`: the canonical maps from the actual `Ring.DirectLimit`
   constructions to `R` and `S`, and from the actual
   `AddCommGroup.DirectLimit` to `M`, are bijective. The stored semilinear
   cocone maps preserve the module actions and commute with transitions.
2. Every `D.base i` is essentially of finite type over `ℤ`.
3. Every `D.alg i` is essentially of finite type over `D.base i`.
4. Every `E.obj i` is finite as a `D.alg i`-module.
5. For each `h : i ≤ j`, `D.IsPrimeLocalization h` holds for the canonical map
   `D.ringBaseChangeMap h : Sᵢ ⊗[Rᵢ] Rⱼ →+* Sⱼ`. Its algebra structure is
   precisely `(D.ringBaseChangeMap h).toAlgebra`, and the prime is a witness
   in this actual tensor product.
6. For each `h : i ≤ j`, the actual `Sⱼ`-linear map
   `E.moduleBaseChangeMap h : Sⱼ ⊗[Sᵢ] Mᵢ →ₗ[Sⱼ] Mⱼ` is bijective.
   It sends `s ⊗ m` to `s • E.map i j h m`; the source's module-first tensor
   order is exchanged by the canonical tensor symmetry.

The ring tensor map in clause 5 sends `s ⊗ r` to
`D.algMap i j h s * algebraMap (D.base j) (D.alg j) r`, with the base-change
action on `Rⱼ` induced by `D.baseMap i j h`. These are the specified maps,
not arbitrary tensor comparisons. Clause 5 is a prime-localization condition,
not bijectivity of the ring map. Remark 00QW explains why an arbitrary
finite-type approximation need not satisfy it.

No flatness of transitions or component base rings, field or domain hypothesis,
or component flatness conclusion is stored in these six clauses.

## Source proof and scope

The source proof starts at one index and expresses the first Tor group with
the component residue field as the kernel of the maximal-ideal tensor map.
It uses Noetherianity and finiteness to choose finitely many kernel generators.
Target flatness and compatibility of tensor products with colimits allow those
generators to vanish at a later index. The local transition criterion 00MO
then gives flatness at that later component. This describes the source route;
no Tor comparison, kernel-vanishing argument or application of 00MO is proved
in this statement module.

The displayed conclusion of 00R6 is existential. Flatness at every sufficiently
large index requires a separate forward-propagation result using clauses 5
and 6. Such a result combines flat base change with localization of the
resulting module over the auxiliary algebra `Sᵢ ⊗[Rᵢ] Rⱼ`, followed by transport
through the actual module comparison. It is not an extra hypothesis or a
stronger conclusion of the proposition defined here. General colimit ascent
and the existence assertions of 00QV/00QX are also separate obligations.
