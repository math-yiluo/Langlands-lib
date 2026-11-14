# All-degree creation on structure-sheaf cohomology

This module constructs creation by a degree-one class on every degree of the
ordered Čech homology of the structure sheaf, then transports it to actual
derived cohomology. It is internal infrastructure for the degree-two exterior
and coproduct comparison. Worker 327 authors the creation construction;
the ordered resolution, class maps, comparison, and degree-one cup product
used here are Worker 5218's prerequisite constructions.

Let `R : CommRingCat`, `π : X ⟶ Spec R`, and let `U : ι → X.Opens` be a
family indexed by a finite type in the same universe. Put
`O = SheafOfModules.unit X.ringCatSheaf` and
`K = AllSeq.cochainComplex π U O`. At the ordered Čech stage the family
need not cover `X` and its members need not be affine. Scalars are the actual
structure-morphism scalars of `AllSeq.cochain`; no unrelated algebra actions
are supplied.

## Creation by a cocycle

For an actual one-cocycle `z`, `creationCochainMap π U z n` is the
`R`-linear morphism `K.X n ⟶ K.X (n+1)` whose function is the existing
Alexander–Whitney product `AllSeq.cup π U z`. The factor `z` is on the left.
Its Leibniz identity gives

`d n ≫ c (n+1) = -(c n ≫ d (n+1))`.

`creationByCocycle π U z n` is the resulting `R`-linear homology morphism
`K.homology n ⟶ K.homology (n+1)`. It uses
`Cech.creationHomologyMap`: the adjacent components of the short-complex
morphism carry minus signs and the middle component is `c n`. That construction
also supplies the degree-zero case, where the left component is zero by the
shape of the natural-number complex.

`creationByCocycle_π_ι` characterizes the map between the homology projection
and inclusion by `iCycles ≫ c n ≫ pOpcycles`.
`creationByCocycleL` proves that this homology morphism depends `R`-linearly
on `z`. The proof cancels the epimorphic homology projection and monomorphic
homology inclusion, and then uses the bilinearity of the actual cochain cup
product.

## Independence of the creating representative

`cupZeroCochainMap` is multiplication by a zero-cochain, retaining the
structure-morphism `R`-action. If `z-z' = d h`, the cup-zero Leibniz identity
gives the homotopy

`c_z n = h_n ≫ d n - d n ≫ h_(n+1) + c_z' n`.

`creationByCocycle_eq_of_sub_eq_d` applies the generic homotopy equality of
`CechCreationClass` to conclude equality on homology in every degree.
The zero criterion for `AllSeq.classMap` then shows that `creationByCocycleL`
annihilates its kernel in the creating argument.

`creationH π U n` is the quotient lift, transported through the
quotient-by-kernel equivalence of the surjective degree-one class map. Its type
is

`K.homology 1 →ₗ[R] K.homology n →ₗ[R] K.homology (n+1)`.

`creationH_classMap` identifies creation by the class of `z` with
`creationByCocycle π U z n`.

## Formulas on classes and actual cohomology

For `b` a cocycle of degree `n+1`, `creation_cup_mem_ker` proves that
`cup z b` is a cocycle of degree `n+2`. The lemmas
`creationByCocycle_classMap` and `creationH_classMap_classMap` identify
creation on its class with the class of this product. They use naturality of
the homology projection and the cycle-inclusion formula of the generic
creation map. Since the cycle inclusion is monic, the latter identifies the
induced cycle with `AllSeq.cyclesOfKer` of the product.

Surjectivity of the degree-one class map in both arguments now proves
`creationH_one : creationH π U 1 = cupH π U`.

Assume in addition `[IsSeparated π]`, `⨆ i, U i = ⊤`, and that every `U i`
is affine. Write `Hⁿ = (relativeCohomology π n).obj O`. The comparison
`e_n = AllSeq.cohomologyEquiv π U hU hUa n` is the actual ordered
resolution comparison, with codomain `Hⁿ`. Define

`creationCanonical n x y = e_(n+1) (creationH n (e_1.symm x) (e_n.symm y))`.

Thus `creationCanonical` has type `H¹ →ₗ[R] Hⁿ →ₗ[R] Hⁿ⁺¹` for every
natural `n`. Its positive-degree representative formula is

`creationCanonical (n+1) (canonicalClass 0 z) (canonicalClass n b) =`
`canonicalClass (n+1) ⟨cup z b, closedness⟩`.

`creationCanonical_one` proves equality with the existing `cupCanonical`
as bilinear maps.

## Provenance and scope

The content is derived from the Library's actual Čech cup products and their
Leibniz identities, the signed short-complex descent and homotopy equality in
`CechCreationDescent` and `CechCreationClass`, and the ordered resolution
comparison in `AllSeqCohomology`, `AllSeqPullback`, and `AllSeqCup`.
The implemented proof uses these internal constructions; it attributes no new
geometric theorem to external literature.

The finite affine family remains an argument of `creationCanonical`.
This module does not prove independence from that family, all-degree pullback
naturality, creation–contraction identities, alternation in characteristic two,
exterior generation, or the host comparison. No field or characteristic
assumption is imposed on the construction.
