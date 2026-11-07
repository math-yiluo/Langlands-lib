# Transport and finite filtrations of represented supercuspidal objects

Author: Worker 1452. Module
`Langlands.Representation.Exponents.RepresentedSupercuspidalityTransport`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This is derived support for Renard VI.5.3(iii), not a proof of that proposition.
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
VI.2.1, printed p.137 / PDF p.143, defines supercuspidality by vanishing of
Jacquet modules along every proper parabolic. VI.5.3(iii), printed p.173 /
PDF p.179, concludes that the filtered Jacquet module of the induced
representation is supercuspidal. The transport construction here is an internal
implementation of invariance of that definition under an actual group-scheme
isomorphism. The filtration argument reuses the published algebraic
coinvariant-vanishing theorem.

## Construction

`jacquetCoinvariantsEquivOfIso` takes an isomorphism of group schemes
`ε : H ≅ G` over a topological Hausdorff field `k : Type u`, a topological
group isomorphism `e : H(k) ≃ₜ* G(k)` equal to the rational-point map of `ε`,
an actual rational parabolic `p : P ⟶ H`, its rational Levi inclusion
`l : M ⟶ P`, its matching geometric unipotent radical `r : U ⟶ P`, and the
isomorphism of their subgroup multiplication. It constructs a complex linear
equivalence between the underlying spaces of the normalized Jacquet module of
`SmoothRep.pullback e A` along `p` and that of `A` along `p ≫ ε.hom`.
Both ambient group schemes are affine; their canonical point topologies are
assumed locally compact and nonarchimedean. No valuation, local-field,
connected-reductive, smoothness-of-the-group or representation-finiteness
assumption is used beyond this data.

The construction uses `IsParabolicSubgroup.comp_iso` to transport the
parabolic. The Levi, radical and multiplication data remain in `P`. The
literal radical point images correspond under `e`: each image witness is
carried across by the same point of `U(k)`, and the converse uses injectivity
of `e`. `GroupTransport.subgroupEquiv` restricts `e` to these images.
`Jacquet.Localization.transportEquiv` with trivial characters and the identity
on the coefficient space then constructs the quotient equivalence.

This is an equivalence of vector spaces, with the identity on coefficient
representatives. It does not compare normalized Levi actions. The scalar twist
in the normalized Jacquet action leaves the underlying quotient space
unchanged, which is sufficient for the vanishing consequences below.

## Consequences and implemented proofs

`isSupercuspidal_pullback_of_iso` proves that `IsSupercuspidal A` implies
`IsSupercuspidal (SmoothRep.pullback e A)`. The predicate is the existing
all-actual-parabolics definition from `LeviSupercuspidalInductionSupport`.
For a proper parabolic `p` in `H`, the transported map `p ≫ ε.hom` is proper:
an isomorphism of that composite would make `p` an isomorphism after
postcomposition with `ε.inv`. Supercuspidality of `A` annihilates the latter
Jacquet module. Injectivity of `jacquetCoinvariantsEquivOfIso` annihilates the
former.

`jacquet_subsingleton_iff_coinvariants` identifies vanishing of the actual
normalized Jacquet module with vanishing of the ordinary coinvariants by
`pointImage (r ≫ p)`. This follows from the published equality
`Jacquet.Localization.relations_one`; normalization changes only the action.

`isSupercuspidal_of_filtration` takes a finite `ObjectRepFiltration` of a
smooth representation `A`, smooth objects `B i` that are supercuspidal, and
actual `Representation.Equiv` witnesses between each graded representation
and `B i`. It proves `IsSupercuspidal A`. The carrier universes of `A` and
the `B i` are independent, and the length may be zero.
For each proper actual parabolic, the supplied representation equivalences
transport the trivial-character coinvariant quotients by
`Jacquet.Localization.representationEquiv`. Vanishing of the `B i` quotients
therefore gives vanishing of every graded quotient. The published
`Jacquet.coinvariants_subsingleton_of_filtration` then gives vanishing for
`A`. The relation comparison returns this to the actual normalized Jacquet
functor. No exactness premise or separately supplied smoothness of the graded
objects is needed.

The module does not construct a filtration of an induced representation,
identify its surviving geometric pieces or prove the geometric lemma. Those
remain separate obligations of the VI.5.3(iii) target.
