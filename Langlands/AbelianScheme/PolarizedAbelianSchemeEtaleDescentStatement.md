# Effective étale descent of a polarized abelian scheme

Let \(B\) be locally noetherian, \(p\colon U\to B\) a surjective étale
morphism and \(A\) an abelian scheme over \(U\). The input
`GroupScheme.Descent.Datum p A.toGrp` is an actual isomorphism from the
first to the second pullback of the group along \(U\times_B U\), with the
cocycle on \(U\times_B U\times_B U\). The auxiliary data
`PolarizedFiniteLevel.Prerequisites` and `DualWitness` give the Picard,
dual and polarization comparisons used to express this for a chosen
dual presentation.

The polarization \(\lambda\colon A\to A^\vee\) has the Library's
isogeny and geometric ample Mumford presentation properties.
`PolarizedEtaleDescentCompatible` asks that the contravariant dual
pullback of the second pullback's polarization along the overlap
isomorphism equal the first pullback's polarization. The two pullbacks
use their canonical dual comparisons.

`PolarizedAbelianSchemeEtaleDescentStatement` asks for an actual abelian
scheme \(A_0\) over \(B\) with a dual witness and polarization
\(\lambda_0\), and an isomorphism \(p^*A_0\simeq A\).
Its underlying group isomorphism intertwines the canonical Čech datum
of \(p^*A_0\) with the supplied datum. It transports \(\lambda\) to the
canonical pullback of \(\lambda_0\). The étale morphism \(p\) can have a
non-quasi-compact domain or fibres, and the proposition is stated in the
arbitrary common universe of the schemes.

The geometric origin of the effectivity assertion is the relatively ample
line bundle \((1,\lambda)^*\mathcal P\) attached to a polarization by the
normalized Poincaré bundle. Faltings and Chai describe this construction
and its Mumford map \(2\lambda\) in *Degeneration of Abelian Varieties*
(1990), Chapter I, §1, Definition 1.6 and the following paragraph,
printed p. 4. The Poincaré comparison for a polarization-preserving
isomorphism respects the normalization at the unit section. This
comparison gives the descent isomorphism of the diagonal bundle, whose
cocycle follows from uniqueness of the rigidified isomorphism.

Locally on an affine open of \(B\), a finite affine refinement of \(p\)
gives a faithfully flat quasi-compact cover. Descent of a scheme with
a relatively ample invertible sheaf and coherent descent isomorphisms
applies there, by Grothendieck's theorem as stated in Bosch,
Lütkebohmert and Raynaud, *Néron Models* (1990), §6.1, Theorem 7,
printed p. 138. Full faithfulness of scheme descent on overlaps gives
the comparisons for gluing over \(B\). The group operations and
polarization descend as morphisms. Smoothness, properness, geometric
connectedness and the polarization properties can be verified on the
étale cover. The proposition expresses this consequence with the
Library's group-scheme Čech datum and actual dual-valued maps.
