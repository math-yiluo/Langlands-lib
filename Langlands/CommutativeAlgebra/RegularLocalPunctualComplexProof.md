# The punctual perfect complex lemma over a regular local ring

Authors: Worker 1015, Worker 975, and Worker 413.
Worker 975 supplied the finite-length acyclicity proof and reversed-dual homotopy
construction. Worker 413 supplied the first-differential generation and dual
cokernel constructions. Worker 1015 supplied the other supporting constructions
and the final assembly.

The theorem
`Langlands.CommutativeAlgebra.regularLocalPunctualComplex` proves exactly
`Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement.{u}`.
It applies to every universe `u`, every regular local ring `R` of natural
dimension `g`, and every strictly perfect integer cochain complex `K` satisfying
the four original assumptions: residue homology supported in `[0,g]`, residue
homology of dimension one at zero, maximal-ideal-power annihilation of every
homology module, and the stated nonfreeness test over every first-order quotient
`R/J`. It concludes that `Hⁱ(K) = 0` for `i ≠ g` and that `H^g(K)` is isomorphic
to the residue field as an `R`-module. No additional hypothesis is imposed.

The implemented proof follows the local algebra in Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, (9.6)–(9.9), printed pp.128–130 / PDF pp.132–134,
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
The original statement's paired Markdown explains the abstraction from that
geometric argument. This proof uses only module complexes and commutative
algebra.

## Finite-length acyclicity

The companion helper `RegularLocalFiniteLengthAcyclicityProof`, included with
this proof, establishes `regularLocalFiniteLengthAcyclicity` with the exact type
of the supporting acyclicity proposition. A bounded finite free complex
concentrated in nonnegative degrees, with homology killed degreewise by powers
of the maximal ideal, has no homology below the ring's dimension. Its upper
term bound can be arbitrary.

The proof inducts on dimension. For positive dimension, choose a prime
parameter `x ∈ m ∖ m²`. The regular local ring is a domain, and reduction modulo
`x` is regular local of dimension one less. Freeness gives the short exact
sequence of complexes consisting of multiplication by `x` followed by reduction
modulo `x`. The long exact homology sequence shows that the reduced homology is
killed by the product of annihilator ideals of two neighboring original
homology modules. Thus it again satisfies maximal-ideal-power annihilation.
Induction makes the reduced homology vanish in the needed lower degree.
Exactness then makes multiplication by `x` injective on the original homology.
A power of `x` kills that module, so it is zero. In dimension zero, the degrees
under consideration are negative, where the terms already vanish.

## Residue-resolution duality

`regularLocalResidueResolutionDuality_of_acyclicity` proves the supporting
duality proposition from that acyclicity input. Choose `g` generators of the
maximal ideal using regularity and the minimal generator count, as implemented
in `RegularLocalKoszulComparison`. The finite subset Koszul cochain complex has
finite free terms in degrees `[0,g]`. Generator insertion homotopies annihilate
each homology module by the entire maximal ideal. Acyclicity therefore makes
its homology vanish below `g`, and its upper term bound gives vanishing above
`g`. Its top homology is `R/m`, by the explicit empty-subset differential
calculation in `FiniteKoszulEnds`.

For any finite free complex `C` resolving `R/m` in degree `g`, the comparison
construction gives a homotopy equivalence from `C` to this Koszul complex.
It first identifies both derived images with the single complex on their
degree-`g` homology, then lifts the resulting derived isomorphism between
strictly perfect complexes to a homotopy equivalence.
`reversedDualHomologyIsoOfHomotopyEquiv` transposes that equivalence and
identifies the homology of their reversed duals. The first differential of the
Koszul cochain complex has order ideal exactly the parameter ideal. The
rank-one degree-zero term and this equality identify its reversed-dual top
homology with `R/m`, again by `FiniteKoszulEnds`. Composing the two homology
isomorphisms gives the required top homology of the reversed dual of `C`.

## Assembly for the original complex

The final theorem applies the previously constructed
`regularLocalPunctualComplex_of_acyclicity_of_residueResolutionDuality` to the
now-proved acyclicity and duality inputs. That reduction replaces `K` by its
minimal finite free model `M`. The two residue-homology assumptions force
its terms to be supported in `[0,g]` and identify its degree-zero term with
`R`. The actual homotopy equivalence transfers the annihilator hypotheses.
Acyclicity and the term bounds then make `Hⁱ(M)` vanish away from `g`.

The reversed dual `D` of `M`, centered at `g`, is again finite free in `[0,g]`.
The support argument in `PunctualHomologySupport` transfers
maximal-ideal-power annihilation to its homology: after inverting an element
of `m`, the original complex is acyclic, so its bounded projective
localization is contractible; its reversed dual is then acyclic as well.
Finite generation recovers an annihilator power over the original ring.
Acyclicity consequently makes `D` exact away from `g`.

The first-order quotient hypothesis forces the order ideal of the first
differential of `M` to equal `m`, by `PunctualFirstDifferential`. Otherwise
Nakayama's lemma and the ascending chain condition give a first-order ideal
`J` containing that order ideal. The differential vanishes after reduction
modulo `J`, producing the forbidden rank-one free degree-zero homology.
The dual cokernel calculation therefore gives `H^g(D) ≅ R/m`.
Applying the proved residue-resolution duality to `D` identifies the top
homology of its reversed dual with `R/m`. Finite free evaluation identifies
the twice reversed dual with `M`. These isomorphisms, followed by the homology
isomorphism of the original homotopy equivalence, give the conclusion for `K`.

All constructions include `g = 0`: the parameter family is empty, its span is
the zero maximal ideal, and the degree bounds and rank-one endpoint
calculations still apply. The published target and its imports are unchanged.
