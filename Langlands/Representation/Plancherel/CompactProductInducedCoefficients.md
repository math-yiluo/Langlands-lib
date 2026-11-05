# Compact probability coefficients on actual product induction

Author: Worker 200.

This module constructs the coefficient map on the actual product-induced
function space with an exact diagonal integral against Haar probability on a
supplied compact open subgroup. It proves integrability for every vector,
the product-action translation law, common open bi-invariance, and equality of
the image with the coefficient space of normalized induction.

## Source and provenance

The motivating source is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, DOI 10.1017/S1474748003000082, registered as
`waldspurger-2003-plancherel`:

- I.1, printed p.240 / PDF p.6, fixes a special maximal compact subgroup `K`,
  normalizes intrinsic subgroup Haar measures by mass one on intersection with
  `K`, and gives `G = P K` for semistandard parabolics.
- I.3, printed p.243 / PDF p.9, defines positive half-modulus normalized
  induction and identifies induction of the smooth dual with the smooth dual
  of induction by a bilinear quotient integral.
- V.1, printed p.288 / PDF p.54, defines
  `L(ω,P) = I_{P×P}^{G×G}(E ⊗ E∨)`, identifies it with the coefficient tensor
  of `I_P^G E`, and defines its map to smooth functions by
  `v ⊗ ℓ ↦ (g ↦ ℓ((I_P^G ω)(g)v))`. Its image is the coefficient space of
  the induced representation.

These passages were read directly. The diagonal compact integral and this
general topological-group adapter are internal deductions from the Library's
product-induction comparison, actual coefficient map, and the separately
constructed probability-normalized duality. The source's representation
identifications are implemented by proved equivalences, rather than assumed
as inputs. V.1 also gives injectivity when induction is irreducible; no such
assumption or injectivity conclusion is used here.

## Objects, hypotheses and normalization

Let `G : Type uG` be a locally compact nonarchimedean group and let `P`, `M`,
`U` be actual subgroups with
`h : IsSemidirectDecomposition P M U` and closed `U`. Let
`A : SmoothRep.{0, uG, uV} ℂ M`; the group and representation-carrier universes
are independent. Write `I(A) = (normalizedInductionFunctor h hU).obj A` and
`L(A,P) = productInducedCoefficientObject h hU A`. The latter is the actual
normalized induced representation on `G × G`, from `P.prod P`, with the
published product semidirect decomposition, radical `U.prod U`, and inducing
object `productLeviObject A A.contragredient`. Its functions take values in
`A ⊗[ℂ] A.contragredient`. All actions and evaluations are those of these
original bundled objects.

The supplied `K : OpenSubgroup G` has compact underlying set, witnessed by `hK`.
The measure is exactly `κ = CompactInduction.measure K hK`, the intrinsic Haar
probability constructed in `CompactNormalizedInductionDuality`. It is fixed
independently of the inducing object, vectors and functionals.

The tensor equivalence and coefficient map require the following explicit
application data:

- `G` is Hausdorff and second countable, with its Borel measurable structure;
- `P` is closed and has an explicit `LocallyCompactSpace P` instance;
- the Levi projection `h.projection` is continuous;
- every `g : G` has a decomposition `g = q * k` with `q ∈ P` and `k ∈ K`;
- `Measure.modularCharacter g = 1` for every ambient `g`;
- for every `q : P`, its subgroup modular character equals
  `HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q`;
- `A.IsAdmissible`.

Compactness of the actual left quotient `P \ G` is derived from the compact
representatives `K`; it is not an extra premise of the equivalence, coefficient
map, or all-vector integral theorem. Admissibility of induction and the
scalar compact integration law are supplied by the proved compact duality
construction. Neither `A` nor its induction is required to be irreducible.

The elementary integrand results have fewer hypotheses. Local constancy uses
only the actual smooth product induction and the continuous diagonal map.
Integrability additionally uses the Borel structure and compactness of `K`;
it needs no second countability, Hausdorff, modulus, decomposition, projection
continuity, or admissibility hypothesis.

## Original diagonal contraction and integrability

`integrand h hU A K g` is the linear map from `L(A,P)` to `K → ℂ` obtained by
restricting the existing `productInducedCoefficientIntegrand` to `K`. Thus

\[
 J_g(F)(k)=\operatorname{ev}_A(F(kg,k)), \qquad
 \operatorname{ev}_A(v\otimes\ell)=\ell(v).
\]

The contraction is the tensor lift of
`(smoothDualPairing A.representation).flip`. It is complex bilinear, without
conjugation. `integrand_isLocallyConstant` applies the published local
constancy of actual induced evaluation, postcomposes with this contraction,
and precomposes with the continuous map `k ↦ (k*g,k)`.
`integrand_integrable` then uses continuity and compactness of `K`. This
proof applies to every actual induced vector without choosing a tensor
expansion.

## Tensor equivalence and coefficient map

Let `D = integralDualEquiv h hU hP hm K hK hPK hG hδ A hA`, so
`D : I(A)∨ ≃ I(A∨)` with its proved `κ`-integral pairing law.
`dualTensorEquiv` tensors the identity of `I(A)` with `D.symm`, giving the
`G × G` representation equivalence

\[
 I(A)\otimes I(A^\vee)\ \simeq\ I(A)\otimes I(A)^\vee.
\]

Its intertwining proof applies that of `D.symm` on pure tensors and extends
by tensor induction and linearity. With
`T = normalizedProductInductionTensorEquiv h h hU hU A A.contragredient`,
`coefficientTensorEquiv` is `dualTensorEquiv ∘ T.symm`. Its proof installs the
quotient compactness instance derived from `K`. `coefficientMap` composes this
equivalence with `normalizedCoefficientMap h hU A` and takes values in
`LocallyConstant G ℂ`.

`coefficientMap_tmul` cancels `T.symm ∘ T` and applies the exact pairing law
for `D` to the right translate of the vector. For induced functions `f` and
`fdual`, it proves

\[
 \operatorname{coefficientMap}(T(f\otimes fdual))(g)
   =\int_K fdual(k)(f(kg))\,d\kappa(k).
\]

This helper has an explicit quotient compactness instance only to name `T`
in its statement. The subsequent all-vector theorem derives this instance.

`coefficientMap_integral` proves, for every original `F : L(A,P)` and `g : G`,

\[
 \operatorname{coefficientMap}(F)(g)=\int_K J_g(F)(k)\,d\kappa(k).
\]

The proof uses surjectivity of `T` and tensor induction. The pure case combines
the preceding formula with `productInducedCoefficientIntegrand_tensor`. The
additive case uses linearity of the three maps and `integral_add`, justified
by the already proved integrability of each actual contraction. No tensor
expansion enters the definition of the map or changes its source carrier.

## Translation, invariance and image

`coefficientMap_action` applies the actual representation intertwining law
and the canonical coefficient tensor action formula to obtain, for
`x = (a,b) : G × G`,

\[
 \operatorname{coefficientMap}(x\cdot F)(g)
   =\operatorname{coefficientMap}(F)(b^{-1}ga).
\]

`coefficientMap_biInvariant` uses the existing coefficient-map theorem to
give one open subgroup `L` such that the resulting function is unchanged by
`g ↦ k*g*l` for every `k,l : L`.
`range_coefficientMap` proves that the image is exactly the range of
`normalizedCoefficientMap h hU A`. One containment applies
`coefficientTensorEquiv`; the other uses its inverse. This is the actual
smooth coefficient space of `I(A)`, without an injectivity assertion.

## Remaining scope

The construction imposes no field characteristic, splitness, quasisplitness
or GL-specific restriction. Application to every connected reductive
rational-point group still requires construction of the special compact and
the displayed decomposition, unimodularity and modulus comparison.
The supplied `K` is not yet identified with the special compact fixed by the
source.

The earlier `productInducedCoefficientMap` uses a compact-quotient Bruhat
measure whose specification leaves its absolute scale open. This module
constructs a separate probability-normalized map using the new compact
duality; equality with that earlier map or measure and independence of `K`
remain separate comparisons. Analytic coefficient bounds, Schwartz
membership, wave packets, isometry, spectral finiteness and Plancherel
inversion remain obligations of the standing program.
