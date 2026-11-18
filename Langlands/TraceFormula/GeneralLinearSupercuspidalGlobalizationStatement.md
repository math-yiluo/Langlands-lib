# Globalization of supercuspidal representations of `GL_n`

`Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationStatement.{u, w}` states that
finitely many prescribed irreducible supercuspidal representations occur up to unramified
twists in one irreducible summand of the group-scheme cuspidal `L²` space. Ramification at
other finite places is allowed only at a single auxiliary place chosen in advance.

## Setting

Let `K : Type u` be a number field and `n : ℕ`. Write `G` for the group scheme
`GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)` and `A` for
`AdelicGroupPoints K G`. Affineness and smoothness are supplied by the Library's
`GroupScheme.GeneralLinear.isAffine_groupScheme` and `GroupScheme.GeneralLinear.smoothStatement`.

The group data specialize `GroupSchemeFullAEL2CuspidalDecompositionStatement` to `G`. They
consist of `hPD : ParabolicDynamicStatement`, `hG : IsConnectedReductive G`, a commutative
group scheme `T` over `Spec K` with a central map `i : T.toGrp ⟶ G` (`hc`), and an
isomorphism `e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I` for a finite type `I`.
The character restriction along `i` is injective (`hi`) with finite-index image. The data
also include right invariance of `Measure.haar` on `normOneSubgroup K G`.

The model uses the left quotient `[G] = G(K) A⁺ \ A` with the Library's Haar quotient
measure, where `A⁺` is the image of the positive real subgroup of the supplied central
torus. The subgroup defining `[G]` is `positiveRationalSubgroup K G T i`. Set
`S = fullAEL2CuspidalSubmodule K G hPD hG T i hi I e hc` in `L²([G])` and let `πc` be
`fullAEL2CuspidalBoundedRightAction K G hPD hG T i hi I e hc`, the right action on `S`.
For `hf : Integrable f ν`, the operator `R_S(f)` is
`fullAEL2CuspidalIntegratedAction K G hPD hG T i hi I e hc ν f hf`.

At a finite place `v : Langlands.Global.FinitePlace K`, the field `K_v` is
`v.adicCompletion K`, also `placeCompletion K (.inr v)`. The matrix group
`GeneralLinear n K_v` carries the matrix-units topology. The proposition takes families of
`MeasurableSpace`, `BorelSpace`, `LocallyCompactSpace` and `TotallyDisconnectedSpace`
instances on these groups, indexed by all finite places. They express the Borel
measurable structure and the local topological properties of the matrix group over `K_v`.
The map `eᵥ v` is the multiplicative homeomorphism from
`PlaceGroupPoints K G (.inr v)` to `GeneralLinear n K_v` supplied by
`GroupScheme.GeneralLinear.affinePointsHomeomorph`. The Library's `atPlace K G (.inr v)`
and `ofPlace K G (.inr v)` are the projection and insertion for the group-scheme points.
Thus `incl v` is the insertion of the matrix group into `A`, given by
`ofPlace K G (.inr v) ∘ (eᵥ v)⁻¹`. The subgroup `GL_n(𝒪_v)` is
`FiniteAdelicGL.localIntegral K n v`, which requires integral entries for the matrix and
its inverse.

## Statement

For all the data above, let `Sc` be a nonempty finite set of finite places and let `vaux`
be any finite place outside `Sc`. Let `V v : Type w` be a family of complex vector spaces
and `π v : Representation ℂ (GeneralLinear n K_v) (V v)` a family of representations.
For each `v ∈ Sc` assume `Representation.IsIrreducible` and `GeneralLinear.IsSupercuspidal`
for `π v`. The latter requires smooth admissibility and vanishing of the Jacquet quotients
for the unipotent radicals of proper block parabolics and their conjugates.

There is a single submodule `P : Submodule ℂ S` with `CompleteSpace P` satisfying all of the
following.

1. `P ≠ ⊥` and `πc a` preserves `P` for every `a ∈ A`. Every closed invariant submodule
   `Q ≤ P` is `⊥` or `P`. The complete subspace `P` is closed in `S` and is an irreducible
   summand for the unitary right action.
2. There is one `x ∈ P` with `x ≠ 0` and `πc (incl w k) x = x` for every finite
   `w ∉ Sc` with `w ≠ vaux` and every `k ∈ FiniteAdelicGL.localIntegral K n w`.
3. For each `v ∈ Sc` there is a character `χ_v : K_vˣ →* ℂˣ` with `χ_v t = 1` whenever
   `Valued.v (t : K_v) = 1`. This is triviality on the units of `𝒪_v`. Both conclusions
   use the same twist `ρ = Langlands.twist (χ_v.comp GeneralLinear.determinant) (π v)`.

   - A nonzero complex-linear map `Tv : V v →ₗ[ℂ] P` satisfies
     `(Tv (ρ g y) : S) = πc (incl v g) (Tv y)` for all `g` and `y`. The character twist
     preserves irreducibility, so the map is an embedding.
   - For every Haar measure `μv` on `GeneralLinear n K_v` and Haar measure `ν` on `A`,
     there exist `hρ : IsAdmissible ρ` and `C : (A → ℂ) → ℂ`. For every
     `fv : SchwartzBruhat (GeneralLinear n K_v)` and `fw : A → ℂ` satisfying
     `fw (g * ofPlace K G (.inr v) x) = fw g` for all `g, x`, put
     `f(g) = fv (eᵥ v (atPlace K G (.inr v) g)) * fw g`. Given `hf : Integrable f ν`, let
     `X = P.orthogonalProjectionOnto ∘L R_S(f) ∘L P.subtypeL` be the compression to `P`.
     If `IsTraceClass X`, then
     `operatorTrace X = Character.distribution μv ρ hρ fv * C fw`.

The distribution character is the trace of the finite-rank action of the locally constant,
compactly supported test `fv`, integrated against `μv`. The quantifier order lets `C` depend
on the earlier choices, including both measures, and uses that same `C` for all test pairs.
The trace identity is the untwisted clause of the project target
`GroupSchemeCuspidalLocalTraceFactorizationStatement` (Task 7701), with the local representation
identified with `ρ` and transported across `eᵥ v`.

## Why the unramified twist is needed

On the quotient `[G]`, the unitary central character `ω_P` of an irreducible summand is
trivial on the principal ideles and on `A⁺`. For `K = ℚ`, `Sc = {p}` and `vaux = q`, write
the idele supported at `p` with value `p` as the principal idele `p` times an idele with
value `1` at `p`, value `p⁻¹` at each prime `ℓ ≠ p`, and positive real value at infinity.
At `ℓ ∉ {p, q}`, the fixed-vector condition forces `ω_{P,ℓ}` to be trivial on local units.
At `q`, the restriction of `ω_{P,q}` to the compact unit group has finite image. Thus
`ω_{P,p}(p) = ω_{P,q}(p)⁻¹` is a root of unity. Already for `n = 1`, the smooth character
`π_p(t) = exp(2πi θ ord_p(t))` with `θ` irrational has infinite-order value at `p` and
cannot embed as the untwisted local representation of such a summand. An unramified twist
by `χ_p ∘ det` multiplies the value of the central character at the scalar `p` by
`χ_p(p)^n`.

## Proof sketch

1. For positive rank and `v ∈ Sc`, truncate a coefficient of the contragredient of `π v`
   with nonzero pairing at the identity to `G_v^0`, the open subgroup of matrices with unit
   determinant. One may first make `π v` unitary by an unramified twist, which is trivial
   on `G_v^0`. The coefficient is compactly supported modulo the center, and imposing
   unit determinant bounds the valuation of the central scalar, giving compact support.
   Jacquet vanishing gives the cuspidal radical integrals. On the regular elliptic set in
   `G_v^0`, the orbital integral is a nonzero multiple of the character evaluated at the
   inverse element. The character is a nonzero constant there sufficiently close to `1`,
   by the local Jacquet–Langlands character identity as in Henniart–Lemaire II.6.7. In
   particular one can choose a regular elliptic point of determinant one where the orbital
   integral is nonzero. Such points occur near `1` in the norm-one torus of a degree-`n`
   local field extension. Schur orthogonality on `G_v^0` and restriction to this normal
   subgroup show that any irreducible admissible representation with nonzero trace on
   this test is an unramified determinant twist of `π v`. The relevant quotient
   `GL_n(K_v)/G_v^0` is the determinant valuation group.
2. Use strong approximation for `SL_n` away from the archimedean places to choose a
   rational element `γ ∈ SL_n(K)` close to those points and to a regular elliptic point at
   `vaux`, integral at every other finite place. In rank one use `γ = 1`. Use the
   normalized integral-subgroup indicators at the other finite places and an auxiliary
   test supported in the regular elliptic locus near `γ` with positive orbital integral.
   Average a nonnegative archimedean bump near `γ` along `A⁺` to get the archimedean
   factor of the test on `A⁺ \ A`. The cuspidal factors at `Sc` give cuspidal image.
3. On the norm-one model of `A⁺ \ A`, the compact test support allows only finitely many
   rational characteristic polynomials because their coefficient vectors lie in a
   compact subset of the adeles and `K` is discrete there. The auxiliary support makes
   the contributing classes regular semisimple and elliptic. Their characteristic
   polynomials determine their rational conjugacy classes in `GL_n`. Shrink the support
   at `vaux` around `γ` to exclude the other polynomials. The simple trace formula gives
   a nonzero cuspidal trace, with geometric side the positive centralizer volume times
   the nonzero orbital integral at `γ`. Some cuspidal summand `P` has nonzero trace on
   this test. Right invariance at all the remaining finite places makes the test operator
   factor through their joint fixed-vector space, giving the single vector of part 2.
4. Use the type I property of `GL_n(K_v)` to split the unitary representation on `P`
   at each prescribed place into its local factor and the factor away from that place.
   The local factor has admissible smooth vectors. The nonzero trace and step 1 identify
   this smooth module with `ρ`. Tensor the identification with a nonzero vector in the
   other factor to obtain `Tv`. For the trace identity, normalize Haar measure on the
   complementary factor so that its product with `μv` gives `ν`. A right-invariant `fw`
   descends to that factor. When the local test is nonzero, integrability of the product
   gives integrability of the complementary weight. The compressed operator is the
   tensor product of the finite-rank local operator and the integrated complementary
   operator. When the local operator is nonzero, composing with a vector inclusion and
   a matrix coefficient in that factor recovers a nonzero multiple of the complementary
   operator. Thus trace class of the compression gives trace class of the complementary
   operator. Take `C fw` to be its trace for integrable complementary weights with
   trace-class action and zero otherwise. A zero local operator gives zero on both sides.

In rank zero the groups are trivial, the cuspidal space is one-dimensional and the
prescribed irreducible representations are one-dimensional. The embedding and fixed
vector then follow from the trivial actions, and the trace identity is scalar
multiplication with the Haar normalization absorbed into `C`.

## Sources and provenance

- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), Chapter 1, Lemma 6.5 and its proof (printed pp. 54–55).
  The lemma prescribes a discrete series with trivial central character at `v₀`, a
  supercuspidal at `v₁` and a Steinberg representation at `v₃`. Its proof uses local
  characters to get a nonzero elliptic orbital integral and isolates a single class with
  the test at `v₂` and the archimedean tests. [Chapter 1, pp. 54–55](https://www.claymath.org/library/cw/arthur/pdf/30.pdf#page=68)
- Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en caractéristique
  non nulle* (2011), II.6.7–II.6.9 (printed pp. 123–125). They choose the central-character
  data compatibly with the prescribed local discrete series, use a pseudo-coefficient and
  a level-zero elliptic test at a split place, then shrink a test at a further split place
  to isolate one rational orbit. The resulting cuspidal representation in their fixed
  central-character space has the prescribed local component at `v₀`.
  [Chapter II, pp. 123–125](https://numdam.org/item/10.24033/msmf.436.pdf#page=131)
- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Corollary 18.4.1
  (printed p. 485), gives the simple trace formula for a test on the quotient by the
  positive split center, with cuspidal image and elliptic semisimple rational classes.
  [Chapter 18, Simple Trace Formulae](https://link.springer.com/chapter/10.1007/978-3-031-41153-3_18)

The proposition is derived for the project's positive-central quotient and its varying
central characters. It combines the source method of selecting a summand by a nonzero
trace with simultaneous supercuspidal prescriptions and any one auxiliary finite place.
The local identification is expressed by the equivariant embedding and the conditional
compressed trace identity in part 3. These are the interfaces used for the global proof
of local cyclic base change.
