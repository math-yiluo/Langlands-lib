# Closed additive subgroups in actual polynomial kernels

Author: Worker 864.

This derived geometric adapter implements a consequence of Conrad–Gabber–Prasad,
*Pseudo-reductive Groups*, second edition (2015), Lemmas B.1.7–B.1.9,
printed pp.563–565, one-based PDF pp.589–591. The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
In B.1.7(3), a coordinate factor in a transformed kernel gives a closed
additive subgroup and a homomorphic retraction. Here the imported polynomial
section and retraction identities give that consequence directly, without
constructing a full change of vector coordinates. The actual morphisms and
their closedness are the new content.

Let `k : Type u` be any field and `n : ℕ`. Write `V_n` for the actual standard
group scheme `VectorGroup.groupScheme (CommRingCat.of k) n`. Polynomial
additivity means the existing two-variable polynomial identity
`OneDimensional.IsAdditive`, rather than a condition only on `k`-points.
There is no perfectness, infinitude, characteristic or positive-dimension
hypothesis.

For an additive tuple `ψ : Fin n → k[X]`, `polynomialCurvePoints` acts on
points of every relative scheme `T` over `Spec k`. If the coordinate of a
`V_1`-point is `x ∈ Γ(T, ⊤)`, its image has coordinates
`(ψ i).eval₂ (AdditiveGroupQuotient.structureMap T) x`. The structure map is
the canonical map from `k` to global functions. The auxiliary lemma
`OneDimensional.IsAdditive.eval₂_add` evaluates polynomial additivity along
any coefficient homomorphism, by using the algebra structure it induces.
Together with zero constant coefficient, this makes the point map a group
homomorphism, with the additive groups written multiplicatively.

For an additive row `f : Fin n → k[X]`, `polynomialRowPoints` sends a tuple
`x` of global sections to the one coordinate
`∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap T) (x i)`.
The coordinate lemmas state these evaluation formulas exactly. The
naturality proofs use compatibility of the structure map with pullback of
global functions and compatibility of polynomial evaluation with ring maps.
No affineness or reducedness hypothesis on the test scheme is used.

`polynomialCurve` and `polynomialRow` are the actual group-scheme morphisms
recovered from these natural homomorphisms by the existing fully faithful
point-functor construction `homOfPoints`. Their composition lemmas identify
the induced maps on every relative scheme test with the formulas above.

Suppose `ψ` and `r` are additive and satisfy

`∑ i, (r i).comp (ψ i) = X`.

Then `polynomialCurve_comp_polynomialRow_eq_id` proves that the actual
curve followed by the actual row is the identity of `V_1`. The proof checks
every test point and its sole coordinate, uses the imported evaluation
identity `sum_aeval_aeval`, and evaluates `X` to that coordinate.
`polynomialCurve_isClosedSubgroup` uses this homomorphic retraction and
the affineness of `V_n`. A section of a separated morphism is a closed
immersion; the imported `LinearKernelTower.isClosedSubgroup_of_section`
provides that geometric argument. The conclusion is the existing predicate
`IsClosedSubgroup` on the actual morphism.

If an additive row `f` also satisfies

`∑ i, (f i).comp (ψ i) = 0`,

then `polynomialCurve_comp_polynomialRow_eq_zero` proves that the actual
composite is the trivial group homomorphism. Its proof evaluates the
polynomial kernel identity on every test, including tests with nilpotents.
The principal construction `polynomialKernelCurve` factors this curve into
the actual categorical kernel `kernel (polynomialRow f hf)`, defined by
pullback with the unit. The inclusion identity
`polynomialKernelCurve_comp_ι` recovers the original ambient curve.

`polynomialKernelCurve_comp_retraction` restricts the ambient row `r` to
the kernel and proves it is a homomorphic left inverse to the factored
curve. `polynomialKernelCurve_isClosedSubgroup` proves closedness into
the kernel: its composite with the kernel inclusion is the already closed
ambient curve, and the kernel inclusion is separated (indeed a closed
immersion). The standard closed-immersion cancellation lemma applies.
No assertion that this kernel is smooth is needed.

`HasSplitAdditiveKernelCurve.exists_closed_kernel_section` packages a
closed immersion `s : V_1 ⟶ kernel (polynomialRow f hf)` and a homomorphism
back to `V_1` with composite `s ≫ r = 𝟙 _`. The two corollaries
`exists_closed_kernel_section_of_nonconstant` and
`exists_closed_kernel_section_of_nonconstant_galois` supply the required
polynomial section and retraction from the imported degree-induction and
Galois-descent results. The former accepts a polynomial tuple with a
positive-degree coordinate satisfying the kernel identity over `k`.
The latter accepts such a tuple over any algebraic Galois extension `K/k`
and constructs the actual subgroup and retraction over `k`. The extension
field can have an independent universe and need not have finite degree.

These are derived consequences of B.1.7–B.1.9 with an explicit retraction.
Although Appendix B assumes positive characteristic, the imported polynomial
results cover characteristic zero via exponential characteristic one, so
the actual constructions here cover every field. The empty-dimensional
case causes no exception: the split or nonconstant polynomial input is then
impossible.

This unit constructs maps of actual group schemes from polynomial tuples.
It does not extract polynomials from an arbitrary affine-line morphism,
construct a full vector-coordinate isomorphism, supply embeddings or
vector-factor decompositions for arbitrary unipotent groups, or prove the
full woundness criterion. Those remain separate obligations.
