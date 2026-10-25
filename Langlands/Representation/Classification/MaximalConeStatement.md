# Dominance-maximal selection of an essentially tempered Jacquet quotient

Author of the correction and independent source checks: Worker 436.
Original statement and documentation: Worker 19.
Counterexample, dominance correction and quotient-route reports: Worker 23.

`Langlands.GLMaximalConeJacquetQuotientStatement` is a derived proposition
definition, not a proved theorem. It selects an actual dual exponent, a
consecutive cone coarsening and an irreducible admissible quotient of the
**whole** normalized opposite Jacquet module. Removing the real determinant
character makes that quotient analytically tempered. Its final clause now
excludes a strictly dominating positive part. The former maximum-number-of-
blocks clause, transcribed from Silberger (1978), Proposition 7.2, was false
with these conclusions. The independently checked obstruction is below.
Konno (2003), Sections 3.2–3.3, supplies the dominance argument; the full
competitor class and the quotient orientation are derived extensions explained
here, rather than assertions that Konno states this exact proposition.

## Quantifiers and retained objects

The field and carrier universes `uF` and `uV` are independent. For every prime
`p`, finite extension `F` of `Q_p` with compatible topological data `T`,
positive rank `n`, and complex representation `A : Rep.{uV} ℂ (GL_n(F))`,
the hypotheses are irreducibility and admissibility. Admissibility includes
smoothness; irreducibility includes nontriviality. No unitarity, finite
representation dimension, selection certificate or known quotient is an input.

The witnesses are positive ordered block shapes `B,C` of total rank `n`,
characters `χ,χC` of their actual block-scalar tori, scalar real parts `r`,
a grouping `q`, determinant exponents `t`, and a representation `S` of the
actual product Levi `C.Levi F.Carrier`. Its existential carrier is in
`Type uV`, as is appropriate for a quotient of a quotient of `A`. It need not
be the carrier of `A`. No tensor factorization of `S` is required.

`T.IsDualJacquetExponent B A χ` means that `χ` has open kernel and has a
nonzero eigenfunctional in the full algebraic transpose dual of the actual
normalized opposite Jacquet module. On the commutative scalar torus this is

```text
f(a.v) = χ(a) f(v).
```

There is **no inversion of χ**. This follows directly from
`commutativeTranspose_apply` and `splitCentreDualJacquet_apply` in the imported
`Exponents/DualJacquet` module. This full transpose is distinct from the usual
smooth contragredient with its inverse-element action.

`T.IsRealPartOf χ r` says, for every tuple `a` of nonzero field elements,

```text
||χ(a)|| = product_i |a_i|^(r_i),     |x| = q_F^(-ord_F(x)).
```

Here `r_i` is a scalar exponent. A determinant twist `|det_i|^(t_i)` on a
block of size `n_i` has scalar exponent `n_i t_i`.

## Cone data and exact dominance comparison

The five numerical requirements of `GLParabolicRootWeightConeStatement`
remain explicit:

- `q` is monotone and surjective, hence groups nonempty consecutive runs.
- `C.size j` is the sum of `B.size i` over the fiber of `j`.
- `t` is strictly decreasing.
- Each fiber has total scalar exponent `(C.size j) t_j`.
- Every prefix inside a fiber has nonpositive sum of
  `r_i - (B.size i) t_(q i)`.

The actual upper matrix parabolic and embedded Levi for `B` are contained
in those for `C`. Character restriction is the pointwise equation
`χC(a) = χ(a ∘ q)`. Occurrence at `C` and the real-part equality
`j ↦ (C.size j) t_j` are conclusions, not definitions of restriction.

The auxiliary **Prop-valued definition**
`GLBlockPositivePartStrictlyDominates C₁ t₁ C₂ t₂` uses the length-`n` vectors

```text
Λ₁(i) = t₁((C₁.indexEquiv.symm i).1),
Λ₂(i) = t₂((C₂.indexEquiv.symm i).1).
```

`indexEquiv` numbers consecutive blocks in their original order. Thus `Λ`
repeats `t_j` exactly `C.size j` times. Write
`L(k) = sum_{0 ≤ i < k} Λ(i)`. The first positive part strictly dominates
the second exactly when

```text
L₁(n) = L₂(n),
L₁(k) ≥ L₂(k) for every k = 0,...,n,
L₁(k) > L₂(k) for at least one such k.
```

Lean uses `k : Fin (n+1)` and filters `i : Fin n` by `i.val < k.val`.
Both endpoints are included: `L(0)=0`, and the last prefix is the total
central value. Strict inequality can therefore occur only at an interior
prefix. Equal positive parts do not strictly dominate one another, even if
presented by different data.

The last clause of the main statement quantifies over **every** actual dual
exponent of `A`, on every standard shape `B'`, and every real part and
numerical consecutive coarsening `q',C',t'` satisfying the same five clauses.
It concludes `¬ GLBlockPositivePartStrictlyDominates C' t' C t`.
There is no restriction to refinements of the chosen `B` or `C`, and no
quotient, temperedness or coarser-occurrence premise on a competitor.
This is maximality: no competitor strictly dominates the selected positive
part. It does not assert a greatest element, comparability of all competitors,
uniqueness or maximum block count.

## Match with Konno and the full-spectrum extension

K03 Section 2.1, pp.384–385, separates the central direction; Section 2.2,
pp.386–387, fixes roots, coroots and fundamental coweights. Section 3.2,
p.394, defines `λ ≤_P μ` by `μ-λ` belonging to the closed positive root cone
in the part annihilating the ambient center. For the upper Borel of `GL_n`,
the simple roots are `e_i-e_(i+1)`. A vector `d` is in that cone precisely
when its total is zero and all its proper prefix sums are nonnegative:

```text
d = sum_{k=1}^{n-1} (sum_{i<k} d_i) (e_(k-1)-e_k).
```

Equivalently, pairing with the `k`th fundamental coweight gives
`sum_{i<k} d_i - (k/n) sum_i d_i`. The central term vanishes for equal
totals. This proves the sign and orientation of the comparison used here.
The embedding of a Levi determinant parameter into Borel coordinates
repeats it with block-size multiplicity, exactly as in the auxiliary
definition. Projection to a coarser Levi takes weighted averages. K03
Lemma 3.3, pp.394–395, is consequently the stated cone decomposition;
Lemma 3.4, pp.395–396, says positive parts preserve dominance.

K03 Theorem 3.5(i), pp.396–397, selects a maximal positive part among
exponents at standard parabolics realizing the cuspidal support. It then
selects a **subrepresentation** of a weak character component of the
opposite Jacquet module. The present full-spectrum quotient variant follows
by the following derived argument; it does not silently identify that
subrepresentation with a quotient.

First, there are finitely many standard shapes and finitely many exponents
at each shape. Jacquet admissibility and finite generation, together with
central local finiteness and its generalized-character decomposition, give
this finiteness (C95 Propositions 2.1.3, 2.1.9 and Theorem 3.3.1). Real parts
are unique, as can be tested on a uniformizer in each coordinate. There
are finitely many groupings, so the full set of candidate positive parts is
finite and has a maximal element. It is nonempty, since the ambient scalar
central character supplies the one-block case. These are proof obligations,
not premises added to the Lean proposition.

For a numerical exponent at `B`, restriction to the scalar torus of `C`
occurs on the whole Jacquet module at `C`: use normalized Jacquet
transitivity and pull its eigenfunctional back along the further Jacquet
projection. The factors of the normalizing characters multiply, so this
introduces no sign change. The quotient extraction below then supplies `S`.

To check temperedness of `τ = |det|^(-t) S`, take any standard parabolic
inside the product Levi of `C`, with flattened finer shape `D`. Its Jacquet
module is a quotient of the corresponding finer Jacquet module of `A`:
Jacquet functors preserve surjections, and normalized transitivity identifies
the latter. A nonzero transpose eigenfunctional pulls back injectively along
a surjection. Hence every exponent of that Jacquet module of `S` is an
actual competitor exponent of `A` at `D`. This is a concrete map argument,
not an exchange between subrepresentations and quotients.

Let `H` be the polygon of cumulative scalar real parts of this finer
exponent before untwisting, with knots at the `D` boundaries. Its values
at the `C` boundaries equal those of the selected polygon `L`, because
`S` has scalar character `χC`. The numerical cone positive part `L'` is
the least concave majorant of `H`: its slopes strictly decrease, it meets
`H` at its coarse boundaries, and the residual-prefix inequalities place
`H` below each coarse chord. This is the GL-coordinate interpretation of
K03 Lemmas 3.3–3.4. Since `L'` is concave and is at least `L` at every
`C` boundary, it is at least the straight chord `L` between those boundaries.
Its total is the same. If any within-block prefix of the untwisted exponent
were positive, then `H(k)>L(k)` there and therefore `L'(k)>L(k)`.
That would give a strictly dominating competitor, a contradiction.

Thus every opposite Jacquet exponent of `τ` has nonpositive within-block
prefixes and zero block totals. These are the weak tempered bounds for the
opposite convention. K03 Section 2.4, p.390, or W03 Proposition III.2.2,
pp.265–266, applied to the product Levi gives temperedness. This argument
uses all standard refinements, so no restriction to cuspidal-support
parabolics is needed. It justifies keeping the original full competitor
class. The analytic translation to the Library predicate is detailed below.

## Extracting a quotient of the whole module and map directions

Set `V = oppositeJacquet(T,C,A)`. A dual exponent gives a nonzero linear
functional `f : V → ℂ` with `f(a.v)=χC(a) f(v)`. Define

```text
W = {v in V | f(m.v)=0 for every m in M_C}.
```

This is an `M_C`-stable subspace and is proper, since `W` is contained in
`ker f`. Since the block scalars are central, for every scalar `a`, every
`m` and every `v` one has

```text
f(m.(a.v - χC(a) v)) = f(a.(m.v)) - χC(a) f(m.v) = 0.
```

Consequently `V/W` is nonzero with scalar character `χC`. It is smooth,
admissible and finitely generated as a quotient of `V` (C95
Proposition 2.1.8 and Theorem 3.3.1). A nonzero finitely generated module
has an irreducible quotient: the union of a chain of proper submodules is
proper because there are finitely many generators, so Zorn's lemma gives
a maximal submodule. Its quotient `S` is admissible and inherits the scalar
character. The composite **surjection `V → V/W → S` has domain the whole
Jacquet module**. No smoothness of the algebraic functional is required.
This extraction is a derived elementary argument, not a theorem printed in
K03. Alternatively, central local finiteness splits off the generalized
`χC` component, and an irreducible quotient of that summand is a quotient
of `V`. Neither route claims every subquotient of `V` is its quotient.

The opposite construction quotients by the actual lower block unipotent
radical. Its normalization is the positive upper half modulus
`δ_P^(1/2)`, equivalently the inverse half modulus of the lower parabolic.
With the Library's right-translation induction and covariance convention,
first adjointness gives

```text
Hom_M(r_(Pbar) A, S) = Hom_G(A, i_(Pbar) S).
```

The nonzero map therefore embeds irreducible `A` into **opposite normalized
induction**. It does not by itself give a surjection from upper induction.
K03 p.396 instead starts with `S ↪ r_(Pbar) A` and uses smooth duality,
`(r_P A^∨)^∨ = r_(Pbar) A`, then first adjointness to obtain
`i_P S → A`. A second-adjointness or equivalent duality bridge is needed
for that direction. This proposition asserts the Jacquet surjection only;
it asserts neither reciprocity nor a surjection from upper induction.

## Independent check of the reported GL4 obstruction

The initial example and map audit were reported by Worker 23. Worker 19
had checked only the finite rational cone enumeration for two reported
Borel words. For this correction Worker 436 independently checked the
representation arguments against Z80 and K03, and recomputed the numerical
cases from geometric-lemma matrices, rather than assuming the reported
spectrum. These are mathematical source checks and finite rational
computations, **not Lean proofs** of a counterexample or of classification.

Write `ν^s=|det|^s`, `a=1/2`, `Δ=[ν^(-a),ν^a]` and
`A=1_(GL2) × 1_(GL2)`, where `×` is normalized upper induction over `Q_p`.
In Z80 Sections 3.1–3.2, `Z(Δ)=<Δ>` is the trivial representation;
Sections 9.1–9.2 give the other orientation `T(Δ)=<Δ>ᵗ=St₂`.
The identical segments `Δ,Δ` are unlinked, so Z80 Theorem 4.2 proves
`A` irreducible; its admissibility follows from parabolic induction of
admissible representations (K03 Section 2.4). This avoids relying on an
unspecified unitary-induction irreducibility theorem.

For a target shape `D`, the geometric lemma (Z80 Sections 1.2 and 1.6)
is indexed by nonnegative two-row matrices `(b_ij)` with row sums `2,2`
and column sums `D.size j`. A cell in a source trivial `GL₂` has opposite
normalized determinant exponent
`(sum_{k>j} b_ik - sum_{k<j} b_ik)/2`. Thus its target column has scalar
exponent

```text
r_j = sum_i b_ij (sum_{k>j} b_ik - sum_{k<j} b_ik)/2.
```

This follows as well from `r_B(1_GL2)=δ_B^(-1/2)` and conjugating upper to
lower Jacquet. In particular the opposite scalar word is `(a,-a)`, with
no inversion caused by taking the Library's transpose dual. Every Bruhat
piece has the indicated scalar character. Finite generalized-character
decomposition shows these are exactly the actual dual characters, including
when the filtration is not split. For the Borel the two words are
`(a,-a,a,-a)` with multiplicity two and `(a,a,-a,-a)` with multiplicity four.
All characters here are unramified; no extra unitary phases occur.

The complete list of scalar real parts and numerical cones is below.
For each row, all consecutive groupings were tested using exact rational
fiber averages and residual prefixes; the displayed cone is the only one
satisfying the five clauses. The two-row formula establishes that no
additional shape or actual exponent is missing.

| Original shape `D` | Scalar real part `r` | Coarse shape `C`; determinant exponents `t` |
| --- | --- | --- |
| `(4)` | `(0)` | `(4)`; `(0)` |
| `(1,3)` | `(a,-a)` | `(1,3)`; `(a,-1/6)` |
| `(2,2)` | `(0,0)` | `(4)`; `(0)` |
| `(2,2)` | `(1,-1)` | `(2,2)`; `(a,-a)` |
| `(1,1,2)` | `(a,-a,0)` | `(1,3)`; `(a,-1/6)` |
| `(1,1,2)` | `(a,a,-1)` | `(2,2)`; `(a,-a)` |
| `(3,1)` | `(a,-a)` | `(3,1)`; `(1/6,-a)` |
| `(1,2,1)` | `(a,0,-a)` | `(1,2,1)`; `(a,0,-a)` |
| `(2,1,1)` | `(0,a,-a)` | `(3,1)`; `(1/6,-a)` |
| `(2,1,1)` | `(1,-a,-a)` | `(2,2)`; `(a,-a)` |
| `(1,1,1,1)` | `(a,-a,a,-a)` | `(1,2,1)`; `(a,0,-a)` |
| `(1,1,1,1)` | `(a,a,-a,-a)` | `(2,2)`; `(a,-a)` |

Maximum block count is therefore three, forcing `C=(1,2,1)` and
`t=(a,0,-a)`. Any irreducible constituent with the required scalar character
has the form `ν^a ⊗ S₂ ⊗ ν^(-a)`. Cuspidal support of the geometric-lemma
terms forces `S₂` to have support `{ν^(-a),ν^a}`. The length-two principal
series has exactly the constituents `1_GL2` and `St₂` (Z80 Proposition 4.6
and Sections 3.2, 9.1–9.2). The trivial middle factor is not tempered:
its opposite exponent `(a,-a)` violates the weak bound. Hence the demanded
tempered quotient would have to be
`S=ν^a ⊗ St₂ ⊗ ν^(-a)`.

A whole opposite-Jacquet quotient onto this `S` would, by first adjointness
and reversal of the three blocks, embed

```text
A ↪ ν^(-a) × St₂ × ν^a.
```

Induction in stages and first adjointness would then give a nonzero map

```text
r_(1,3)(A) → ν^(-a) ⊗ (St₂ × ν^a),
```

where this `r_(1,3)` is the **upper** normalized Jacquet functor. Its
geometric-lemma filtration has two factors, both
`ν^(-a) ⊗ R`, with `R=1_GL2 × ν^a`: the two matrices have first columns
`(1,0)` and `(0,1)`. The column of rank three gives respectively
`ν^a × 1_GL2` and `1_GL2 × ν^a`, which are the same irreducible `R`.
The singleton segment `{ν^a}` is contained in `Δ`, so it is unlinked
with `Δ`. Z80 Theorems 4.2 and 9.7 prove both `R` and
`T=St₂ × ν^a` irreducible. Their upper Borel Jacquet words distinguish them:

```text
R: (-a,a,a) twice, (a,-a,a) once;
T: ( a,a,-a) twice, (a,-a,a) once.
```

These follow by shuffling the upper words `(-a,a)` and `(a,-a)` with
`(a)`. Thus `R` and `T` are inequivalent. No factor of the finite filtration
of `r_(1,3)(A)` is the proposed irreducible target, so its Hom space to
`ν^(-a) ⊗ T` is zero. This proves the reported whole-quotient obstruction.
It does not assume that an arbitrary middle subquotient lifts to a quotient.
The same obstruction excludes the subrepresentation variant: dualize a
putative `i_P(S) → A`, using `A^∨=A` and `St₂^∨=St₂`, to obtain the same
impossible embedding. The failure therefore cannot be repaired just by
swapping the Jacquet map direction.

The two-block positive part has prefix polygon `(0,a,1,a,0)`, strictly
above the length-maximal polygon `(0,a,a,a,0)`. It is the unique maximal
polygon among the listed cases. Its scalar-character component in
`r_(Pbar_(2,2))(A)` is the single irreducible

```text
(ν^a × ν^a) ⊗ (ν^(-a) × ν^(-a)).
```

The other two Bruhat pieces have scalar real part `(0,0)`, so the component
is a direct summand and supplies an actual whole-module quotient.
Untwisting leaves `(1 × 1) ⊗ (1 × 1)`, which is tempered by tempered
induction (W03 Lemma III.2.3). This illustrates the corrected selection.

## Analytic temperedness and arbitrary central twists

The retained conclusion quantifies over **every** Borel measurable-space
structure and Haar measure on
`C.Levi F.Carrier / Subgroup.center (C.Levi F.Carrier)`, and asserts
`IsTemperedModCenter (T.leviRealPowerTwist C (-t) S.ρ) μ`.
The twist is the actual character `product_j |det m_j|^(-t_j)` on the same
carrier. Its block-scalar exponents are `-(C.size j) t_j`, so it removes
the real part of `χC` exactly. Its open kernel and preservation of smoothness
are proved in `Twist/LeviRealPower`.

`IsTemperedModCenter` includes admissibility, a scalar unitary central
character and `L^(2+ε)` membership of every smooth matrix coefficient for
every real `ε>0`. The full center of this positive-rank product Levi is
the block-scalar torus. Haar quantification is nonvacuous:
`T.exists_isHaarMeasure_leviCentralQuotient` supplies a Borel Haar measure.

The analytic predicate is a derived translation of the weak exponent
criterion. W03 Section III.2 bounds every coefficient by
`C Ξ(g)(1+length(g))^d`; I.1(5) and Lemma II.1.1 compare Cartan volumes to
`δ_0^(-1)` and bound `Ξ` by `δ_0^(1/2)` times a polynomial. Modulo the
center, the `2+ε` integral is bounded by a chamber lattice sum of
`δ_0^(ε/2)` times a polynomial, which converges. Central unitarity makes the
absolute coefficient descend. Products have product Cartan estimates;
no chosen tensor factorization of `S` is needed. Haar measures differ by a
positive constant, so the result holds for every measure in the statement.
The cited exponent and analytic implications remain unformalized here.

The ambient central character fixes the common total
`sum_j (C.size j) t_j` for all candidates. If a real ambient determinant
twist has exponent `c`, then removing it replaces `r_i` by `r_i-n_i c`,
`t_j` by `t_j-c`, and `L(k)` by `L(k)-k c`. Fiber residuals, strict
adjacent differences and differences between candidate polygons are
unchanged. Equality of total central values is preserved. No total-zero,
individual-positivity or unitary-central-character hypothesis on `A` is
introduced. With `c` equal to its total scalar real part divided by positive
`n`, the usual center-zero normalization is recovered. The one-block case
has vacuous strict decrease and includes arbitrary essentially tempered
central twists.

## Originals, provenance and remaining proof obligations

All citations below refer to retained originals, not peer reports. The
supplied S78 and K03 fingerprints and the remaining PDF fingerprints were
checked against the retained bytes. No `notes/errata/` entries for these
sources were present in the Library used for this correction.

| Key and registered source ID | Retained PDF SHA256 | Locations used |
| --- | --- | --- |
| S78: A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978), `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354` | `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5` | Lemma 7.1, p.103; proof of Proposition 7.2, p.104. PDF page 1 is printed p.95. |
| K03: T. Konno, *A note on the Langlands classification and irreducibility of induced representations of p-adic groups* (2003), `konno-2003-langlands-classification` | `71931493382f2c8aa60734e27328db9a0f39c3af0b9c47bf746adcfa47fc0b42` | Sections 2–3, pp.384–397; especially order p.394, Lemmas 3.3–3.4, pp.394–396, Theorem 3.5(i), pp.396–397. PDF page 1 is printed p.383. |
| Z80: A. V. Zelevinsky, *Induced representations of reductive p-adic groups II* (1980), `zelevinsky-1980-induced-ii` | `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | Sections 1.1–1.6, pp.170–172; Sections 3.1–3.4, pp.180–182; Sections 4.1–4.2 and Proposition 4.6, pp.184–186; Sections 9.1–9.7, pp.197–199. |
| C95: W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive groups*, draft 1 May 1995, `casselman-1995-admissible-representations` | `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a` | Propositions 2.1.3, 2.1.8–2.1.9, pp.19–21; Proposition 3.2.3 and Theorem 3.2.4, p.34; Theorem 3.3.1, p.35. |
| S79: A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic groups* (1979), `silberger-1979-harmonic-analysis` | `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc` | Theorem 4.5.1, tempered definition and Lemma 4.5.3, pp.183–186. PDF page = printed page + 6. |
| W03: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d’après Harish-Chandra* (2003), `waldspurger-2003-plancherel` | `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7` | I.1(5), p.241; I.4.1, p.245; Lemmas II.1.1 and II.1.5, pp.251–252; Section III.2 and Proposition III.2.2, pp.265–266; Lemma III.2.3, p.266. PDF page = printed page − 234. |

S78 supplies the historical cone and whole-quotient motivation. Its p.104
step identifying finer positive supports solely from maximal cardinality
does not justify the required bounds; the GL4 calculation above refutes
that selection assertion. The old statement's publication is not proof of
it. This is a project correction, not an author-issued erratum. K03's
separate introductory criticism of S78 Lemma 5.3 is not evidence for this
new cardinality defect. The corrected proposition uses K03's dominance
geometry, the explicit full-spectrum polygon argument and the independent
whole-quotient extraction above.

The original author had read S78 in full and the cited earlier exponent
and analytic passages for related families. For this correction Worker 436
read S78 pp.103–104, K03 Sections 2–3, the listed Z80 and C95 passages and
the listed S79/W03 analytic passages; the order, selection and relevant
segment formulas were also checked in page images. No fresh full reading
of all six works or every transitive original proof source is claimed.
C95 is not the older Casselman preprint cited in S78; the retained Langlands
retypesetting discussed in `ParabolicConeStatement.md` is likewise not
identified with S78's original IAS preprint.

Future Lean proofs must construct finite spectra, the numerical cone and
its order compatibility, restriction occurrence, the whole Jacquet
surjection, normalized relative Jacquet transitivity, finer exponent
lifting and the analytic bridge. No such result is assumed as a certificate
or proved by this proposition definition. Deriving a final quotient from
upper induction additionally needs the correct adjointness/duality and
regular-head arguments. Other statement families, the public source map
and the downstream proof task are outside this correction pair.
