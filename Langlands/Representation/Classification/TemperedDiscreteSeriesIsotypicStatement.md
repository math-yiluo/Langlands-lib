# Discrete-series isotypic projectors in tempered Levi representations

`Langlands.GLTemperedDiscreteSeriesIsotypicStatement.{uF,uV,uW}` is a proposition
definition. It proves nothing and supplies no projector. It states a
lower-level step that is derived from, but not stated verbatim in, the proof of
Silberger 1979, Theorem 4.5.18. Fix a tempered representation `ρ` and an
irreducible square-integrable representation `σ` of an actual block Levi, both
with the same exact scalar central character. The step asserts that the
intrinsic `σ`-isotypic part of `ρ` is the range of an equivariant idempotent
whose kernel has no `σ`-subquotient.

## Exact statement and binders

The binders and their order are those of
`GLTemperedDiscreteSeriesJacquetQuotientStatement` in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md). The
proposition quantifies over every prime `p`, every `F : PadicField p`, its actual
topological data `T`, with topology `T.topology`, a positive rank `n` and a
standard block shape `B` of `n`. Put `M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F)`
with the proved instance `T.leviTopologicalGroup B`, and `Q = M / Z(M)`, the
quotient by the actual center `Subgroup.center M`. The proposition then
quantifies over every Borel measurable structure on `Q` and every Haar measure `μ` on it.

Next come two independent complex vector spaces, `V : Type uV` and
`W : Type uW`, and actual representations `ρ : Representation ℂ M V` and
`σ : Representation ℂ M W`. It also quantifies over actual unitary
central-character data `cρ : UnitaryCentralCharacter ρ` and
`cσ : UnitaryCentralCharacter σ`. The hypotheses are exactly

```text
IsTemperedModCenter ρ μ,
Representation.IsIrreducible σ, IsSquareIntegrableModCenter σ μ,
cρ.character = cσ.character.
```

The proposition first defines the isotypic subrepresentation intrinsically:

```lean
let I : Subrepresentation ρ := ⨆ f : σ.IntertwiningMap ρ, f.range
```

The supremum is taken in the complete lattice
`Langlands.Subrepresentation.instCompleteLattice` of
[SubrepresentationLattice](../SubrepresentationLattice.md). Its underlying
subspace is the span of the images of all intertwiners `σ → ρ`. Only after `I`
is defined does the conclusion assert

```lean
∃ P : ρ.IntertwiningMap ρ, P.comp P = P ∧ P.range = I ∧
  ∀ K : Subrepresentation P.ker.toRepresentation,
    ¬ ∃ q : K.toRepresentation.IntertwiningMap σ, Function.Surjective q
```

Thus `P` is an actual `M`-equivariant complex-linear idempotent on `V` whose
range is exactly `I`. Its kernel `P.ker` is the complementary invariant
subspace. The last clause states that no subrepresentation `K` of the kernel
has a surjective intertwiner onto `σ`. Equivalently, `σ` is no subquotient of
`P.ker`: a subquotient is a quotient of a subrepresentation. The witnesses `P`
and `q` are conclusions, not hypotheses or fields of a datum.

`ρ` is not assumed irreducible, unitarizable, semisimple, finitely generated or
of finite length. It is only admissible, which is part of `IsTemperedModCenter`. The
coefficients of `σ` are not assumed compactly supported modulo the center. No
projector, quotient map or decomposition is supplied as a hypothesis. The
universes `uF`, `uV` and `uW` are independent level parameters. Intertwiners
between `W` and `V` are allowed across different universes.

## Scalar-character and measure hypotheses

`UnitaryCentralCharacter` is the Library structure in
`Langlands.Representation.MatrixCoefficient.ModuloCenter`. Each datum is a
homomorphism `Z(M) →* ℂˣ` with open kernel and values of norm one. The center
acts by these scalars: `ρ z v = cρ.character z • v`, and similarly for `σ`. The
hypothesis `cρ.character = cσ.character` states that `ρ` and `σ` have the same
exact scalar central character `χ`. It is not a generalized-eigenspace
condition.

For `M = ∏ GL_(B.size i)(F)` the full center is the product of the scalar
subgroups `F^×`. This is the split component `A` of the center that
Silberger's integrals divide by. Hence Silberger's condition
`μ(a)w = χ(a)w (a ∈ A)` in the proof of Theorem 3.3.1 is exactly the stated
scalar action. Each analytic predicate contains its own existential unitary
central character. On a nonzero space the scalar action determines the
character, so these internal characters agree with `cρ` and `cσ`.

The same `μ` occurs in both analytic predicates and not in the conclusion.
Every choice is allowed, and the range is nonempty by
`T.exists_isHaarMeasure_leviCentralQuotient B` in
[TemperedInductionStatement](TemperedInductionStatement.md). Borel Haar measures
on this locally compact second-countable quotient differ by positive finite
scalars. Such a scalar changes no membership in `L²` or `L^(2+ε)`. Silberger's
measure `dx*` on `M/A` is one of these Haar measures.

## Original sources and provenance

The source is Allan J. Silberger, *Introduction to Harmonic Analysis on
Reductive p-adic Groups* (1979), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Its one-based PDF page is the printed page plus six. The passages below were
read in rendered page images. No errata note for this source was present in
the current Library.

| Source location | Use |
| --- | --- |
| Theorem 3.3.1, proof, pp.126–127 | For supercuspidal `ω` and an admissible `M`-module `(W, μ)` with `μ(a)w = χ(a)w` for `a ∈ A`, the coefficient space `𝒜(ω)` is a semisimple algebra under `φ * ψ(m) = ∫_(M/A) φ(x)ψ(x⁻¹m) dx*`. It acts by `μ(φ)w = ∫_(M/A) φ(x⁻¹)μ(x)w dx*`. Then `W` is the direct sum of the submodule annihilated by `𝒜(ω)` and finitely many simple `𝒜(ω)`-modules. Each simple module is an `M`-module of class `ω`. |
| Lemma 1.11.5, p.66 | An irreducible admissible representation receiving a nonzero `G`-map from a subspace of the coefficient space `𝒜(π)` of an irreducible admissible `π` is equivalent to `π`. This identifies the simple `𝒜(ω)`-modules above with copies of `ω`. |
| Theorem 4.5.10 (1)⇔(4), pp.188–189 | A coefficient with unitary central character `η` is square integrable on `G/Z` if and only if for every `r > 0` it is bounded by `c(r) Ξ(x)(1 + σ_*(x))^(-r)`. These Schwartz-type bounds apply to the coefficients of `σ`. |
| Remark before Lemma 4.5.16, p.191; proof of Lemma 4.5.16, p.192; Corollary 4.5.17, p.193 | The weakly tempered functions form a double module over the Schwartz algebra. The coefficient space of any admissible tempered representation is a submodule, and convolution preserves each finite-dimensional `K₀`-level. The estimate on p.192 bounds a Schwartz function convolved with a weakly tempered function by `∫ Ξ(x)²(1 + σ(x))^(d-r) dx`, which is finite for large `r`. |
| Theorem 4.5.18 and its proof, p.193 | For irreducible tempered `π` and `σ ∈ ω ∈ ℰ₂(M)`, the proof is that of Theorem 3.3.1, except that one must assume the auxiliary module `(W, μ)` is tempered. |

The proposition is a derived specialization of this route. Silberger applies
the decomposition to an auxiliary admissible module with exact character `χ`,
not to an arbitrary named representation. He states it only inside the proofs
of Theorems 3.3.1 and 4.5.18. Here `(W, μ)` becomes the representation `ρ`, and
`ω` becomes the class of `σ`. The group is specialized to the product Levi of
`GL_n`. The direct-sum statement becomes an idempotent intertwiner with range
`I` and kernel the annihilated part. The finiteness of the number of simple
summands, which Silberger obtains from admissibility, is not part of the Lean
conclusion.

## Coefficient-algebra route behind the formulation

This section explains why the formulation is the right extraction. It is
neither a proof nor a claim that a proof exists in the Library.

1. By Theorem 4.5.10 the coefficients of `σ` satisfy Schwartz bounds modulo
   the center. Under convolution on `M/Z(M)`, the coefficient space `𝒜(σ)`
   plays the role of the semisimple algebra `𝒜(ω)` in the proof of
   Theorem 3.3.1, as the proof of Theorem 4.5.18 requires. Closure under
   convolution comes from the Schur orthogonality relations for
   square-integrable representations with the formal degree. These are
   relations (2)–(3) of Waldspurger, p.265, cited below.
2. For `φ ∈ 𝒜(σ)` and `v ∈ V`, the integrand `x ↦ φ(x⁻¹) ρ(x) v` is invariant
   under `x ↦ xz` for central `z` exactly because `ρ` and `σ` have the same
   scalar character. This is the role of `cρ.character = cσ.character`.
   Pairing with smooth functionals gives integrals of a Schwartz function
   against weakly tempered coefficients of `ρ`. These converge absolutely by
   the type of estimate used on p.192. Each `φ` is bi-invariant under some compact open `K₀`,
   and `V^(K₀)` is finite-dimensional by admissibility. So the weak integral
   defines `ρ(φ)v ∈ V^(K₀)`. This is where temperedness of `ρ` is used, as the
   4.5.18 proof requires.
3. On each `V^(K₀)` the finite-dimensional semisimple algebra of
   `K₀`-bi-invariant elements of `𝒜(σ)` acts. The space splits into its
   annihilator and a nondegenerate part. The units of these finite-level
   algebras are compatible and assemble to an `M`-equivariant idempotent `P`.
4. The nondegenerate part is a sum of copies of `σ` by Lemma 1.11.5, so it lies
   in `I`. Conversely an intertwiner `f : σ → ρ` commutes with the action, and
   `σ` is nondegenerate, so `f.range` lies in the range of `P`. Hence
   `P.range = I`.
5. Let `K` lie in the kernel of `P` and let `q : K → σ` be a surjective
   intertwiner. Then `q(ρ(φ)k) = σ(φ)q(k)`, where the left side vanishes
   because `𝒜(σ)` annihilates the kernel. This would make `σ` degenerate.
   Hence the kernel has no `σ`-subquotient.

## Analytic convention bridge

Silberger's temperedness is the weak coefficient inequality
`|c(x)| ≤ C Ξ(x)(1 + σ(x))^r` (Theorem 4.5.1 and the following definition,
pp.183–184). The Library predicate `IsTemperedModCenter` instead requires every
coefficient norm to lie in `L^(2+ε)(Q, μ)` for every `ε > 0`.
`IsSquareIntegrableModCenter` requires `L²(Q, μ)`, which is Silberger's
condition (1) of Theorem 4.5.10 on `M/A`. For the product Levi, the passage
from `L^(2+ε)` to the weak inequality is the derived argument documented in
[TemperedInductionStatement](TemperedInductionStatement.md), under “Analytic
convention correspondence”. It is also used in
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md). Its inputs
are the Cartan double-coset volume, the `Ξ` bound and the Jacquet coefficient
asymptotic, which feed the exponent criterion. They are taken from
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques d’après
Harish-Chandra* (2003), registered as `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:
I.1(5), p.241; Theorem I.4.1, p.245; Lemma II.1.1, p.251; and §III.2 with
Proposition III.2.2, pp.265–266. The orthogonality relations (2)–(3) at the end
of §III.1, p.265, are the ones used in step 1 above. The one-based PDF page is
the printed page minus 234. No errata note for this source was present in the
current Library.

Here `ρ` need not be finitely generated, but both temperedness conditions are
conditions on individual coefficients. A coefficient `x ↦ ℓ(ρ(x)v)` is a
coefficient of the finitely generated admissible subrepresentation generated by
`v`, restricted to that subrepresentation. Admissibility lets every smooth
functional on that subrepresentation extend to `V`. So the bridge is applied
coefficientwise, to finitely generated admissible pieces. It is a documented
mathematical derivation, not a Lean proof.

## Boundary from compact-coefficient projectors

[CompactCoefficient.ProjectorStatement](../CompactCoefficient/ProjectorStatement.md)
states Bernstein–Zelevinsky (1976), §§2.42–2.44: natural projectors onto
compact-isotypic parts of arbitrary smooth representations. Its proof module is
not used or duplicated here. Those projectors are indexed by irreducible
representations satisfying `HasCompactSmoothDualCoefficients`, whose
coefficients are compactly supported on the group itself. Their coefficient
algebra acts on every smooth representation without analytic hypotheses. Here
`Z(M)` is noncompact and acts on `σ` by a unitary character. So the nonzero
coefficients of `σ` never have compact support, and even supercuspidal
coefficients are compactly supported only modulo the center. A discrete
series has coefficients only of Schwartz type modulo the center. Their
integrals converge only against weakly tempered coefficients with the
matching central character. The present proposition therefore assumes
temperedness of `ρ` and the same scalar central character instead. It neither
assumes nor implies the compact-coefficient premise for `σ`, and adds no new
coefficient-class quotient or analytic algebra to the Library.

## Scope

The proposition asserts no converse, and no semisimplicity of `ρ` or of its
`σ`-isotypic part. It claims no finiteness of multiplicity, uniqueness or
naturality of `P`, or orthogonality between projectors for different `σ`. It is
a prerequisite for, not a proof of, the opposite Jacquet quotient criterion
`GLTemperedDiscreteSeriesJacquetQuotientStatement`. No support, head, summand or
exhaustion statement is used to justify it.
