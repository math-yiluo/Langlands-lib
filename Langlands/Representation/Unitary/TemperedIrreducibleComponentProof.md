# Proof of the irreducible tempered component theorem

The theorem `Langlands.Analysis.temperedIrreducibleComponent` proves the proposition
`Langlands.Analysis.TemperedIrreducibleComponentStatement` (module
`Langlands.Representation.Unitary.TemperedIrreducibleComponentStatement`): for a unitary jointly
continuous representation `π` of a second countable locally compact group `G` on `H`, a nonzero
closed invariant subspace `H₀`, a jointly continuous `π_W` on `W` and an injective equivariant
bounded `j : H → W` with `j ∘ π(φ)` Hilbert–Schmidt for every test function `φ`, and a countable
family `Φ` of test functions, there is an irreducible unitary tempered component `(V, σ, D, J)` as
the statement describes. The module also contains two auxiliary lemmas,
`TemperedComponent.eq_zero_of_hilbertBasis` (a bounded operator vanishing on a Hilbert basis is
zero) and `TemperedComponent.wSub_invariant` (the closure of `j(H₀)` is `π_W`-invariant).

## Route

The statement's Markdown sketches a proof by a direct-integral decomposition of a cyclic
subrepresentation into irreducibles (Folland, Theorems 7.29 and 7.30(b)) and Bernstein's
Gelfand–Kostyuchenko theorem. Mathlib has neither direct integrals nor the spectral theorem for
commutative von Neumann algebras, and the proof here takes a different route: instead of
decomposing, it produces one irreducible component as an extreme point of a compact convex set,
in the way extreme points of the functions of positive type give irreducible representations
(G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press 2015, registered as
`folland-2015-abstract-harmonic-analysis-second`, §3.3: Theorem 3.25 on printed p.86 and the
Krein–Milman argument on printed pp.87–88). The points of the set are
operator-valued positive kernels `F (k, k', a, w, w') = ⟪w, B_k ρ(a) B_{k'}^* w'⟫` normalized by a
weighted trace `∑_k c_k tr (B_k B_k^*)`; the Hilbert–Schmidt hypothesis on the maps
`T_k = j ∘ π(ψ_k)` makes this trace finite for the global kernel, whose maps are the projected
adjoints `A_k = P₀ T_k^* : W → H₀`. The maps `B_k` at an extreme point play the role of Bernstein's
fibre maps `B_{ψ,z}` (J. Bernstein, *On the support of Plancherel measure*, 1988, §§1.3–1.5).

## The proof

1. **Test functions.** `exists_approxIdentity` gives an approximate identity `χ_n`. The index type
   is `κ = ℕ ⊕ Φ`, with `ψ_{inl n} = χ_n` and `ψ_{inr φ} = φ`; `nIdx = inl`.
2. **Hilbert–Schmidt sums.** For each `k`, the hypothesis gives that `T_k = j ∘ π(ψ_k)` is
   Hilbert–Schmidt; by `Langlands.Analysis.OperatorIdeals.isHilbertSchmidt_adjoint` and
   `hilbertSchmidtBasisIndependence`, `∑_b ‖T_k^* e_b‖²` converges for a Hilbert basis `e` of `W`
   (`exists_hilbertBasis`), hence so does `S_k = ∑_b ‖A_k e_b‖²` for `A_k = P₀ T_k^*`.
3. **Weights.** With an injection `enc : κ → ℕ` (`κ` is countable), put
   `c_k = 2^{-enc k} / (1 + S_k) > 0`, so that `c_k S_k ≤ 2^{-enc k}`.
4. **The global kernel.** `F⁰ = globalKernel` is a bounded cone element for the relations
   `globalRel` (`isConeElement_globalKernel`, `isBoundedForm_globalKernel`). Its weighted trace
   is `∑_k c_k S_k ≤ ∑_n 2^{-n} = 2`, and it is nonzero: for `h₀ ∈ H₀ ∖ {0}`,
   `j (π(χ_n) h₀) → j h₀ ≠ 0` (injectivity of `j`), so some `A_{inl n}^* h₀ = j π(χ_n) h₀` is nonzero,
   so `A_{inl n} e_b ≠ 0` for some `b` by `eq_zero_of_hilbertBasis`. Hence
   `traceW⁻¹ • F⁰ ∈ coneSet` (`smul_inv_mem_coneSet`) and it is nonzero.
5. **An extreme point.** `exists_extremePoint_ne_zero` (Krein–Milman) gives a nonzero extreme
   point `F` of `coneSet`.
6. **The representation.** `V = VL hF` and `σ = sigma hF hπu` (module
   `Langlands.Representation.Unitary.TemperedComponentGNS`) are unitary and jointly continuous.
   The maps `B_k = opB hF hB k` satisfy `B_{inl n} σ(a) σ(ψ_k) = π_W(χ_n) π_W(a) B_k`
   (`opB_relation`), take values in `W₀ = closure (j(H₀))` (`opB_mem_wSub`), and some `B_k v` is
   nonzero (`exists_opB_ne_zero`); in particular `V` is nontrivial, and `σ` is topologically
   irreducible by `isTopologicallyIrreducible_sigma`.
7. **The map `J`.** `exists_intertwiner` (module
   `Langlands.Representation.Unitary.TemperedComponentIntertwiner`) gives `D` and `J` with all
   clauses of the conclusion, applied with `W₀ = wSub j H₀` (closed, and invariant by
   `wSub_invariant`). The integrated operators of the statement, `∫ φ(g) • σ(g) d dμ(g)` and
   `∫ φ(g) • π_W(g) (J d) dμ(g)`, are by definition the values of `testOp`, and the clause for
   `ψ ∈ Φ` is the bound for the index `inr ψ`. The values `J d` lie in `wSub j H₀`, whose carrier
   is `closure (j '' H₀)` (`coe_wSub`).

## Dependencies

Mathlib (Krein–Milman `closure_convexHull_extremePoints`, completions of pre-inner-product
spaces, Bochner integration, the `L¹` continuity of the domain action `Lp.instContinuousSMulDomMulAct`,
Banach–Steinhaus) and, in the Library, `Langlands.Analysis.OperatorIdeals.isHilbertSchmidt_adjoint`
and `Langlands.Analysis.OperatorIdeals.hilbertSchmidtBasisIndependence`, together with the helper
modules `Langlands.Analysis.PositiveKernelHilbert`, `Langlands.Analysis.TraceNormalizedKernelCone`,
`Langlands.Analysis.TraceNormalizedKernelExtreme`,
`Langlands.Representation.Unitary.TestFunctionOperators`,
`Langlands.Representation.Unitary.TemperedComponentAlgebra`,
`Langlands.Representation.Unitary.TemperedComponentGNS`,
`Langlands.Representation.Unitary.TemperedComponentGlobalKernel`,
`Langlands.Representation.Unitary.TemperedComponentIntertwiner` and
`Langlands.Representation.Unitary.TemperedComponentFibre`.

## Remark on the scope of the argument

The proof produces one irreducible component, which is all the proposition asserts. Unlike the
direct-integral argument of the statement's Markdown, it does not show that the component is
weakly contained in `π|H₀` or that almost every fibre of a decomposition has the property.
