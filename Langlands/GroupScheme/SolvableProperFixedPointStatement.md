# Solvable fixed points on proper schemes

Workers 1293 and 1351.

`Langlands.GroupScheme.SolvableProperFixedPointStatement.{u}` defines the
algebraically closed field case of the Borel fixed-point theorem in Milne,
*Algebraic Groups* (2017), Corollary 17.3, printed p.353 (one-based PDF p.369).
It is a definition returning `Prop`. This module supplies no proof of the
proposition, and it does not assume fixed-point existence or any structural
input to that proof.

For every `k : Type u` with `Field k` and `IsAlgClosed k`, write
`S = Spec (CommRingCat.of k)`. The proposition quantifies over every actual
`H : GroupScheme S` with `Smooth H.X.hom` and `IsAffineHom H.X.hom`, then
assumes `ConnectedSpace H.X.left` and the existing
`IsSolvableGroupScheme H`. For every `X : Over S` it assumes
`IsProper X.hom` and `Nonempty X.left`; for every `a : SchemeAction H X`
it concludes

```lean
∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed x
```

There is no restriction on the characteristic or on the universe `u`.
The group is an actual group object in schemes over `S`, and its smoothness,
connectedness, affineness and solvability match the smooth connected solvable
algebraic group in Corollary 17.3. Milne works with affine algebraic groups
of finite type. Here smoothness gives local finite type, and affineness gives
quasi-compactness, so their combination retains finite type. Solvability is
exactly the published `IsSolvableGroupScheme` predicate: abstract solvability
of the algebraic-closure point group of the base change of `H`. The paired
Markdown for `Langlands.GroupScheme.Absolute.Borel` explains its agreement
with Milne's derived-series notion for smooth affine groups. That comparison
has not itself been formalized; it is not added as an assumed field here.

Milne introduces Corollaries 17.2 and 17.3 for separated algebraic schemes
`X`. His completeness convention is properness over the base field
(Appendix A.75 and A.76(b), printed p.583, PDF p.599). Mathlib's
`IsProper X.hom` means separated, universally closed and locally of finite
type; universal closedness also gives quasi-compactness, hence finite type.
Thus the proposition retains the required separatedness and finite type
without separate hypotheses. `X` may be nonreduced. It need not be smooth,
connected, affine or projective. Corollary 17.3 does not impose reducedness;
its proof reduces to reduced `X` after extension to an algebraically closed
field. The Lean nonemptiness hypothesis concerns the underlying scheme,
`Nonempty X.left`, and does not supply an initial rational point. The
conclusion supplies that rational point. Over an algebraically closed field,
Milne's geometric fixed point can be taken over `k` itself; the source's
more general field conclusion is not asserted here.

The action is the published actual categorical scheme action
`SchemeAction H X`, an abbreviation for `ModObj H.X X`, including its action
morphism and its unit and associativity laws. For the rational point `x`,
`a.IsFixed x` requires, for every test scheme `T : Over S`, every morphism
`b : T ⟶ Over.mk (𝟙 S)`, and every `h : T ⟶ H.X`, the equality
`a.act h (b ≫ x) = b ≫ x`. This is scheme-theoretic fixedness after every
refinement. The published `SchemeAction.isFixed_iff_universal` identifies it
with the universal product equation. This formulation expresses the fixed
subscheme meaning of Milne's `Xᴴ`: Theorem 7.1 (printed pp.138–139, PDF
pp.154–155) quantifies over all algebra extensions and all group points.
The all-scheme formulation agrees through the actual action morphism and
its restrictions to affine tests. Invariance under `H(k)` alone is not the
conclusion being defined.

The source route is Theorem 17.1, Corollary 17.2, then Corollary 17.3
(printed pp.352–353, PDF pp.368–369). Theorem 17.1 excludes complete
positive-dimensional subschemes in homogeneous spaces of smooth connected
solvable groups. Corollary 17.2 applies this to orbits. In 17.3, formation of
the fixed subscheme commutes with field extension; after the algebraically
closed and reduced reductions, a minimum-dimensional orbit is closed
(1.66), hence complete (A.75(a)), hence a single fixed point by 17.2. These
are literature explanations, not implemented Lean proofs. The proof of the
exact published proposition and all needed geometric inputs and comparisons
remain separate obligations. The arbitrary-field split-solvable
pseudo-complete theorem is outside this statement.

The registered original is `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was checked; its Chapter 17 entries do not change Corollary 17.3. The Lean
statement reuses Worker 1293's preliminary draft, with source comparison and
expanded documentation by Worker 1351.
