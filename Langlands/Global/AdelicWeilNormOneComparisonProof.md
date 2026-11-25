# Canonical norm-one comparison for affine Weil restriction

`Langlands.Global.AdelicWeilRestriction.normOneComparison` proves
`NormOneComparisonStatement` in arbitrary universe `u`. For an extension
`L/F` of number fields and an affine group scheme `G` locally of finite type
over `L`, it uses the fixed `adelicPointsEquiv F L G`. The first two clauses
are `isHomeomorph_adelicPointsEquiv` for the actual point topologies and
`adelicPointsEquiv_rational` for the canonical principal-point maps.

Write `W = Res_{L/F} G`. To prove the reverse inclusion of norm-one subgroups,
the proof starts with an arbitrary `F`-character `ψ` of `W`. On each
commutative `L`-algebra, it evaluates `ψ` after the natural graph-factor
inclusion `WeilFactor.embNat`. These unit-valued group homomorphisms are
natural in the coefficient algebra. `AffineCharacterNaturalValues.character`
therefore realizes them by an actual `L`-character `χ` of `G`.

Over an `Ω`-algebra `R`, where `Ω/F` splits the embeddings of `L`, the tensor
evaluation maps identify the Weil points with a finite product of conjugate
point groups indexed by the embeddings `τ : L →ₐ[F] Ω`. Each factor uses `R`
with the `L`-action through `τ`. In the factor indexed by `τ`, the graph-factor
inclusion has the given point as its `τ`-coordinate by
`projNat_embNat_apply`. At a different embedding `σ`, the graph relation
shows that the image of the graph idempotent is annihilated by the image in
`R` of `σ(b) − τ(b)` for any `b : L`. Choosing `b` where the embeddings
differ makes that scalar a unit. The idempotent then evaluates to zero and
the corresponding point is the identity, by `IdempotentPoints.proj_map`
and `IdempotentPoints.proj_zero`.

The determinant defining the transferred norm character of `χ` becomes
the product of its coordinate values in the split tensor algebra.
On each single-coordinate inclusion, this product equals the value of
`ψ` by the construction of `χ`. `MonoidHom.pi_ext` extends the equality of
evaluations to the whole product, including noncommutative point groups.
For an arbitrary commutative `F`-algebra `A`, the proof applies the split
calculation to `AlgebraicClosure F ⊗[F] A`. Naturality and the injectivity
of `A → AlgebraicClosure F ⊗[F] A` on units give the same equality over `A`.

Taking `A` to be the full adele ring of `F` and applying
`IdeleAbsoluteValue.full F` turns this equality into an equality of
normalized character values. `characterNorm_normCharacter_apply` identifies
the transferred value at a ground-field adelic point with the value of `χ`
at its canonical image. Thus the inverse image of an upper-field norm-one
point has norm one for every `ψ`. Together with `map_normOneSubgroup_le`,
this proves equality of the full normalized-character kernel intersections
under the canonical map.

T. A. Springer states the topological and rational comparison for linear
algebraic groups in *Reduction theory over global fields* (1994), §1.4,
printed pp. 208–209 (PDF pp. 2–3), and the norm-one identification in the
reduction to the basic global field in §3.1(a)–(b), printed p. 214 (PDF p. 8).
The Lean proof gives the number-field comparison for arbitrary `L/F` by
the character evaluation argument above. The registered source is
`springer-1994-reduction-global-fields`, with SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
