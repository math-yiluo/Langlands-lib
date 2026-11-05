# Proof of splitting for linear extensions of diagonalizable groups by closed additive subgroups

Module `Langlands.GroupScheme.LinearAdditiveExtensionSplittingProof`.

`Langlands.GroupScheme.linearAdditiveExtensionSplitting` proves the published proposition
`LinearAdditiveExtensionSplittingStatement.{u}` exactly, at arbitrary universe `u`. This is
Milne, *Algebraic Groups* (2022), Theorem 15.34(d), for a diagonalizable quotient. The
quantifiers are those of the statement. `k` is algebraically closed of any characteristic. `Λ`
is finitely generated and may have torsion or be trivial. The extension `E` is affine and
locally of finite type. `q` is flat, surjective and locally of finite presentation. The kernel
is the full actual kernel, embedded in `𝔾ₐ` by a closed immersion `a`, possibly finite or
nonreduced. The action `b` satisfies the two all-test equations. The finite generation of `Λ`,
local finite type of `E` and local finite presentation of `q` are not used.

The implemented proof follows Milne's argument for 15.34(d) and (a), rewritten concretely. It
does not use derived functors, sheaf `Ext` groups or the pushout extension.

1. **Equivariant function** (`LinearAdditiveExtension.exists_equivariant`). Degree-one Amitsur
   exactness for the faithfully flat cover `q` of the affine scheme `D` gives
   `f : E ⟶ 𝔾ₐ` with `f(g · ι(u)) = f(g) + χ(q g) a(u)`. This is a scheme section of the pushout
   torsor.
2. **Crossed homomorphism** (`LinearAdditiveExtension.crossedHom`, `crossedHom_mul`,
   `kernel_comp_crossedHom`). The two-variable function `χ(q g)⁻¹(f(g x) − f(g))` descends along
   `q ▷ E` to `D ⊗ E`. Its average over `D`, the constant coefficient at the universal point of
   `D(Λ)`, is a crossed homomorphism `c'` for the action through `χ ∘ q`, with `ι ≫ c' = a`.
   This uses quasi-compactness of `q`, which holds because `E` and `D` are affine.
3. **Correction** (`LinearAdditiveExtension.exists_corrected`). Let `f` be the monic additive
   polynomial cutting out the image of `a` (`ClosedAdditivePolynomial`). Then `f ∘ c'` descends
   to a crossed homomorphism of `D` for `χ^N`. Averaging shows that it is `μ (1 − χ^N)` for a
   constant `μ`. A root `r₀ ∈ k` of `f − μ`, which exists since `k` is algebraically closed,
   gives `c'' = c' + r₀(χ ∘ q − 1)` with values in the closed subgroup.
4. **Section** (`LinearAdditiveExtension.exists_section`). With `c'' = c₀ ≫ a`, let `σ(g)` be
   the unique point of the coset `g · kernel` on which `c''` vanishes. It descends along `q` to
   `s : D ⟶ E`. The uniqueness of these points shows that `s` is a homomorphism with
   `s ≫ q = 𝟙`.

The proof file assembles these steps. It converts `crossedHom_mul` and `kernel_comp_crossedHom`
to the pointwise hypotheses of `exists_corrected`, and passes the result to `exists_section`.

Source: J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a Field*,
corrected reprint 2022 (`milne-2022-algebraic-groups`). Theorem 15.34(d) is on printed
pp. 319–320 (zero-based PDF indices 329–330), with Proposition 15.31 and Exercise 14-3 used
there.
