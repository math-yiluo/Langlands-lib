# Proof of the hyperplane-slicing induction step of the uniform Lang–Weil estimate

Authors: Worker 5132 and Worker 196.

`familyLangWeilSlicing` proves the published statement
`Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilSlicingStatement`, which is imported
unchanged. Given Bertini's theorem for the generic hyperplane section
(`BertiniGenericHyperplaneStatement`) and the uniform point-count upper bound in families
(`FamilyPointUpperBoundStatement`), the uniform Lang–Weil estimate in fibre dimension `d + 1`
(`FamilyLangWeilInDimension (d + 1)`) implies it in fibre dimension `d + 2`. The proof uses no
other hypotheses. It combines two results from the helper modules in `Slicing/`, joined by the
ring-level interface `Slicing.AffineFamilyLangWeil e` defined in `Slicing/Reduction.lean`.

## The interface

`AffineFamilyLangWeil e` says: let `R` be a domain of finite type over `ℤ`, `A` an `R`-algebra
of finite type and `r₀ ≠ 0` in `R`, such that `K ⊗[R] A` has prime nilradical and Krull
dimension `e` for every field `K` over `R` in which `r₀` does not vanish. Then there are `r ≠ 0`
in `R` and `C > 0` with `|#(A →ₐ[R] κ) - (#κ)^e| ≤ C (#κ)^(e - 1/2)` for every finite field `κ`
over `R` in which `r` does not vanish. This is the Lang–Weil estimate for a geometrically
irreducible affine family `Spec A → Spec R` of dimension `e`, over the dense open subset
`D(r)` of an integral base.

## The two steps

1. **Slicing for affine families** (Worker 5132, `Slicing/Core.lean`):
   `Slicing.affineFamilyLangWeil_slicing hB hUB d hLW` proves `AffineFamilyLangWeil (d + 2)`
   from the three hypotheses. It counts pairs of a point and an affine hyperplane through it.
   The estimate in dimension `d + 1` is applied to the universal hyperplane section, over the
   parameter ring of hyperplanes localized at a nonzero polynomial `c`. Here `c` is built from
   Bertini's theorem with spreading (`Slicing/GenericSlice.lean`) and Chevalley's theorem
   (`Slicing/GenericImage.lean`). The remaining hyperplanes are bounded by
   `FamilyPointUpperBoundStatement` and the Schwartz–Zippel lemma (`Slicing/Counting.lean`).
   The proof is described in `Slicing/Core.md`.
2. **Reduction to affine families** (Worker 196, `Slicing/Reduction.lean`):
   `Slicing.familyLangWeil_of_affine hUB e` turns `AffineFamilyLangWeil (e + 1)` into
   `FamilyLangWeilInDimension (e + 1)`. The base is covered by finitely many affine opens
   `S₀`, and every `κ`-point of `S` factors through one of them. Over a fixed `S₀`, Noetherian
   induction on the ideals of `Γ(S₀)` reduces the estimate to the finite fields near a single
   prime `𝔭` (those in which `𝔭` vanishes and a fixed `r ∉ 𝔭` does not). The preimage of `S₀`
   is covered by finitely many affine charts, and one chart `c₀` contains a point over `𝔭`.
   `AffineFamilyLangWeil (e + 1)`, applied over the domain `Γ(S₀) ⧸ 𝔭`, gives the main term
   from the points in `c₀`. The fibre over `𝔭` is irreducible, so every other chart has an
   element `a` with `D(a)` inside `c₀` and `a` not nilpotent in the fibres near `𝔭`. The
   remaining points lie in the zero sets of these elements, whose fibres have dimension at most
   `e`, and `FamilyPointUpperBoundStatement` bounds them by `C (#κ)^e`. The proof is described
   in `Slicing/Reduction.md`.

The theorem applies step 2 with `e = d + 1` to the output of step 1:

`fun hB hUB d hLW => familyLangWeil_of_affine hUB (d + 1) (affineFamilyLangWeil_slicing hB hUB d hLW)`.

## Helper modules

- `Slicing/Counting.lean`: double counting of points on hyperplanes, the Schwartz–Zippel bound
  and the final real-number estimate.
- `Slicing/Bridges.lean`: ring-level forms of the family statements via `Spec`.
- `Slicing/Dimension.lean`: Krull dimension of quotients and hyperplane sections.
- `Slicing/Hyperplane.lean`: the universal hyperplane section and its base changes.
- `Slicing/GenericSlice.lean`: Bertini plus spreading gives the bad-parameter polynomial `c₁`.
- `Slicing/GenericImage.lean`: Chevalley's theorem gives the polynomial `c₂`, for hyperplanes
  that do not contain the fibre.
- `Slicing/Core.lean`: the slicing estimate for affine families.
- `Slicing/Reduction.lean`: the interface `AffineFamilyLangWeil` and the reduction to it.

## Provenance

The route follows the induction step of Lang and Weil, *Number of points of varieties in finite
fields* (Amer. J. Math. 76 (1954), registered source `lang-weil-1954-number-of-points`, printed
pp. 822–823), and Tao, *The Lang–Weil bound* (registered source `tao-2012-lang-weil-bound`,
Section 2), made uniform in families as described in the Markdown of
`FamilyLangWeilSlicingStatement`.
