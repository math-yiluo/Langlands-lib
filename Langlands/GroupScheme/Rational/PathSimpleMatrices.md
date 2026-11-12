# Canonical reflection matrices in the normalized path basis

This internal prerequisite computes the actual canonical simple-reflection representatives in the normalized path basis. It is derived from the published normalized-vector action formulas in `PathReflectionScalars` and the remaining-line stabilizer formula in `PathLineStabilizers`, through the coordinate interface in `PathNormalizedMatrices`.

Work over an arbitrary field `k : Type u`, with an affine group scheme, a supplied split pinning, a finite matrix representation of highest weight `lam`, a path component `β : Fin L → p.base.support`, and the condition that `lam` is fundamental at the first path vertex. For the action statements, supply normalized simple-root parametrizations `x` and a nonzero vector `v₀` in the initial path weight space. There is no parity or algebraic-closure restriction in this module.

`pathReflectionMatrix i` is the matrix indexed by `Fin (L + 1)` whose column `i.castSucc` has entry `-1` at row `i.succ`, whose column `i.succ` has entry `1` at row `i.castSucc`, and whose other columns are the corresponding identity columns. Thus its two by two block on those consecutive indices is `[[0, 1], [-1, 0]]`. All entries and signs are interpreted in the supplied field, including characteristic two.

`normalizedPathMatrix_canonicalReflection` states that the actual rational-point matrix of `(x (β i)).reflectionRepresentative.point`, expressed in the normalized basis, equals `pathReflectionMatrix i`. The two distinguished column lemmas apply the published formulas sending the normalized vector at `i` to minus the vector at `i + 1` and the vector at `i + 1` to the vector at `i`. The other-column lemma applies `canonicalReflection_path_fixes`. Taking basis coordinates converts these vector equalities to matrix entries; matrix extensionality and the three column cases prove the complete equality.

This pair establishes the canonical reflection factor calculation. Root-coordinate factors, modified-product characteristic polynomials, and the canonical-quotient cross-section theorem remain separate obligations.
