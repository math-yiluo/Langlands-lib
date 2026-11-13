# Coroot points on normalized path lines

This internal prerequisite works over an arbitrary field `k : Type u`. It uses the actual affine group scheme `G` over `Spec k` with a supplied split pinning `p`, and a matrix representation `ρ` with a finite decidable index type `d : Type`. For the normalized path results, `ρ` is a supplied highest-weight representation that is fundamental at the first vertex of a path component `β : Fin L → p.base.support`. It also uses supplied normalized simple-root maps `x` and a nonzero initial vector `v₀` of the first path weight space, the same data as `Langlands.GroupScheme.Rational.PathNormalizedMatrices`. There is no parity, characteristic, infinitude, perfection or algebraic-closure assumption. Here `t : kˣ` is a unit, `r` is a root index of the pinning, and `⟨w, ν⟩` is the root-datum pairing `p.rootDatum.toLinearMap w ν` of a character `w` with a cocharacter `ν`.

## Definition

`adjacentCorootMatrix L i t` is the diagonal matrix indexed by `Fin (L + 1)`, the lines `0, ..., L`. Its entry at line `i` is `t`, its entry at line `i + 2` is `t⁻¹`, and every other diagonal entry is `1`. A line `i` or `i + 2` outside `0, ..., L` does not occur; the theorem below assumes `i + 2 ≤ L`. `adjacentCorootMatrix_eq` unfolds it to `Matrix.diagonal` of this function, by definition.

## Statements

- The imported `CocharacterUniformizer.rationalCharacterEval_cocharacterPoints k T w ν t`: for a commutative group scheme `T` over `Spec k` (no splitness is assumed), a character `w` and a cocharacter `ν`, evaluating the rational character of `w` at the rational point `ν(t)` gives `t ^ latticePairing T w ν`.
- `rationalMatrix_torusPoint_mulVec_of_mem`: if `v` lies in the `ρ`-weight space of `w` for the split maximal torus, then every rational point `s` of the torus multiplies `v` by the value of the rational character of `w` at `s`. In symbols, `ρ(s) v = w(s) • v`.
- `rationalMatrix_corootRationalPoint_mulVec_of_mem r t hv`: on the weight space of `w`, the coroot point `r^∨(t) = corootRationalPoint p r t` acts by the scalar `t ^ ⟨w, r^∨⟩`.
- `normalizedPathMatrix_eq_diagonal c hg`: suppose a rational point `g` of `G` has every normalized path vector `j` as an eigenvector with eigenvalue `c j`. Then its matrix `normalizedPathMatrix hρ hβ hlam x v₀ hv₀ g` in the normalized path basis is `Matrix.diagonal c`.
- `normalizedPathMatrix_corootRationalPoint r t`: the matrix of `r^∨(t)` in the normalized path basis is diagonal. Its entry at line `j : Fin (L + 1)` is `t ^ ⟨pathWeight β lam j, r^∨⟩`.
- `adjacentRoot_coroot hβ hi hr`: let `i + 2 ≤ L` and let the root of `r` equal `α_(β i) + α_(β (i+1))`. Then the coroot of `r` is `α_(β i)^∨ + α_(β (i+1))^∨`.
- `normalizedPathMatrix_corootRationalPoint_adjacent hβ hi hr t`: under the same hypotheses on `i` and `r`, the matrix of `r^∨(t)` in the normalized path basis is `adjacentCorootMatrix L i t`. This is the diagonal matrix with `t` at line `i`, `t⁻¹` at line `i + 2`, and `1` at every other line.

This module does not use the even-chain data. For a path `C.path c` of length `L = 2m` in such data, the merged root is `α = (C.modified c).alpha`. The field `SteinbergModifiedData.root_eq`, rewritten with `C.modified_a` and `C.modified_b`, gives the hypothesis `hr` for `r = α` and `i = m - 1`, where `i + 2 = m + 1 ≤ 2m`. In that setting the last theorem gives the matrix of `α^∨(t)` on the path lines.

## Proofs

The module reuses
`CocharacterUniformizer.rationalCharacterEval_cocharacterPoints` from
`CocharacterUniformizerEvaluation`. Unfolding `cocharacterPoints` identifies its
rational point with the displayed composite through `Gm.affinePointsEquiv`; its
conclusion is exactly the character/cocharacter pairing formula needed here.

`rationalMatrix_torusPoint_mulVec_of_mem` applies the published `characterSpace_affine` to the affine point of `s` over the test algebra `k`. It identifies that affine action with the rational matrix of `s ≫ p.inclusion` using `affineMatrix_restrict`, `affineUnitsEquiv_rationalAffinePoint`, `rationalMatrix_eq_affineMatrix` and `rationalAffinePoint_comp`.

`rationalMatrix_corootRationalPoint_mulVec_of_mem` applies the torus statement to the rational point of the coroot cocharacter at `t`, which is the point under `corootRationalPoint`. It evaluates the scalar with the first theorem. The pinning field `p.isRootDatum.1` identifies the root-datum pairing with `latticePairing p.torus`.

`normalizedPathMatrix_eq_diagonal` compares entries. Column `j` of the normalized path matrix is the coordinate vector of `ρ(g)` applied to the basis vector `j`. By hypothesis this is `c j` times basis vector `j`, whose coordinates are `c j` at `j` and `0` elsewhere.

`normalizedPathMatrix_corootRationalPoint` applies the diagonal criterion to the scalars from the coroot theorem. Each normalized path vector lies in its path weight space.

`adjacentRoot_coroot` uses the published `adjacentRoot_eq_reflectionPerm`. It says that `r` is the reflection of the root index `β (i+1)` in `β i`. The coroot of a reflected root is the coreflected coroot (`RootPairing.coroot_reflectionPerm`, `RootPairing.coreflection_apply_coroot`). The adjacent Cartan pairing `hβ.pairing_succ_right` is `-1`, so the coreflection gives `α_(β (i+1))^∨ + α_(β i)^∨`.

`normalizedPathMatrix_corootRationalPoint_adjacent` unfolds `adjacentCorootMatrix` and rewrites the diagonal entries with the coroot sum and additivity of the pairing. It evaluates both pairings with the published `pairing_pathWeight_mk`, which gives `1` at `j = i`, `-1` at `j = i + 1` and `0` otherwise. The exponent is therefore `1` at line `i`, `-1 + 1 = 0` at line `i + 1`, `-1` at line `i + 2` and `0` elsewhere. A case split on these conditions finishes the proof.

## Provenance

This is internal derived infrastructure, written for Task 5373: the proof of the split even-path cross-section (Steinberg 1965, *Regular elements of semi-simple algebraic groups*, Sections 9.15-9.19). It records the standard facts that a torus acts on a weight space by the weight and that a coroot point `r^∨(t)` acts on the weight `w` by `t ^ ⟨w, r^∨⟩`, specialized to the normalized path basis. It makes no direct literature claim. Every statement is exactly as written in the Lean file.
