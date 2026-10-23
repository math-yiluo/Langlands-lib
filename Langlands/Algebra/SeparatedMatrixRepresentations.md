# Finiteness of separated matrix representations of a finitely generated algebra

This internal algebraic module supplies the finiteness step of
Bernstein--Zelevinsky (1976), 4.16, page 41. The source finishes 4.16 by appeal
to the fact that a finitely generated algebra has only finitely many separated
representations of a fixed finite dimension. The proof here is a derived
argument and does not follow a printed proof.

## Setting

`R` is a complex algebra, `Ring R` and `Algebra ℂ R`. The generators are a
finite family `gen : Fin t → R` with `Algebra.adjoin ℂ (Set.range gen) = ⊤`.
A matrix representation of size `s` is an algebra homomorphism
`R →ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ`.

## Declarations

- `generatorEntries gen φ` is the point of `Fin t × Fin s × Fin s → ℂ` that
  lists the matrix entries `φ (gen k) a b` of the generator images.
- `exists_genericMatrix gen hgen r` gives, for each `r : R`, one matrix `Q` of
  polynomials in `MvPolynomial (Fin t × Fin s × Fin s) ℂ`. For every matrix
  representation `φ`, evaluating `Q` entrywise at `generatorEntries gen φ`
  gives `φ r`. The proof is induction on the adjoin (`Algebra.adjoin_induction`).
  A generator `gen k` is the matrix of variables `X (k, a, b)`. Scalars, sums
  and products are handled by `AlgHom.commutes`, `map_add` and `map_mul`, using
  that entrywise evaluation `(aeval _).mapMatrix` is a ring homomorphism.
- `finite_of_separated_matrixRepresentations gen hgen ψ f hself hother` takes a
  family `ψ : ι → R →ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ` and elements `f : ι → R`
  such that `ψ i (f i) ≠ 0` for all `i` and `ψ j (f i) = 0` for all `i ≠ j`.
  It concludes `Finite ι`.

## Proof of finiteness

For each `i`, `J i` is the ideal spanned by the entries of the generic matrix
of `f i`. Evaluation at the point of `ψ j` sends these entries to the entries
of `ψ j (f i)`. So `J i` lies in the kernel of evaluation at `ψ j` when
`j ≠ i`, and does not lie in the kernel of evaluation at `ψ i`.

The polynomial ring is Noetherian (`IsNoetherianRing ℂ` comes from the
principal-ideal-domain import). By `set_has_maximal_iff_noetherian`, the
finite suprema `⨆ i ∈ F, J i`, for `F : Finset ι`, have a maximal member `F`.
Suppose `i ∉ F`. Every `J j` with `j ∈ F` lies in the kernel at `ψ i`, so their
supremum does too. Since `J i` is not in that kernel, it does not lie under the
supremum. Then the supremum over `insert i F` is strictly larger, which
contradicts maximality. Hence every `i` lies in `F`, and `ι` injects into the
finite set `F`.
