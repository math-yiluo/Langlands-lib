# Hom spaces from a supplied twisted piece

This module supplies derived algebraic support for the endomorphism argument
using the geometric lemma in Renard VI.5.3, as applied in VII.1.3. It does not
construct geometric pieces, prove the geometric lemma, or prove the maximal-Levi
dichotomy. The relevant original context is Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 version, VI.5.3, printed p.173 / PDF p.179, and
VII.1.3, printed p.225 / PDF p.231.

The acting group `H`, the carrier `V` of `ρ`, and the carrier `W` of `τ` have
independent universes. Both are complex representations of the actual group.
There is no topology, smoothness, admissibility, finite-dimensionality, or
algebraicity premise. A homomorphism `α : H →* H`, a supplied complex-linear
equivalence `T : W ≃ₗ[ℂ] V`, and its covariance
`T (τ m x) = ρ (α m) (T x)` are inputs. The module asserts no existence of these
inputs. Its provenance is internal derived algebra from the published
surjective-pullback, intertwiner Schur, and Hom length results.

`twistedPieceEquiv` packages `T` and this covariance into an actual representation
equivalence from `τ` to `ρ.comp α`; its underlying linear map is `T`.

`length_hom_le_one_of_twistedPiece` additionally assumes `α` is surjective, `ρ`
is irreducible, and every intertwining endomorphism of `ρ` is a scalar multiple
of its identity. It proves that the full intertwining space `Hom_H(τ, ρ)` has
complex module length at most one. This is extended-natural module length, via
`HomSpace.length`, and does not require finite-dimensionality in its premises.
The proof transfers irreducibility through surjective pullback and
`twistedPieceEquiv`. If every intertwiner is zero, the Hom space has length zero.
Otherwise a nonzero intertwiner is bijective by irreducible Schur. Source
transport then identifies the Hom space with `End_H(ρ)`, whose length is at most
one by the explicit scalar premise. No scalarity premise on the pullback action
is needed.

`inverseTwistedPieceEquiv` additionally assumes only irreducibility of `ρ`,
surjectivity of `α`, and a specified nonzero intertwiner `f : τ → ρ`. It returns
an actual representation equivalence from `ρ` to `ρ.comp α`. The proof composes
`f` with `T⁻¹`, checks nonzeroness using surjectivity of `T`, and checks the
covariance `S (ρ (α m) y) = ρ m (S y)`. The published twisted-intertwiner Schur
result makes `S` invertible. Its inverse `U` therefore satisfies
`U (ρ m x) = ρ (α m) (U x)`, the direction used in the endomorphism dichotomy.
This constructor requires no scalarity premise.

The geometric lemma, the production of its supplied piece equivalences, the
identity-double-coset bookkeeping, the actual adjunction and the final
endomorphism dichotomy remain separate obligations.
