# Unramified Hecke data of the cyclic character-twisted block sum

Derived from Clozel–Rajan, *Solvable base change*, arXiv:1806.02513v1, §7.1, Proposition 6 and the Hecke-matrix calculation after it (PDF p. 23), §7.2 (PDF p. 25), and §7.3 (PDF p. 26). These use the block maps of §6, (6.13)–(6.15) (PDF pp. 18–19). In §7.3 Clozel and Rajan state that at primes where all data are unramified, the endoscopic map on Hecke matrices sends `t_w(π_b)` to

`t_w(π_b ⊗ η_1) ⊕ t_w(σπ_b ⊗ η_2) ⊕ ⋯ ⊕ t_w(σ^(d−1)π_b ⊗ η_d)`,

and that this remains true for every automorphic `π_b` of `GL(b, A_E)`, in particular for those in the discrete trace formula of the endoscopic group. This file implements the numerical side of that calculation for unramified Satake data. It then proves that each block, and the whole block sum, has a genuinely attached cuspidal support. Blocks are indexed by `α : Fin d` and pair `σ^α` with `η α`; this is Clozel–Rajan's `η_(α+1)` with indices starting at `0`.

## Numerical blocks

Here `E` is a number field, `σ : E ≃+* E` is a supplied automorphism, and `η : Fin d → HeckeCharacter E` is a supplied family of characters. The code makes no assumption that `σ` generates a Galois group of prime order, and no recurrence among the `η α`.

- `blockPullback σ α` is `(σ ^ α)⁻¹`. Library arithmetic pullback along a ring isomorphism `e` sends an automorphic function `F` to `F ∘ adelicEquiv e`, so along `(σ ^ α)⁻¹` it sends `F` to `g ↦ F(θ^(−α)(g))`, where `θ` is the entrywise transport by `σ`. This is `A^α` for the operator `A F(x) = F(θ⁻¹(x))` of `AdelicGLCharacterTwistOperator`. The block is labeled `σ^α Π` in this convention.
- `blockSourcePlace σ α` is `(finitePlaceEquiv (blockPullback σ α)).symm`. This is the place correspondence in `cuspidalArithmeticSpectralTransport` for that pullback: at a finite place `v` it is the image of `v` under `σ^(−α)`.
- `blockPullbackSystem σ α s` reads the eigenvalue multiset of `s` at `blockSourcePlace σ α v`. It moves the exceptional set to the corresponding places.
- `twistedHeckeBlock σ η s α` multiplies every eigenvalue of that system at `v` by `(η α).finiteUniformizerValue v`, the value of the local component of `η α` at the Library's chosen uniformizer. The exceptional set is unchanged.
- `twistedBlockSystem σ η s` is the `SpectralSystem.finiteSum` of the `d` blocks. Its rank is `∑ _ : Fin d, b`. Its exceptional set is the union of the block exceptional sets, and its eigenvalue multiset at `v` is the sum of the block multisets.

`twistedHeckeBlock_eulerPolynomial` is the Euler-polynomial form of the scaling. Off the exceptional set, the polynomial of block `α` at `v` equals the polynomial of `s` at `blockSourcePlace σ α v`, composed with `X ↦ (η α).finiteUniformizerValue v · X`. It is `SpectralSystem.scale_eulerPolynomial`.

## Attached cuspidal support

The section `Actual` assumes `CompactSpace (AdeleQuotient E)`, as the Library's cuspidal-class API requires, and that each `η α` has finite order, the hypothesis of the Library's determinant twist of cuspidal classes.

`twistedBlockConstituent σ η hη c (α, j)` is the actual positive-rank cuspidal class obtained from the constituent `c j` by arithmetic pullback along `blockPullback σ α`, followed by `PositiveRankCuspidalClass.determinantTwist` by `η α`. Its rank is that of `c j`.

`exists_twistedHeckeBlock_support` takes a finite family `c : Fin m → PositiveRankCuspidalClass E` with attached spectral systems `t j`, in the sense of `PositiveRankCuspidalClass.HasSpectralSystem`. It also takes a system `s` of rank `b` whose Euler polynomials agree off a finite set with those of `SpectralSystem.finiteSum t`. For each block `α` the theorem gives systems `u j` attached to `twistedBlockConstituent σ η hη c (α, j)` whose finite sum has the same Euler polynomials as `twistedHeckeBlock σ η s α` off a finite set.

The proof applies `cuspidalArithmeticSpectralTransport` to each `c j` along `blockPullback σ α`. This gives an attached system `t' j` whose Euler polynomial at almost every `v` is that of `t j` at `blockSourcePlace σ α v`. Then `PositiveRankCuspidalClass.HasSpectralSystem.determinantTwist` attaches to the twisted class the system `t' j` scaled by `(η α).finiteUniformizerValue`, restricted away from `(η α).finiteDeterminantTail`. At places outside the finitely many exceptional and transported exceptional places, the polynomial of the sum is the product over `j`. The cofinite comparison `hs` is pulled back along the bijection `blockSourcePlace σ α`, which preserves cofinite sets. `Polynomial.prod_comp` moves the uniformizer substitution through the product.

`exists_twistedBlockSystem_support` flattens the blocks. The attached family is indexed by `Fin d × Fin m`, with the class at `(α, j)` equal to `twistedBlockConstituent σ η hη c (α, j)`. The finite sum of its systems has the same Euler polynomials as `twistedBlockSystem σ η s` off a finite set. The proof combines the blockwise results with `Fintype.prod_prod_type`.

The family `c` may repeat classes, so multiplicities are retained. This is the form needed when `s` is the Satake system of an isobaric sum, of a residual Speh-type representation, or of the data inducing a proper Levi term, once the cuspidal attachments of its constituents are supplied. Supplying those attachments, and showing that a given discrete-spectrum representation has such a cuspidal support, are not part of this file.

## Scope

This file contains the unramified, Hecke-matrix-level calculation of §7.3 only. It does not assume or prove any of the following:

- the recurrence `η_(α+1) ∘ σ = ω η_α` for the characters;
- that the block sum agrees with Clozel–Rajan's endoscopic `ξ₁` up to conjugation (that comparison concerns L-homomorphisms, see `CyclicRelativeWeilBlockSum`);
- that the stable or twisted side of the trace formula is supported on these blocks;
- multiplicity one or linear independence of Hecke characters;
- any trace identity.

It records only that the transferred Hecke data of a supported system is again the Hecke data of an explicit, actually attached family of cuspidal classes.
