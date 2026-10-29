# Finite twisted coinvariants of irreducible cuspidal Levi representations

Author: Worker 784.

`Langlands.Whittaker.LeviCuspidalCoinvariantFinitenessStatement.{uF,uV}` is a
`Prop`-valued definition. It states the finite-dimensionality part of the
cuspidal-Levi coefficient step (5) in the proof of Bernstein–Zelevinsky (1976),
Theorem 7.12, printed p.61. This module supplies no proof of the proposition.
It does not assume the proposition anywhere.

## Exact statement

For every prime `p` with `[Fact p.Prime]`, every finite extension
`F : PadicField.{uF} p` of Mathlib's `ℚ_p`, every supplied
`T : F.TopologicalData`, every `n : ℕ` with `0 < n`, and every
`B : GeneralLinear.BlockShape n`, the body installs `letI := T.topology`. Then
for every `σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)` it assumes

- `σ.IsIrreducible`, and
- `CuspidalSupport.IsLeviCuspidal B σ.representation`.

Let `U_B` be

```lean
Subgroup.pi Set.univ
  (fun i : Fin B.length => GeneralLinear.upperUnipotent (B.size i) F.Carrier)
```

Then for every monoid homomorphism `η : U_B →* ℂˣ` with
`IsLocallyConstant (fun u => (η u : ℂ))`, the statement concludes

```lean
FiniteDimensional ℂ
  (Jacquet.Localization.Coinvariants σ.representation U_B η)
```

The Lean source spells out `U_B` in both places where it occurs. The binder
shape `(n : ℕ), 0 < n → ∀ B, letI := T.topology; ∀ σ, …` is the same as in the
published `Langlands.CuspidalSupport.PadicLeviCuspidalFactorizationStatement`.

## Actual objects

- `B.Levi F.Carrier` (`Langlands.Group.GL.Blocks`) is the actual abstract
  product `∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier`. It carries
  the product of the matrix-unit topologies induced by `T.topology`. It is the
  source's `G_β = ∏ G_{n_i}` (BZ76 §§3.3–3.4) for the ordered partition
  `β = (B.size 0, …, B.size (B.length - 1))` of `n`. Every block size is
  positive, so `0 < n` forces `B.length ≥ 1`.
- `GeneralLinear.upperUnipotent m F.Carrier` (`Langlands.Group.GL.UpperUnipotent`)
  is the existing subgroup of upper triangular matrices in `GL_m(F)` with all
  diagonal entries `1`. This is the source's `U_m` (BZ76 §5.1, printed p.44).
- `U_B = Subgroup.pi Set.univ (fun i => upperUnipotent (B.size i) F.Carrier)`
  is the subgroup of `B.Levi F.Carrier` of tuples whose `i`-th component is
  upper unitriangular, for every block `i`. This is the source's
  `U ∩ G_β = ∏ U_{n_i}` of §7.12(5), with `G_β` taken as the abstract product.
  The block-diagonal embedding `B.leviEmbedding` into `GL_n` is not used here.
  `U_B` is the same subgroup term that
  `Langlands.Whittaker.openStabilizerLocalizationEquiv` (module
  `Langlands.Representation.Whittaker.OpenStabilizerLocalization`) uses. It is
  the instance `U = fun i => upperUnipotent (B.size i) F.Carrier` of the
  subgroup `Subgroup.pi Set.univ U` in
  `Langlands.FiniteTensor.characterLocalizationEquiv` (module
  `Langlands.Representation.Tensor.CharacterLocalization`). `U_B` carries the
  subspace topology of the product topology.
- `Jacquet.Localization.Coinvariants ρ U η` (`Langlands.Representation.Jacquet.Localization`)
  is the existing quotient of the carrier by
  `Jacquet.Localization.relations ρ U η`. That is the complex span of the
  vectors `ρ u v - (η u : ℂ) • v` for `u ∈ U` and `v` in the carrier. It is
  the space `E_{H,θ} = E / E(H,θ)` of BZ76 Definition 2.30, printed p.24, with
  `H = U_B` and `θ = η`.
- `SmoothRep.{0,uF,uV} ℂ G` (`Langlands.Representation.Category.Basic`) is
  the full subcategory of Mathlib's `Rep ℂ G` on objects in which every vector
  has an open stabilizer. These are the algebraic representations of BZ76
  §2.1, printed p.15. No topology is placed on the carrier, and no finite
  dimension is required.
- `σ.IsIrreducible` is Mathlib's `Representation.IsIrreducible` of the
  underlying action. It means the lattice of invariant subspaces is simple, so
  the carrier is nonzero. This is BZ76's irreducibility (p.15).
- `CuspidalSupport.IsLeviCuspidal B ρ`
  (`Langlands.Representation.CuspidalSupport.LeviDefinitions`) is
  `IsAdmissible ρ ∧ IsLeviQuasicuspidal B ρ`. `IsAdmissible` is smoothness
  together with finite-dimensional fixed vectors for every open subgroup.
  `IsLeviQuasicuspidal B ρ` says that for every proper standard block
  refinement `S` of `B` (`refinedParabolic F B S ≠ ⊤`), the ordinary
  coinvariants `Jacquet.Coinvariants ρ (refinedUnipotent F B S)` are a
  subsingleton. This matches BZ76 §3.18, printed p.34: a representation of
  `G_α` is quasi-cuspidal if `r_{β,α}(π) = 0` for every partition `β ≤ α`
  with `β ≠ α`, and "an admissible quasi-cuspidal representation is called
  cuspidal". Vanishing of a Jacquet module does not depend on its normalizing
  twist.
- A character of an l-group is, in BZ76 §1.19 (printed p.11), a locally
  constant homomorphism into `ℂ^*`. The monoid homomorphism `η : U_B →* ℂˣ`
  with `IsLocallyConstant (fun u => (η u : ℂ))` is exactly such a character of
  `U_B`.

The local `letI := T.topology` installs exactly the supplied field topology
before smoothness, admissibility, quasicuspidality and local constancy are
formed.

## Scope and what is not assumed

The quantification is over all positive ranks `n`, all ordered positive block
shapes `B` (including one-block shapes and blocks of size `1`), all
irreducible cuspidal `σ`, and all locally constant characters `η`. In
particular `η` may be trivial or degenerate.

The statement does not assume any of the following:

- genericity or non-degeneracy of `σ` (BZ76 §5.7) or of `η` (BZ76 §5.6);
- the existence of a nonzero Whittaker functional;
- any multiplicity-one result, in particular not the unproved Library
  proposition `Langlands.Whittaker.MultiplicityOneStatement`;
- finite dimension of the carrier of `σ`;
- a tensor factorization of `σ` along the blocks, or a central character.

Assuming finite dimension of the carrier would make the statement nearly
vacuous. By a standard fact, not formalized here, an irreducible cuspidal
representation with a block of size at least `2` is infinite-dimensional.

The field and carrier universes `uF` and `uV` are independent parameters. The
coefficient field `ℂ` lies in `Type 0`, the first universe argument of
`SmoothRep`.

Rank `0` is excluded by `0 < n`, as the task specifies and as in
`PadicLeviCuspidalFactorizationStatement`. For `n = 0` the only block shape is
empty, `U_B` is trivial, and the coinvariant quotient is the carrier itself,
which is one-dimensional by irreducibility. This boundary remark is not part
of the statement.

## Relation to the source assertion

In the proof of Theorem 7.12 (printed pp.60–61), step (5) reads, for an
irreducible cuspidal representation `(ρ, G_β, V)`:

> Now `U ∩ G_β = ∏ U_{n_i}` and `θ^{w⁻¹}|_{U ∩ G_β} = ∏ θ_i`, where `θ_i` is a
> character of `U_{n_i}`. Recalling that `ρ` is irreducible and cuspidal, we
> see, exactly as in 5.18, that if at least one of the `θ_i` is degenerate,
> then `V_{∏U_{n_i}, ∏θ_i} = 0`. But if all the `θ_i` are non-degenerate, then
> `dim V_{∏U_{n_i}, ∏θ_i} = 1`.

So the source asserts **dimension zero or one**, according as some block
character is degenerate or all are non-degenerate. Step (5) uses only the
bound `dim ≤ 1` to obtain `dim E_{U,θ} ≤ n!`. Step (6) uses the exact values
for non-degenerate `θ`. This pair states only the
weaker conclusion that the space is **finite-dimensional**. The following
source assertions are not stated here:

- the bound `dim ≤ 1`;
- vanishing for a degenerate block character;
- dimension exactly one when all block characters are non-degenerate.

Finite dimension is what the finiteness proof of
`Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` (BZ76
Theorem 5.21, finiteness part) needs from the cuspidal inducing data, where
finitely many orbit contributions are combined.

In the source the character is the restriction `θ^{w⁻¹}|_{U ∩ G_β}` of a
character of `U_n`. Here `η` is an arbitrary locally constant character of
`U_B`, so the statement does not depend on the Bruhat cell or the Weyl
element.

BZ76 §5.6 (printed p.45) calls a character `θ(a_1, …, a_{m-1})` of `U_m`
non-degenerate if all `a_j ≠ 0`, and degenerate otherwise. Here §5.5
identifies the characters of `U_m` through its superdiagonal entries. For a
block of size `1` the group `U_1` is trivial and the block character is
vacuously non-degenerate.

## Proof obligations (not formalized here)

A proof of this target must supply the following. They are obligations, not
premises.

1. **Tensor factorization.** The published theorem
   `Langlands.CuspidalSupport.padicLeviCuspidalFactorization` proves
   `PadicLeviCuspidalFactorizationStatement`. It gives an equivalence of
   `σ.representation` with `B.blockTensor (fun i => (A i).obj.representation)`
   for irreducible supercuspidal block representations `A i`, with carriers
   in a prescribed universe. A proof must transport the coinvariant quotient
   along this equivalence, for example with
   `Jacquet.Localization.representationEquiv`.
2. **Character decomposition.** A proof must write `η` as
   `FiniteTensor.productCharacter` of its blockwise restrictions `η_i`. Here
   `η_i` is `η` evaluated on tuples that are `1` outside block `i`, and each
   `η_i` is locally constant. This is the source's `∏ θ_i`. It is elementary
   but not formalized here.
3. **Tensor localization.** `Langlands.FiniteTensor.characterLocalizationEquiv`
   identifies the character coinvariants of a finite external tensor for a
   product character with the tensor product of the blockwise coinvariants. A
   finite tensor product of finite-dimensional spaces is finite-dimensional.
4. **Single-block cuspidal character cases.** For every irreducible cuspidal
   representation `ρ` of `GL_m(F)` with `m ≥ 1`, and every locally constant
   character `θ` of `upperUnipotent m F`, a proof must show that `ρ_{U_m,θ}`
   is finite-dimensional. No Library result imported by this module supplies
   this. In the source it is §5.18 (printed p.50): "If `π` is cuspidal and
   irreducible, then `π|_P = τ_P^0`. The proof follows from Proposition
   5.15a) and Theorem 5.16." There are two cases.
   - For degenerate `θ`, vanishing comes from Proposition 5.15(a)
     (pp.49–50). That proposition rests on the derivative functors of
     §§5.9–5.14.
   - For non-degenerate `θ`, dimension one is Theorem 5.16 (p.50). Its proof
     uses the invariant-distribution theorems of §6 (pp.52–57) and occupies
     §§7.1–7.9 (pp.57–60). Theorem 5.16 is a
     multiplicity-one theorem. A proof of this target may not cite an
     unproved multiplicity-one statement as a theorem. It must prove the
     needed finiteness or bound.
   - For `m = 1`, `U_1` is trivial. The coinvariants are the whole
     representation, which is one-dimensional by Theorem 5.16 for `n = 1`
     (or by Schur's lemma for the abelian group `F^×`).

## Consumer

This is the cuspidal coefficient input for proof task
5ab445dc-d2b4-4072-80d1-6370870a4a26 (Worker 499). That task's unchanged
target is `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement`.
According to the task context, that proof uses the existing
`CuspidalSupport.cuspidalEmbedding`, exactness of character localization
(BZ76 Proposition 2.35, printed p.25), and a finite orbit filtration. A
separate statement about preservation under normalized induction will take
finiteness for arbitrary locally constant characters on the Levi as an
explicit hypothesis. The quantification over all such `η` here is what lets
the two interfaces compose.

## Sources and reading

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
  GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical
  Surveys 31:3 (1976), 1–68. Registered source:
  `bernstein-zelevinsky-1976-representations-gln`. Central-Library PDF
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`,
  verified for this pair. Printed pages equal one-based PDF pages.

Passages read directly for this pair on 2026-10-28:

- §§2.30–2.35, pp.24–25;
- §§3.3–3.5, pp.29–30 (partitions into segments, `G_α = ∏ G_{n_i}`);
- §3.18, p.34 (checked visually);
- §§5.1 and 5.5–5.7, pp.44–45;
- §§5.14–5.18, pp.48–50;
- the headings of §6 (p.52) and §7 (p.57), and §7.6 (p.58);
- §§7.11–7.12, pp.60–61. Page 61, which contains step (5), was checked
  visually.

Theorem 5.21 (p.51) was read for the companion statement
`IrreducibleCoinvariantFinitenessStatement`.

On 2026-10-28 the Library notes and wiki, the project literature index and the
Central-Library listing were searched for errata. No erratum or correction for
this source was found.
