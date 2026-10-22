# Finite admissible tensor factorization for standard p-adic Levis

Author: Worker 278.

`Langlands.CuspidalSupport.PadicLeviAdmissibleFactorizationStatement.{uF,uW}`
is a closed proposition definition. It is a derived theorem target. This pair
does not prove the factorization, and it assumes no two-factor theorem.

## Exact statement and constructions

For every prime `p`, every actual finite extension `F : PadicField.{uF} p`,
every `T : F.TopologicalData`, every positive integer `n`, and every ordered
block shape `B : GeneralLinear.BlockShape n`, install `T.topology`. Let
`σ : SmoothRep.{0,uF,uW} ℂ (B.Levi F.Carrier)` be irreducible and admissible,
that is, `σ.IsIrreducible` and `σ.IsAdmissible`. Then there exists a family

```text
A : ∀ i : Fin B.length,
  SmoothRep.{0,uF,uW} ℂ (GeneralLinear (B.size i) F.Carrier)
```

such that every `(A i).IsIrreducible`, every `(A i).IsAdmissible`, and there is
a representation equivalence

```text
σ.representation.Equiv (B.blockTensor (fun i => (A i).representation)).
```

The equivalence is asserted by `Nonempty`; no particular choice is required.
These two hypotheses are the only hypotheses on `σ`.

The constructions are the existing Library ones, used by Lean name.

- `B.Levi F.Carrier` is the actual product type
  `∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier`. Each factor is
  Mathlib's group of units of the matrix ring, with the units topology of the
  entrywise matrix topology from `T.topology`. The Levi has the product
  topology; this is the same topology as `T.leviTopology B`. No block-diagonal
  embedding into `GL_n` enters the statement.
- `SmoothRep.{0,uF,uW}` is the full subcategory of Mathlib's `Rep` cut out by
  smoothness. Its carriers lie in `Type uW`. `SmoothRep.IsIrreducible` is
  Mathlib's `Representation.IsIrreducible`, which excludes the zero
  representation. `SmoothRep.IsAdmissible` is the published
  `Langlands.IsAdmissible`: smoothness together with finite-dimensional fixed
  spaces for every open subgroup.
- `BlockShape.blockTensor` is `FiniteTensor.external`. Its carrier is Mathlib's
  `PiTensorProduct ℂ` of the factor carriers. A tuple `m` of block matrices acts
  on a pure tensor `⨂ v i` by `⨂ (A i)(m i)(v i)`. It is a constructed
  representation, not a supplied tensor decomposition or factorization
  package.

## Universes and scope

The field universe `uF` and the carrier universe `uW` are independent. The
factors lie in the same carrier universe `uW` as `σ`. This pair is the
same-universe finite factorization. Factors in an independently prescribed
smaller universe belong to the parent
`Langlands.CuspidalSupport.PadicLeviCuspidalFactorizationStatement` and to the
small-realization statement and proof task (`baca19e0-4b51-4368-9b1a-817f6d583c5f`).
Positivity of `n` excludes the empty block shape. Indeed, the block sizes are
positive and sum to `n`, so `B.length ≥ 1`. The one-block case
`B.length = 1` is included.

The statement has no cuspidality assumption. It also has no supplied tensor
decomposition, local-finiteness hypothesis, cardinal bound, or shrinking
premise. Its conclusion asserts no cuspidality and no uniqueness of factors.
The parent's hypothesis `IsLeviCuspidal B σ.representation` contains
admissibility as its first conjunct. An irreducible cuspidal source therefore
satisfies the present hypotheses.

## Source correspondence

The following retained originals were read directly on 2026-10-22.

- D. Flath, *Decomposition of representations into tensor products*, Proc.
  Sympos. Pure Math. 33, Part 1 (1979), pp.179–183. Source ID:
  `flath-1979-tensor-products`; retained file:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`;
  SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
  Theorem 1, clause (1.2), printed p.179 (one-based PDF page 175), states the
  following for locally compact totally disconnected `G₁`, `G₂` and
  `G = G₁ × G₂`. Every admissible irreducible `π` of `G` is isomorphic to
  `π₁ ⊗ π₂` for admissible irreducible representations `πᵢ` of `Gᵢ`. The
  proof, printed p.180 (PDF page 176), uses Hecke algebras of compact open
  subgroups `K₁ × K₂`. It obtains each factor as an inductive limit of
  irreducible Hecke-algebra modules. Flath states only the two-factor case.
  His uniqueness assertion is outside this pair.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977). Source ID: `bernstein-zelevinsky-1977-induced-i`;
  retained file:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`;
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Section 2.2, printed p.446 (PDF page 7), takes `G = GL(n,F)` with the
  upper-triangular minimal parabolic and the diagonal torus. It numbers the
  standard subgroups by ordered partitions `α = (n₁,…,n_r)` of `n`. The
  subgroup for `α` is `G_α = G_{n₁} × ⋯ × G_{n_r}`, embedded as the
  block-diagonal ("cellular-diagonal") matrices. Section 2.1 on the same page
  says that groups of `F`-points carry a natural locally compact topology
  making them `l`-groups. `BlockShape` is such an ordered partition. The
  Library's `B.Levi` is the abstract product `G_α` itself, not its
  block-diagonal image.

## Derived content: finite iteration of Flath's theorem

The finite-product form is derived content. It does not translate a single
printed theorem. It is obtained by finite iteration of Flath's two-factor
Theorem 1(1.2) along the actual product decomposition of BZ77 section 2.2.
The two-factor input is the published
`Langlands.AdmissibleProductFactorizationStatement.{uG₁,uG₂,uV}` in
`Langlands.Representation.Smooth.Factorization.TwoFactorStatement` (author
Worker 44). That pair is a proposition target, not a proved theorem. Its exact
proof is requested by task `ea7e032e-0818-4425-9fc4-6f30126f4fc4`, revision 2.
Its factors lie in `ModuleCat.{uV} ℂ` with `uV` the source carrier universe.
This is what keeps every iterated factor in `uW`.

The present pair does not import that two-factor pair. Its Lean statement
neither assumes nor mentions it. A two-factor proposition is not a proof. A
later proof of this exact target must use a proved and published closing
theorem of the two-factor statement, or prove that content itself. It must not
take `AdmissibleProductFactorizationStatement` as a hypothesis or assume the
desired finite factorization. It must not use forward tensor irreducibility
or admissibility (Flath (1.1), `AdmissibleExternalTensorStatement`) as a
substitute for existence.

A mathematical route is as follows. Its formal implementation remains
outstanding; the identifications below are retained proof obligations, not
facts asserted by this pair.

1. **Topological hypotheses.** For `T.topology`, each `GL_m(F)` and each finite
   product of them must be a Hausdorff, locally compact, totally disconnected
   topological group. The Library already provides
   `PadicField.TopologicalData.generalLinearTopologicalGroup`,
   `generalLinearT2Space` and `generalLinearLocallyCompactSpace`, together with
   the Levi versions `leviTopologicalGroup`, `leviT2Space` and
   `leviLocallyCompactSpace`. Total disconnectedness of these groups is not
   yet a named Library result and remains to be proved.
2. **Continuous group reindexing.** For `B.length = r + 1`, construct a
   topological group isomorphism between `B.Levi F.Carrier` and the product
   `GL_{n₀}(F) × ∏_{j<r} GL_{n_{j+1}}(F)`, which separates the first block
   from the rest. Pull `σ` back along it. Pullback along a topological group
   isomorphism preserves smoothness, admissibility (open subgroups
   correspond), and irreducibility.
3. **Two-factor step and induction.** Apply the proved two-factor theorem to
   the pulled-back representation. The first factor is an admissible
   irreducible representation of `GL_{n₀}(F)`. The second factor is an
   admissible irreducible representation of the product of the remaining `r`
   blocks, so the induction hypothesis on the number of blocks applies to it.
   Irreducibility of each factor comes from Flath's existence clause, not
   from the forward tensor direction. The two-factor result produces
   `ModuleCat` carriers with `Representation` data; these are repackaged as
   `SmoothRep` objects, smoothness being part of admissibility.
4. **Tensor associativity.** Identify `V₀ ⊗ (⨂_{j<r} V_{j+1})` with the
   `PiTensorProduct` over `Fin (r + 1)`. Mathlib's `PiTensorProduct.reindex`,
   `PiTensorProduct.tmulEquivDep` and the `Fin`/`Sum` index equivalences are
   available ingredients. The identification must intertwine the external
   action of the two-factor product with the `FiniteTensor.external` action.
   Dependent block sizes `B.size i` must be handled along the index
   reindexing.
5. **One-block action equivalence.** For `B.length = 1`, identify
   `B.Levi F.Carrier` with `GL_{n}(F)` through evaluation at the unique index.
   Identify the `PiTensorProduct` over `Fin 1` with the single factor, for
   example by `PiTensorProduct.subsingletonEquiv`. Show that this is an
   equivalence of representations from `σ` to `B.blockTensor` of the single
   pulled-back factor. This base case needs no two-factor theorem.
6. **Assembly.** Compose the pullback equivalence, the two-factor
   equivalence, the tensor of the inductive equivalences with the identity,
   and the associativity equivalence. The target must be exactly
   `B.blockTensor (fun i => (A i).representation)` for the constructed
   family `A`.

The project's all-open-subgroups admissibility convention differs from Flath's
compact-open one. Bridging the two conventions belongs to the two-factor proof,
as its own Markdown explains. Steps 2–6 then use only the project convention.
If any of steps 1–5 needs a substantial reviewed construction, the proof
worker should publish it as a separate definition or statement task first.

## Dependencies and remaining scope

The only import is the published
`Langlands.Representation.Induction.BlockFactors`. It supplies
`BlockShape.blockTensor` and, transitively, `SmoothRep`,
`SmoothRep.IsIrreducible`, `SmoothRep.IsAdmissible`, `BlockShape.Levi`,
`PadicField` and `PadicField.TopologicalData`. None of these files is
changed. The environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.

The immediate consumer is the exhaustion proof task
`334e2222-c3e9-47e3-b05c-2afe12f49e94` for
`PadicLeviCuspidalFactorizationStatement`. That proof must still derive
factorwise supercuspidality and independently smaller carriers. Neither is
asserted here. Compilation and complete declaration inspection show only that
this is a well-formed closed proposition with level parameters `uF`, `uW`.
Independent semantic review and publication are required, followed by a
separate proof of this exact target.
