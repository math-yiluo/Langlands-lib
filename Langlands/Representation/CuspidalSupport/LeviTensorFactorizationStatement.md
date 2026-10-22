# Small-universe tensor exhaustion for cuspidal standard Levis

Author: Worker 82.

`Langlands.CuspidalSupport.PadicLeviCuspidalFactorizationStatement.{uF,uW,uV}`
is a closed proposition definition. It is a derived theorem target; this pair
proves neither tensor factorization nor existence of small realizations.

## Exact statement and constructions

For every prime `p`, every actual finite extension `F : PadicField.{uF} p`,
every `T : F.TopologicalData`, every positive integer `n`, and every ordered
block shape `B : GeneralLinear.BlockShape n`, install `T.topology`. For any
`σ : SmoothRep.{0,uF,uW} ℂ (B.Levi F.Carrier)` that is irreducible and satisfies
`IsLeviCuspidal B σ.representation`, there exists a family

```text
A : ∀ i : Fin B.length,
  GeneralLinear.SupercuspidalRep.{uF,uV}
    (F := F.Carrier) (n := B.size i)
```

and a genuine representation equivalence from `σ.representation` to
`B.blockTensor (fun i => (A i).obj.representation)`. The equivalence is asserted
by `Nonempty`; no particular choice is required.

`B.Levi F.Carrier` is the actual product of the general linear groups for the
positive block sizes, with the product topology induced from `T.topology`.
`BlockFactors.blockTensor` reuses the finite algebraic tensor representation:
a tuple of block matrices acts on a pure tensor by acting separately on its
factors. The right-hand carrier is the actual `PiTensorProduct` over `ℂ`, not
a supplied representation or abstract factorization package.

The imported `IsLeviCuspidal` means admissibility together with vanishing of
the actual unipotent coinvariant quotients for every proper standard block
refinement. Admissibility includes smoothness. The imported
`SupercuspidalRep` packages a smooth irreducible block representation satisfying
`GeneralLinear.IsSupercuspidal`: admissibility and zero coinvariants for every
proper standard block parabolic and every conjugate of its unipotent radical.
Irreducibility excludes zero. The conclusion therefore asserts the actual
irreducibility, admissibility, and conjugate-radical vanishing of each factor.

The field universe `uF`, source-carrier universe `uW`, and factor-carrier
universe `uV` are independent. In particular the factors are in `uV`, not
`max uF uV` or `uW`. One may specialize `uW` to `max uF uV`, as required by
normalized parabolic induction, without changing the requested factor universe.
`Representation.Equiv` supplies an actual equivariant complex-linear
isomorphism across these carrier universes. There is no cardinal-bound,
smallness, or shrinking-equivalence hypothesis. Positivity of `n` excludes
the empty partition; a single block is allowed.

## Source correspondence

The following retained originals were read directly on 2026-10-21.

- D. Flath, *Decomposition of representations into tensor products*, Proc.
  Sympos. Pure Math. 33, Part 1 (1979), Theorem 1(1.2), printed p.179, and its
  proof, p.180 (one-based PDF pages 175–176). Source ID:
  `flath-1979-tensor-products`; retained file:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`;
  SHA-256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
  This gives admissible irreducible factorization for a product of two locally
  compact totally disconnected groups. Finite iteration supplies the product
  case here. Its uniqueness conclusion is outside this statement.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), sections 2.2, 2.4 and 2.7, printed pp.446–447
  (PDF pages 7–8). Source ID: `bernstein-zelevinsky-1977-induced-i`; retained
  file: `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`;
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Section 2.2 identifies standard Levis with products and standard subgroups
  with refinements; section 2.4 defines quasicuspidality and cuspidality;
  section 2.7 uses tensor factors for representations of these Levis. Section
  2.7 alone is not being cited as a proof of the small-universe exhaustion.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980), section 1.10, printed
  p.174 (PDF page 11). Source ID: `zelevinsky-1980-induced-ii`; retained file:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`;
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  The first paragraph explicitly relates quasicuspidality of a nonzero
  external tensor product to quasicuspidality of every factor. No multisegment
  classification or support uniqueness assertion is included here.

The published `Langlands.AdmissibleProductFactorizationStatement` in
`Representation.Smooth.Factorization.TwoFactorStatement` is an existing
proposition target for Flath's two-factor result, not a proved theorem. It
provides factors in the original representation-carrier universe. Neither its
truth nor a change of universe is assumed by the present statement.

## Derived small-realization rationale and proof obligations

The universe reduction is additional derived content, not a claim that the
cited papers identify Lean universes. A concrete mathematical route is as
follows; formal implementation of all these steps remains outstanding.

1. Apply finite iteration of admissible product factorization to the actual
   product Levi. The p-adic block groups have the Hausdorff, locally compact,
   totally disconnected topology required by Flath. Construct the product
   reindexing and tensor associativity equivalences, including the one-block
   case, so that the resulting action is exactly `B.blockTensor`.
2. Each factor is nonzero, smooth, admissible, and irreducible. Under the
   factorization equivalence, Levi quasicuspidality forces standard Jacquet
   vanishing in each block. One can isolate a proper parabolic in a single
   block and use the coinvariant tensor formula: the other nonzero factors
   detect vanishing of the selected factor's quotient. Normalization does not
   change whether the underlying quotient is zero. Transport by the action
   of a conjugating block matrix identifies coinvariants for conjugate
   radicals. Together with admissibility this yields the imported
   `IsSupercuspidal` predicate, including its conjugate tests.
3. The topology in `F.TopologicalData` is certified to be the canonical
   finite-dimensional `ℚ_p`-module topology. A finite basis identifies it
   topologically with a finite power of `ℚ_p`, a second-countable space.
   Finite matrix spaces, their general linear groups, and finite products
   of these groups are consequently second countable. This argument concerns
   the given topology even when the carrier of `F` lies in a large universe.
4. In any nonzero irreducible smooth complex representation of one of these
   groups, choose a nonzero vector `v`. Its stabilizer `K` is open. The
   disjoint open cosets in `G/K` are a countable family in a second-countable
   space, so the orbit of `v` is countable. The linear span of the orbit is
   a nonzero invariant subspace and hence the whole representation. Thus
   its dimension is at most countable. No countability of the set of
   complex scalars or of the group itself is needed.
5. Extract a basis from that countable spanning set and index it by a subset
   `I` of `ℕ`. The finite-support function space `I →₀ ℂ` has a carrier in
   `Type 0`. Lift this carrier to `Type uV` and transport the original action
   along the resulting complex-linear equivalence. This constructs an actual
   representation in the requested independent universe. Transfer smoothness,
   irreducibility, admissibility, and Jacquet vanishing along the equivalence;
   then tensor the factor equivalences and compose with the factorization
   equivalence from step 1.

Alternatively admissibility and a countable cofinal family of compact open
subgroups give a countable union of finite-dimensional fixed spaces. Neither
route supplies an assumed bound in the Lean statement. The statement asserts
the existence of these realizations as part of its conclusion.

This pair imports the existing `CuspidalSupport.LeviDefinitions`,
`Classification.Supercuspidal`, and `Induction.BlockFactors` without changing
their Lean or Markdown. It is complementary to forward tensor
irreducibility/cuspidality and permutation association; it asserts only
exhaustion. Compilation and complete declaration inspection establish that
this is a well-formed closed proposition. Independent semantic review and
publication are required, followed by a separate proof of this exact target.
