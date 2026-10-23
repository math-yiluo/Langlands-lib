# Integral Tate transport along actual geometric paths

Author: Worker 142.

This module extends the published finite-level construction along a given
isomorphism of the actual geometric fibre functors to the existing integral
Tate limits. It constructs an additive homeomorphism, profinite scalar
linearity, homomorphism naturality, and compatibility with actual monodromy.
The full and away versions retain their existing carriers and topologies.

## Sources and derived provenance

The construction follows the conventions in these originals:

- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
  (2001), Chapter I, printed p.18 / PDF p.26: the full limit over positive
  torsion orders and the away limit over orders prime to the excluded primes.
  Registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
- Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary version built
  2012-02-08, Chapter X §3, Definitions (10.25)–(10.26), printed p.150 /
  PDF p.154, and (10.29), printed p.151 / PDF p.155: the actual finite étale
  fibre functors and noncanonical change of geometric base point. Registered
  source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
  `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

These source passages were read directly in their original PDF extractions;
no corresponding errata note was found in the available Library. The Lean
API and its proofs are **derived** from the imported `FiniteTransport`,
`IntegralMonodromy`, and actual Tate-limit definitions. The arbitrary selected
predicate is an internal generalization. Neither original is claimed to print
this precise API or supply its Lean proof. The named geometric theorem
hypotheses below remain explicit and are not proved here.

## Exact inputs

Fix a scheme `S`, an actual `A : AbelianScheme S`, two field-valued points
`s : Spec (.of Ω) ⟶ S`, `t : Spec (.of Ω') ⟶ S`, and finite-fibre proofs
`hs : ∀ Y : Cover S, Finite (Fiber s Y)` and `ht` at `t`. The path is
`p : fiberFunctor s hs ≅ fiberFunctor t ht`. These are the actual finite
étale categories and geometric point functors, not arbitrary replacement
modules or actions. Different fields are allowed in the same universe. A
third field and point occur in the composition law.

For a predicate `P : ℕ → Prop`, `Index P` consists of orders satisfying
`0 < n` and `P n`. The theorem dependencies are

```lean
htor : TorsionFiniteEtaleStatement
hu : ∀ n : Index P, IsUnit (n.val : Γ(S, ⊤))
```

Thus every selected actual multiplication kernel is finite étale, by the
explicit input `htor` at a positive invertible order. No closure property of
`P` is required for this coordinatewise construction. The intended geometric
setting has algebraically closed coefficient fields and connected locally
noetherian `S`; the conditional evaluation arguments do not need these extra
hypotheses. This module asserts neither path existence nor the geometric
Galois-category theorem.

## Construction and composition

All declarations lie in `Langlands.AbelianScheme.Tate`.
`integralTransportHom htor A P hu p` uses the existing limit constructor
`lift`. Its coordinate at `n` is `levelTransport htor A n.val n.property.1
(hu n) p` applied to the existing evaluation at `n`. The finite transport
transition law and the input family's coherence prove that the resulting
family is coherent. The additive homomorphism structure is inherited from
this construction. `evaluation_integralTransportHom` gives its exact
coordinate formula.

`integralTransportHom_refl` and `integralTransportHom_trans` follow by
extensionality and their finite-level counterparts. In particular,
`p ≪≫ q` first transports along `p` and then along `q`.
`integralTransport` bundles the homomorphism as an additive equivalence, with
reverse path `p.symm` as inverse. The two inverse laws use the composition
law, the identities for a natural isomorphism and its inverse, and the
identity-path law.

`evaluation_integralTransport`, `integralTransport_refl`,
`integralTransport_trans`, and `integralTransport_symm` expose the same
coordinate, identity, composition, and reverse-path properties.
`integralTransport_aut` identifies transport along a loop with the existing
`integralMonodromy`. The equality uses the same actual finite-level
evaluation construction, not a comparison with an unspecified action.

## Topology and scalars

The source and target carry the already published product-subspace topologies
on their coherent families of discrete torsion points.
`continuous_integralTransport` applies the existing
`GroupScheme.Tate.continuous_iff_evaluation`: each output coordinate is the
composition of a continuous finite-level transport with a continuous input
evaluation. Applying the same theorem to the reverse path gives inverse
continuity. `integralTransportHomeomorph` bundles the result as an additive
topological equivalence `≃ₜ+`. No change of topology, rationalization topology,
or independent compactness argument is introduced.

`integralTransport_full_smul` proves compatibility with the existing
`Global.ProfiniteIntegerRing` action. At coordinate `n` this is the
finite-level `ZMod n` scalar law, evaluated at `fullReduction P n a`.
`integralTransportLinearEquiv` bundles that same additive equivalence over
the full profinite-integer ring.

## Naturality and monodromy

`integralTransport_map` states naturality for an actual abelian-scheme
homomorphism `f : A ⟶ B`: applying the existing Tate map at `s` and then
transporting on `B` equals transporting on `A` and applying the Tate map at
`t`. Coordinate extensionality reduces it to `levelTransport_map`.

`integralTransport_monodromy` intertwines the actual monodromy actions at
`s` and `t` using the same `pathConjugation p` constructed from the path.
`integralTransport_change_path` states, for paths `p,q` from `s` to `t`,

```text
transport(q)(x) = monodromy_t(p.symm ≪≫ q)(transport(p)(x)).
```

Both proofs reduce coordinatewise to the corresponding finite-level laws.
The latter identity records the exact dependence on the chosen path. It
does not assert equality of transports for arbitrary paths or yet construct
a fixed-orbit quotient on which they agree.

## Full and away specialization

`fullTransport` uses `P n := True` and requires invertibility of every positive
order. `awayTransport m` uses `P n := Nat.Coprime n m` and only requires the
retained positive orders to be invertible. These abbreviations use the
existing full and away Tate carriers. No primality assumption on `m` is
required; the prime-to-`p` application takes `m = p`.

`awayTransport_smul` proves compatibility with the existing
`Global.PrimeToProfiniteIntegerRing m` action using `awayReduction m n a`
and the finite residue scalar law. `awayTransportLinearEquiv` bundles it over
that ring. Both full and away transport inherit the generic continuity,
inverse, composition, and monodromy laws by specialization.

`restrictAway_transport` states that full-to-away restriction commutes with
transport along the same path. Its away invertibility family is explicitly
the restriction of the full family, and the identity is definitional on each
retained coordinate.

Rational or adelic transport, pointed base change, Weil pairings, path
existence, and independence of the invariant level-orbit set remain separate
constructions or obligations. In particular, this module does not claim a
canonical unpointed PEL functor.
