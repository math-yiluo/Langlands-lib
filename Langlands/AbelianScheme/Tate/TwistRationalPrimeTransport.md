# Geometric path transport on rational prime-adic roots-of-unity twists

This internal construction extends the integral prime-adic root path transport
from `ℤ_[p]` to `ℚ_[p]` and proves compatibility with rational extraction from
selected, full and away root systems. It imports `TwistPrimeTransport`,
`TwistRationalTransport` and `TwistRationalPrimeMonodromy`. All declarations
are in `Langlands.TateTwist.Geometry`.

## Inputs and carriers

Fix a scheme `S`, fields `Ω`, `Ω'` and, for composition, `Ω''` in the same
universe, and points `s : Spec Ω ⟶ S`, `t : Spec Ω' ⟶ S`,
`r : Spec Ω'' ⟶ S`. Each point has an explicit finite-fibre hypothesis,
such as `hs : ∀ Y : Cover S, Finite (Fiber s Y)`. A path is a supplied
natural isomorphism `γ : fiberFunctor s hs ≅ fiberFunctor t ht` of the
actual finite-cover fibre functors.

For a natural prime `p`, expressed by `[Fact p.Prime]`, the instance families
`hμfin` and `hμet` require the structural map of the actual scheme
`mu S (p ^ n)` to be finite and étale for every `n : ℕ`, including `n = 0`.
These hypotheses are retained rather than derived from invertibility here.
The conditional construction uses no connectedness or algebraic-closure
assumption and proves no existence of a path.

The existing carrier is
`Rational Ω p = ℚ_[p] ⊗[ℤ_[p]] Integral Ω p`, and similarly at the
other fields. The integral factor consists of coherent actual roots of
unity at prime-power orders with the existing residue scalar action.
The construction chooses no field map, compatible roots, basis or twist
trivialization.

## Scalar extension and path laws

`rationalPrimeTransportMap p γ` is the `ℚ_[p]`-linear map obtained as
`(primeTransportHom p γ).baseChange ℚ_[p]`. Its pure-tensor formula
`rationalPrimeTransportMap_tmul` is

```text
q ⊗ x ↦ q ⊗ primeTransport p γ x.
```

The integral map evaluates the same geometric path on the actual
roots-of-unity covers and then forms the coherent family.
`rationalPrimeTransportMap_refl` first proves equality of the integral
linear map with the identity by linear-map extensionality. Applying
scalar extension to that equality, followed by `LinearMap.baseChange_id`,
proves the rational identity. `rationalPrimeTransportMap_trans` similarly
extends the equality of integral composite maps and uses
`LinearMap.baseChange_comp`. The convention is

```text
T_(γ ≪≫ δ)(x) = T_δ(T_γ(x)).
```

`rationalPrimeTransport p γ` bundles this map into a `ℚ_[p]`-linear
equivalence. Its inverse is the map for `γ.symm`; the inverse equations
follow from composition, cancellation of the path with its reverse, and
the identity law. The lemmas `rationalPrimeTransport_tmul`,
`rationalPrimeTransport_refl`, `rationalPrimeTransport_trans` and
`rationalPrimeTransport_symm` retain the pure-tensor, identity, composition
and inverse formulas for the equivalence.

`primeToRational_transport` states that the canonical map
`TateTwist.toRational Ω p`, given by `x ↦ 1 ⊗ x`, commutes with transport.
This equality holds by reflexivity and does not assert injectivity of the
canonical map.

## Monodromy and dependence on a path

For a loop `g : FundamentalGroup s hs`, `rationalPrimeTransport_aut`
identifies the entire linear equivalence with
`rationalPrimeMonodromy s hs p g`. Its proof takes the underlying linear
maps in the integral identity `primeTransport_aut`, applies scalar
extension, and uses injectivity of `LinearEquiv.toLinearMap`.

`rationalPrimeTransport_monodromy` proves the intertwining identity

```text
T_γ(ρ_s(g)(x)) = ρ_t(pathConjugation γ g)(T_γ(x)).
```

Here `pathConjugation γ` is the existing conjugation of actual geometric
fundamental groups induced by the same natural isomorphism. The proof
forms an equality of composed integral linear maps using
`primeTransport_monodromy`, applies scalar extension, and rewrites its
compatibility with composition.

For two paths `γ, δ` from `s` to `t`,
`rationalPrimeTransport_change_path` proves

```text
T_δ(x) = ρ_t(γ.symm ≪≫ δ)(T_γ(x)).
```

The loop on the right is at the target point. The proof replaces its
monodromy by transport, uses the composition law and cancels the reverse
path. This describes the difference between paths; it does not identify
all path transports.

## Selected, full and away extraction

For `P : ℕ → Prop`, the existing `Index P` comprises positive integers
satisfying `P`. The extraction section assumes finite and étale structural
maps for `mu S n.val` at every such index. A hypothesis
`hP : ∀ n : ℕ, P (p ^ n)` retains all prime powers, including order one.
The prime-side finite/étale instances are exactly the selected instances
restricted along `Divisibility.primePowerIndex P p hP`.

`rationalToPrime_transport` proves

```text
rationalToPrime Ω' P p hP (rationalTransport P γ x)
  = rationalPrimeTransport p γ (rationalToPrime Ω P p hP x).
```

The domain is the existing
`Divisibility.Rational Ω P = ℚ ⊗[ℤ] Divisibility.Integral Ω P`.
The extraction map sends `q ⊗ x` to `(q : ℚ_[p]) ⊗ toPrime Ω P p hP x`.
Tensor induction proves the equality: the pure-tensor case is the
integral compatibility `toPrime_transport` under tensoring with `q`,
and additivity handles sums. `rationalToPrimeSemilinear_transport`
states the same equality for the existing semilinear projection, whose
underlying function is definitionally the same.

`rationalFullToPrime_transport` specializes to `P = True`, taking the
finite/étale families at every positive order explicitly.
`rationalAwayToPrime_transport` specializes to
`P n = Nat.Coprime n m` for any natural modulus `m`, with a hypothesis
`h : Nat.Coprime p m`. Each prime power is retained by `h.pow_left n`,
and the prime-side instances are restricted along those exact indices.
`rationalAwayToPrimeSemilinear_transport` supplies the corresponding
away semilinear wrapper. A separately named full semilinear wrapper is
not introduced; the selected theorem can be specialized to `P = True`.
These are compatibility identities, not assertions that the extraction
maps are isomorphisms.

## Provenance and scope

This is an internal derivation from the integral prime-adic transport,
rational root carriers, geometric monodromy and rational extraction
maps. The implemented proof routes are described above. No new theorem
is attributed to external literature.

The result is algebraic. It introduces no topology or continuity on the
rational prime-adic carrier, no new rank or comparison-isomorphism
theorem, and no pointed base-change or pairing compatibility. Path
existence and canonical independence of PEL fixed-orbit sets remain
separate obligations. This unit does not claim completion of the parent
PEL infrastructure task.
