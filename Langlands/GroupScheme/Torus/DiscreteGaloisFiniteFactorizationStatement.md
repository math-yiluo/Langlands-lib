# Finite Galois factorization of finitely generated discrete modules

`Langlands.GroupScheme.DiscreteGaloisFiniteFactorizationStatement.{u,v}`
asserts the following. Let `k : Type u` be any field and let `M : Type v` be
an abelian group with its integral module structure, finitely generated over
`ℤ`. Let

```text
ρ : Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) M
```

be the specified actual representation. If `IsSmooth ρ` holds for the Krull
topology, there is an intermediate field `L` of the chosen separable closure,
finite-dimensional and Galois over `k`, and a representation `ρL` of
`L ≃ₐ[k] L` on the **same** module `M`, such that

```text
ρL.comp (AlgEquiv.restrictNormalHom L) = ρ.
```

The homomorphism in this equality is canonical restriction of actual
separable-closure automorphisms to the normal intermediate field. The
existential Galois proof is installed locally to define that restriction.
Equality is equality of representations, so it retains the specified action
on every automorphism and vector, without a change of carrier or a supplied
abstract finite quotient.

The field and module universes are independent. Torsion modules are allowed;
no freeness, torsion-freeness, characteristic or perfectness assumption is
added. `IsSmooth` means that every vector is fixed by an open subgroup. No
topology on `M` is installed: for a discrete module this is the usual
continuity condition, as established by the published discrete-orbit
comparison. The zero module is included.

## Provenance and scope

This is a derived structural statement using the published representation
smoothness predicate, Mathlib's finite-generation predicate, its chosen
separable closure, and its Krull topology and restriction homomorphism. Its
mathematical justification is the elementary finite-generator argument:
finitely many open stabilizers give an open action kernel; the normal Krull
neighborhood basis supplies a finite Galois intermediate field whose fixing
subgroup acts trivially; surjective restriction then descends the action.
These ingredients explain the statement, and are not a submitted Lean proof.
No new external theorem is imported or asserted as proof evidence.

The result is a supporting step for passing between absolute-Galois modules
and finite-Galois realization. It neither constructs a group scheme from the
module nor proves finite splitting of group schemes, an actual character
comparison, full faithfulness or a character anti-equivalence. Those remain
separate mathematical obligations.
