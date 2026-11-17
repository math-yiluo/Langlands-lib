# Finite Galois factorization of discrete integral representations

`Langlands.GroupScheme.discreteGaloisFiniteFactorization.{u,v}` proves the
exact Library statement
`Langlands.GroupScheme.DiscreteGaloisFiniteFactorizationStatement.{u,v}`.

## Result

Let `k : Type u` be a field and `M : Type v` a finitely generated module over
`ℤ`. Let

```text
ρ : Representation ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) M
```

be a representation that is smooth for the Krull topology. Then the proof
gives an intermediate field `L` of `SeparableClosure k`, finite-dimensional
and Galois over `k`, and a representation `ρL` of `L ≃ₐ[k] L` on the same
module `M` such that

```text
ρL.comp (AlgEquiv.restrictNormalHom L) = ρ.
```

The universes `u` and `v` are independent. The module may have torsion or be
zero. No other hypothesis is used.

## Proof

1. **Open kernel.** The published theorem
   `Langlands.Shimura.ContinuousGaloisAction.exists_openSubgroup_le_ker`
   applies to `ρ`, because `ρ` is smooth and `M` is finitely generated. It
   gives an open subgroup `U` of the absolute Galois group with
   `U ≤ ρ.ker`. In that proof, `U` is the intersection of the open
   stabilizers of finitely many generators.

2. **Finite Galois intermediate field.** `SeparableClosure k` is normal over
   `k`, and `U` is a neighborhood of `1`. So Mathlib's
   `krullTopology_mem_nhds_one_iff_of_normal` gives an intermediate field `L`
   that is finite-dimensional and normal over `k`, and whose fixing subgroup
   is contained in `U`. `L` is separable over `k` because it lies inside the
   separable closure, so the instance `IsGalois k L` is built from the
   normality and separability instances.

3. **Restriction.** Let `f = AlgEquiv.restrictNormalHom L`. It is surjective
   by `AlgEquiv.restrictNormalHom_surjective`. By
   `IntermediateField.restrictNormalHom_ker`, its kernel is the fixing
   subgroup of `L`. So the kernel of `f` lies in `U`, and therefore in the
   kernel of `ρ`. The proof records this for `ρ.asGroupHom`, the
   representation seen as a homomorphism into the units of
   `Module.End ℤ M`. To show that `σ` is in the kernel of `ρ.asGroupHom`, it
   applies `Units.ext` and reduces to `ρ σ = 1`.

4. **Descent.** Mathlib's `MonoidHom.liftOfSurjective f hf` turns
   `ρ.asGroupHom` and the kernel inclusion into a homomorphism
   `τ : (L ≃ₐ[k] L) →* (Module.End ℤ M)ˣ` with `τ (f σ) = ρ.asGroupHom σ`. The
   representation `ρL` is `τ` followed by `Units.coeHom`. It acts on the same
   module `M`.

5. **Equality.** The two sides are compared with `MonoidHom.ext`. At an
   automorphism `σ`, the left side is the coercion of `τ (f σ)`. The lemma
   `MonoidHom.liftOfRightInverse_comp_apply` rewrites it to
   `ρ.asGroupHom σ`, and `Representation.asGroupHom_apply` turns that into
   `ρ σ`.

## Provenance and scope

This is a derived proof. It uses the published open-kernel theorem above and
Mathlib's Krull topology, restriction and homomorphism-lifting results. It
introduces no external assertion and no new hypothesis. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

The proof was first drafted by Worker 3483 as the shared draft of this task.
Worker 4767 checked it and submitted it, replacing the local instance `let`
bindings by `have` and rewriting this Markdown.

The theorem does not construct a group scheme. It does not prove finite
splitting of multiplicative-type groups, finite-Galois realization, full
faithfulness, or a character anti-equivalence.
