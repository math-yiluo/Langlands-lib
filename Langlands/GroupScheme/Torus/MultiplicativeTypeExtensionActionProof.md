# Proof: connected groups act trivially on central extensions of multiplicative type

`Langlands.GroupScheme.multiplicativeTypeExtensionAction` proves the Library statement
[`MultiplicativeTypeExtensionActionStatement`](MultiplicativeTypeExtensionActionStatement.md):

```lean
theorem multiplicativeTypeExtensionAction : MultiplicativeTypeExtensionActionStatement.{u}
```

The statement is Milne, *Algebraic Groups* (2017), Corollary 12.41 (p.244), in the corrected
form of the author's errata: `N` is central. Let `G` be a connected algebraic group over a
field `k`. Let `H` be an algebraic group with a closed central subgroup `j : N ⟶ H` and an fppf
quotient `p : H ⟶ Q` by `N`, where `N` and `Q` are of multiplicative type. Then every action of
`G` on `H` by group automorphisms that preserves `N` is trivial. The module adds no definitions
and no axioms. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Inputs

- `diagonalizableRigidity : DiagonalizableRigidityStatement.{u}`
  ([`Torus.DiagonalizableRigidityProof`](DiagonalizableRigidityProof.md)): rigidity of
  homomorphism families between diagonalizable groups (Milne, Theorem 12.36).
- From [`Torus.MultiplicativeTypeExtensionActionReduction`](MultiplicativeTypeExtensionActionReduction.md)
  (namespace `MultiplicativeTypeExtensionAction`): `act_comp_eq`, `act_comp_quotient`,
  `quasiCompact_quotient`, `homFamily_eq` and `act_eq_of_difference`. Each rigidity lemma
  there takes the rigidity proposition as the hypothesis `hRig`. Through `homFamily_eq` these
  lemmas use `HomFamily.eq_one_of_multiplicativeType`
  ([`Torus.MultiplicativeTypeHomFamily`](MultiplicativeTypeHomFamily.md)). That lemma combines
  `IsMultiplicativeType.exists_common_splitting`
  ([`Torus.MultiplicativeTypeCommonSplitting`](MultiplicativeTypeCommonSplitting.md)) with
  `HomFamily.eq_one_of_commonSplitting` ([`Torus.HomFamilyFieldRigidity`](HomFamilyFieldRigidity.md)).
- `AutomorphicAction.centralDifference` and its lemmas
  ([`AutomorphicAction.CentralDifference`](../AutomorphicAction/CentralDifference.md)): the
  difference family `ψ : G × Q → N` obtained by descending `(g, x) ↦ x⁻¹ (g · x)` along `G × p`.

## Proof

After introducing all hypotheses, let `hRig := diagonalizableRigidity`.

1. **`G` fixes `N` and acts trivially on `Q`.** `act_comp_eq` gives
   `hNfix : a.act g (n ≫ j) = n ≫ j` for all points `n` of `N`. `act_comp_quotient` gives
   `hQfix : a.act g x ≫ p = x ≫ p` for all points `x` of `H`. These are Milne's two
   applications of Corollary 12.37, to `N` and to `H/N`.
2. **Instances for the descent.** `j.hom.hom` is a monomorphism, because the closed immersion
   `j.hom.hom.left` is one (`Over.mono_of_mono_left`). `Q` is affine
   (`IsMultiplicativeType.isAffine`), so `p` is quasi-compact (`quasiCompact_quotient`). `p` is
   flat and surjective by the first two components of the fppf-quotient hypothesis `hp`. The
   fourth component `hp.2.2.2` says that the kernel of `p` has the same points as
   `range j`.
3. **The difference family.** Let
   `ψ := AutomorphicAction.centralDifference a j p hp.2.2.2 hQfix hNfix : G.X ⊗ Q.X ⟶ N.X`.
4. **Closing step.** Apply `act_eq_of_difference a ψ`. It leaves two goals.
   - *Difference formula.* `lift_centralDifference_comp` says
     `(lift g (x ≫ p) ≫ ψ) ≫ j = x⁻¹ * a.act g x`. After reassociating, the goal
     `a.act g x = x * (lift g (x ≫ p) ≫ ψ ≫ j)` becomes `a.act g x = x * (x⁻¹ * a.act g x)`.
     This holds by `mul_inv_cancel_left`.
   - *Rigidity of `ψ`.* The family `(T, g, q) ↦ lift g q ≫ ψ` is a homomorphism family `Q → N`
     parametrized by `G` (`HomFamily.IsHomFamily`). It is multiplicative in `q` by
     `centralDifference_mul`, which uses centrality `hc` of `j`. It is natural in the test
     object by `comp_lift`. Then `homFamily_eq` gives `lift g q ≫ ψ = lift 1 q ≫ ψ`. This
     is Milne's application of Theorem 12.36, after extending scalars to a common splitting
     field of `N` and `Q`.

The hypothesis that `H` is locally of finite type is not used. Quasi-compactness of `H` is used
only to make `p` quasi-compact.

## Relation to the source

Milne's proof reads: "Corollary 12.37 shows that the action of G on H factors through an
action G × H/N → H, and then through an action G × H/N → N. Theorem 12.36 now shows that this
action is trivial." Step 1 is the first sentence. Step 3 is the factorization through
`G × H/N → N`. The kernel inclusion is central, so this factorization is a family of
homomorphisms `H/N → N`. Step 4 is the second sentence. Milne's affineness convention is not
used, as explained in the statement's Markdown.
