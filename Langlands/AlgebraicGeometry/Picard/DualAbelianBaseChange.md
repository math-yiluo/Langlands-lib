# Conditional canonical base change of dual abelian schemes

`dualAbelianBaseChangeIso` constructs an isomorphism from the actual base
change of the constructed dual abelian scheme to the constructed dual of the
base-changed abelian scheme. It takes an explicit proof of
`DualAbelianBaseChangeStatement`. The two duals are exactly
`dualAbelianSchemeFromEvaluation` with their supplied universal-family,
geometry and inverse/evaluation inputs. All seven construction theorem
inputs and the separate universal-family base-change theorem input remain
explicit.

The construction chooses the witness asserted by that statement.
`dualAbelianBaseChangeIso_hom` extracts its exact equality with
`dualSchemeBaseChangeIso` as a morphism in `Over S'`. Thus this is the lift
of the Poincare-compatible canonical comparison; its underlying map is
prescribed on the schemes themselves and on every test scheme.

`dualAbelianBaseChangeIso_unique` proves uniqueness of any lift with that
underlying map. The proof reduces equality of isomorphisms to equality of
forward homomorphisms and uses injectivity of the additive wrapper and
extensionality of group-object homomorphisms. It claims no uniqueness of
bundle evaluation isomorphisms or inverse bundle witnesses.

For a homomorphism `lam : A → A^dual`, `dualAbelianBaseChangeMap` first
applies the actual abelian-scheme base-change functor to `lam`, then composes
with the forward canonical comparison. The result is a genuine
homomorphism `A_{S'} → (A_{S'})^dual`. Its `_hom` lemma proves that
forgetting the group structure gives exactly `dualBaseChangeMap`, the
scheme map already used in the ample Mumford presentation and field
polarization predicates. The proof expands the composition and rewrites
by the comparison's underlying-map equality.

## Internal provenance and scope

This file extracts the witness and its prescribed-map property from the
separately stated group-compatibility obligation and composes it with the
existing base-change functor. It introduces no geometric theorem. The
bases are arbitrary schemes in one universe; the actual duals and their
geometric properties are explicit premises. The named compatibility
statement is an assumption here, not proved by choosing its witness.
Unconditional dual existence, geometric properties, base-change
universality, the compatibility statement itself, independence from the
inverse/evaluation choices, and coherence for successive base changes
are not established by this file.
