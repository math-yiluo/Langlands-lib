# Proof of the actual simultaneous-basis Jacquet adapter

Author: Worker 4067.

`Langlands.BruhatTits.SpecialCompact.simultaneousBasisJacquetAdapter` proves
the published proposition
`Langlands.BruhatTits.SpecialCompact.SimultaneousBasisJacquetAdapterStatement.{u}`
from [`JacquetAdapterStatement`](JacquetAdapterStatement.md) exactly, at an
arbitrary universe `u`. The theorem has no hypotheses. Its type is the whole
unapplied proposition. The statement pair and its imported closure are
unchanged.

## What is proved

Fix a nonarchimedean local field `F` of either characteristic, an actual
connected reductive group scheme `G` over `Spec F`, a maximal split torus
inclusion `i : S.toGrp ⟶ G` and a generic cocharacter `ν`. Fix any subgroup
`K0` of `G(F)` with `SimultaneousStandardBasisAt i ν K0`. Then for every
`J ⊆ simpleRelativeRoots i ν`, the existing
`Langlands.Jacquet.HasIwahoriContractionBasis` holds for the actual standard
radical `standardUnipotentPoints i ν J`, the actual standard Levi
`standardLeviPoints i ν J` and the actual opposite radical
`standardOppositeUnipotentPoints i ν J`. The topology on `G(F)` is
`rationalPointTopology F G.X`. Every rank is allowed, including an empty set of
simple roots. Both `J = ∅` and `J` equal to all simple roots are allowed.

Concretely, every open subgroup `L` of `M_J(F)` gets two things. The first is a
compact open subgroup `K` of `G(F)` with `K.comap M_J.subtype ≤ L`. The second
is an actual element `g` of `G(F)` with all seven fields of
`IsIwahoriContraction K N_J M_J Nbar_J g`: `mem_levi`, `factor`, `upper`,
`levi`, `lower`, `exhaust` and `contract`. The `contract` field is the uniform
opposite contraction into every open subgroup of `G(F)`, as stated in the
existing predicate.

## Implemented proof

The proof is a composition of two published theorems. It adds no premise.

1. `Langlands.GroupScheme.standardCocharacter :
   StandardCocharacterStatement.{u}` (module
   `Langlands.GroupScheme.Rational.StandardCocharacterProof`) is unconditional.
   It holds over every field, so in particular over `F`. For the given `G`,
   `i`, generic `ν` and `J`, its existence clause gives an actual cocharacter
   `zeta` of `S` with `IsStandardCocharacter i ν J zeta`. That is, `zeta` has
   zero pairing with every root in `J` and positive pairing with every simple
   relative root outside `J`. The proof route of that theorem goes through
   rank-one opposite factor pairs, intrinsic integral reflections and Mathlib's
   linear independence of a root-pairing base. That module's Markdown
   describes the route.
2. `simultaneousBasisJacquetAdapter_of_standardCocharacterStatement` (module
   `Langlands.BruhatTits.SpecialCompact.JacquetAdapterProof`) derives the
   target from `StandardCocharacterStatement.{u}`. It uses only the existence
   clause, so the dynamic-comparison clause is not used. For each `J` it
   applies `SimultaneousStandardBasisAt.hasIwahoriContractionBasis` to the
   supplied basis and the cocharacter `zeta`. Inside that local adapter:
   - The premise gives the common compact open normal basis `B` of `K0`. For
     this `J` it also gives the inherited Levi basis and an actual compatible
     split component `q : A.toGrp ⟶ S.toGrp`. Every member of `B` satisfies
     `StandardParabolicBasisMember i ν J q`.
   - `IsCompatibleStandardSplitComponent.strictElement` (module
     `JacquetStrictElement`) lifts `zeta` integrally through `q`. It uses the
     represented standard Levi, its central torus factor and the split
     component's factorization property. It then evaluates the lift at the
     common uniformizer section. The result is an actual element `g` of
     `G(F)` in `M_J(F)`, in `standardComponentCA i q`, in the weak chamber and
     in the strict chamber. The strict chamber is nonempty because `zeta` is
     positive on the outside-`J` simple roots. The strict-chamber membership
     is proved; it is not assumed. The element is fixed before `L` is
     introduced.
   - `InheritedCompactOpenNormalBasis.exists_intersection_le` (module
     `JacquetContractionAssembly`) chooses `K ∈ B` with
     `K.comap M_J.subtype ≤ L`. Openness and compactness come from the basis
     clause.
   - `isIwahoriContraction_of_contractionAndCofinality` (module
     `JacquetContractionAssembly`) proves the seven fields from the basis
     member's clauses. The actual multiplication bijection gives `factor` with
     the literal intersections and the order `(K ∩ Nbar)(K ∩ M)(K ∩ N)`. Weak
     chamber contraction gives `upper` and `lower`. Normalization of
     `K ∩ M` by `CA` gives `levi`. Strict-chamber exhaustion gives `exhaust`.
     The opposite power neighborhood basis gives `contract`, uniformly over
     `K ∩ Nbar`.

Affineness of `G` comes from `IsConnectedReductive` through
`hG.isAffineHom`. `IsMaximalSplitTorus` supplies the torus facts used by
both steps.

## Scope and retained obligations

The proof keeps every quantifier of the target: arbitrary local fields in
both characteristics, all ranks, all allowed `J`, the fixed maximal split
torus and generic cocharacter, the same `K0` and the canonical
rational-point topology. The proof assumes neither strict-chamber
nonemptiness, nor a chosen contracting element, nor the Jacquet conclusion.

This theorem is the conditional adapter only. It does not prove existence of
a subgroup `K0` with `SimultaneousStandardBasisAt i ν K0`. It also does not
construct the structural building certificate or any `StablePairingData`. It
does not prove the eventual-entry upgrade
`Langlands.Jacquet.IsIwahoriContraction.eventually_mem`, which needs the
separate standard-Levi normalization of the radical.

Lean reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The adapter is the derived packaging of Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, V.5.2(ii)–(iv), printed p.123 /
PDF p.129, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The target's
Markdown records this correspondence. The implemented proof is an internal
composition of the published Library results named above.
