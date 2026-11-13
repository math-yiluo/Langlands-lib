# Finite equivariant refinements on the twisted quasi-étale site

Author: Worker 26. Uses the published `Langlands.Sheaf.Equivariant.AnalyticGSheaves`
(twisted quasi-étale site, lifts on compact objects, the local action system
`compactLiftSystem`, Worker 26) and `Langlands.Sheaf.Equivariant.LocalActionDiscretePart`
(the class `LocalActionSystem.HasFiniteEquivariantRefinements` and
`isLocallyEquivariant_of_intertwines`, Worker 26). From Worker 21 it uses the
quasi-étale site `QuasiEtaleSite`, its topology `quasiEtaleTopology`, compact spaces
`IsCompactSpace`, lifts `ActionLift`, and the statement
`QuasiEtaleActionLiftStatement` (`Langlands.Geometry.Analytic.QuasiEtaleActionLiftStatement`).

## Purpose

Let a topological group `G` act on a `K`-analytic space `X` by `ρ : G →* Aut X`. The
quasi-étale `G`-sheaves `QuasiEtaleGSheaf ρ A` are the discrete sheaves on the twisted
quasi-étale site for the local action system `compactLiftSystem ρ` of lifts of the
action to compact quasi-étale objects. The published modules
`AnalyticQuasiEtaleCompactCohomology` and `TwistedCompactSupport` assume the class

    (compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)

for the abelian structure of these sheaves and for their derived compactly supported
cohomology `H^q_c(X{G}, F)`. This module reduces that class to three conditions on the
plain quasi-étale site of `X`. Two of them are new propositions. The third follows
from Worker 21's published statement of Berkovich's lifts. The three conditions
remain hypotheses. This module does not prove any of them.

All declarations are in `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field. `X` is an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `G : Type z` is a group with a topology, and `ρ : G →* Aut X`. The theorem that uses
  `QuasiEtaleActionLiftStatement` also assumes `[IsTopologicalGroup G]`.
- `IsCompactSpace U` means that the underlying space of `U` is compact and Hausdorff
  (Worker 21's definition).

## The three conditions

- (A) `HasFiniteCompactQuasiEtaleRefinements X`: for every object `U` of
  `QuasiEtaleSite X` with `IsCompactSpace U.left` and every covering sieve `S` of `U`
  for `quasiEtaleTopology X`, there are `n : ℕ`, objects `V i` of `QuasiEtaleSite X`
  with `IsCompactSpace (V i).left` and arrows `f i : V i ⟶ U` in `S` (`i : Fin n`)
  such that `Sieve.ofArrows V f` is a covering sieve of `U`. This condition involves
  only the quasi-étale site of `X`, not the action.
- (B) `HasCompactQuasiEtaleLifts ρ`: every object `V` of `QuasiEtaleSite X` with
  `IsCompactSpace V.left` admits a lift `ActionLift ρ V.hom`. Such a lift consists of
  an open subgroup `H` of `G`, a continuous action of `H` on `V.left`, and the
  `H`-equivariance of the structure morphism `V.hom`.
- (C) `HasCompatibleCompactQuasiEtaleLifts ρ`: for all objects `U`, `V` of
  `QuasiEtaleSite X` with compact sources, every arrow `f : V ⟶ U` over `X`, and all
  lifts `a : ActionLift ρ U.hom` and `b : ActionLift ρ V.hom`, there is a subgroup `N`
  of `G` such that `N` is open, `N ≤ a.subgroup`, `N ≤ b.subgroup`, and for every
  `g ∈ N`, `(b.action g).hom ≫ f.left = f.left ≫ (a.action g).hom`. In words, `f`
  intertwines the two lifted actions on an open subgroup.

`hasCompactQuasiEtaleLifts_of_actionLiftStatement hKL hX hρ` (theorem) derives (B) from
Worker 21's `QuasiEtaleActionLiftStatement.{u, v, z} K` (`hKL`), the Hausdorff property
of the underlying space of `X` (`hX`) and continuity of `ρ` (`hρ :
IsContinuousAction ρ`). It applies the statement to the structure morphism `V.hom`,
which is quasi-étale because `V` is an object of `QuasiEtaleSite X`, and keeps the
existence half.

(C) does not follow from the uniqueness half of `QuasiEtaleActionLiftStatement`. That
half compares two lifts on the same object over `X`. (C) compares lifts on two
different objects along an arrow between them. So (C) is stated as a separate
condition.

## The reduction

`hasFiniteEquivariantRefinements_compactLiftSystem ρ hA hB hC` (theorem) proves

    (compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)

from (A), (B) and (C). The proof is as follows.

1. An admissible local action of `compactLiftSystem ρ` on an object `U` of the twisted
   site comes with `IsCompactSpace U.obj.left`, a lift `l` on `U.obj`, an open
   subgroup `H ≤ l.subgroup`, and the action `(liftAction l).comp (inclusion _)`.
2. A covering sieve `S` of `U` for `twistedQuasiEtaleTopology ρ` is, by definition of
   the twisted topology, a sieve whose pullback along the inclusion
   `ι quasiEtale ρ` covers `U.obj` in `quasiEtaleTopology X`. Condition (A) gives
   finitely many compact objects `V i` and arrows `f i : V i ⟶ U.obj` whose images
   `(ι quasiEtale ρ).map (f i)` lie in `S`, and whose family covers `U.obj`.
3. Condition (B) gives a lift `m i` on each `V i`. Its local action
   `liftAction (m i)` on `(ι quasiEtale ρ).obj (V i)`, on the open subgroup
   `liftOpenSubgroup (m i)`, is admissible: take the lift `m i` itself, with the
   inclusion of its subgroup into itself.
4. Local equivariance of `(ι quasiEtale ρ).map (f i)` follows from the published
   `isLocallyEquivariant_of_intertwines`, applied to the open subgroup `N ⊓ H`, where
   `N` comes from condition (C) for `f i`, `l` and `m i`. Twisted morphisms are
   compared by `TwistedOver.hom_ext`. Their twists agree because `ι` has trivial
   twist, and their underlying arrows agree by (C) at `g⁻¹ ∈ N`. Here `liftAction`
   lets `h` act through `h⁻¹`.
5. The family `(ι quasiEtale ρ).map (f i)` generates a covering sieve in the twisted
   topology. The pullback of the generated sieve along `ι quasiEtale ρ` contains every
   arrow `f i`, because each `f i` maps to a member of the family. Hence this pullback
   contains `Sieve.ofArrows V f`, which covers by (A), and the pullback covers too.

## Correspondence with the source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
proves Theorem 1.4.2 by the same three ingredients. In the proof of Theorem 1.4.2,
step A.2 (printed p.8), he reduces the sheaf property on a compact `U` to finite
quasi-étale coverings of `U` by compact spaces:

> 2. If U is compact, then b^p E(U) ⥲ b_* E(U). Indeed, for this it suffices to verify
> that, given a finite quasi-étale covering {U_i → U} by compact analytic spaces, one
> has b^p E(U) = Ker(∏_i b^p E(U_i) ⇉ ∏_{i,j} b^p E(U_i ×_U U_j)). The Key Lemma
> implies that for a sufficiently small open subgroup N of the intersection
> G_U ∩ ∩_{i,j} (G_{U_i} ∩ G_{U_j}) the morphisms U_i → U and U_i ×_U U_j → U_i are in
> fact N-morphisms.

Step A.1 (printed p.8) also uses compatibility along a quasi-étale morphism: "Since
this morphism is quasi-étale, it follows from the Key Lemma that it is an N-morphism
for some open subgroup N ⊂ G_U." The lifts themselves come from §1.4, printed p.7:
"for any quasi-étale morphism U → X with compact U the action of G on X extends in a
canonical way to a continuous action of some open subgroup G_U ⊂ G on U."

The correspondence is as follows.

- (A) is the reduction to finite coverings by compact spaces in step A.2. Berkovich
  does not state it as a lemma. On a compact `U`, a quasi-étale covering in the sense
  of `quasiEtalePrecoverage` gives each point a neighbourhood that is a finite union
  of images of affinoid domains of members of the covering. Compactness of `U` then
  leaves finitely many such domains. This argument is a derived explanation and is
  not formalized. In particular, it is not checked here for coverings produced by the
  transitivity closure of the generated topology.
- (B) is the existence of the extension to `G_U` on p.7. It is the existence half of
  Worker 21's `QuasiEtaleActionLiftStatement`.
- (C) is the statement that the morphisms `U_i → U` are `N`-morphisms for a small
  open `N` (steps A.1 and A.2). Berkovich derives it from the Key Lemma (Berkovich
  1994, Key Lemma 7.2) and the canonical choice of the extensions. Here it is a
  hypothesis for arbitrary lifts, not only for canonical ones. That is the form the
  class `HasFiniteEquivariantRefinements` needs, because `compactLiftSystem` admits
  every lift. Restricted to identity arrows, (C) says that two lifts on the same
  object agree on an open subgroup. That is the uniqueness half of
  `QuasiEtaleActionLiftStatement`.

The class `HasFiniteEquivariantRefinements` adds, for every member of the refinement,
an admissible local action and the local equivariance of the arrow. These are exactly
the facts that step A.2 uses, on a subgroup small enough for all members at once.

## Scope

- (A) and (C) are new hypotheses. Their proofs belong with the geometry of the
  quasi-étale site and with Berkovich's Key Lemma. Neither proof is given here.
- (B) is derived from `QuasiEtaleActionLiftStatement`, which is itself an unproved
  statement. The Hausdorff hypothesis on `X` is that statement's hypothesis. The
  three conditions and the reduction theorem do not assume it.
- No instance is declared. A user supplies the class locally, for example with
  `haveI := hasFiniteEquivariantRefinements_compactLiftSystem ρ hA hB hC`.
- The étale counterpart for `distinguishedLiftSystem` is not treated. There the class
  fails for non-compact distinguished objects such as an open disc.
