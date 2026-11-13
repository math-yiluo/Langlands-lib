/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Extension fixed representations and the cyclic norm-kernel vanishing condition

Modified by Worker 133: extract M004.002–M004.005 from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, prefix the namespace
with `Langlands.NYLL`, and replace the source's module imports by the focused
Mathlib imports that these four declarations use. The declarations, their
binders and their bodies are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

As in the source, an abelian group is represented additively as a `ℤ`-linear
left representation; passing from a multiplicative module with a right action
replaces a generator by its inverse and does not change the quotient
`H⁻¹` below.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open CategoryTheory

universe u

/-- If the abstract field `L` extends `K`, this is exactly `G_L` regarded as
a subgroup of `G_K`.  The standard `Subgroup.subgroupOf` construction is the
canonical representation; the containment proof only changes the subtype
membership proof and therefore cannot create a second subgroup representation. -/
abbrev extensionSubgroup {G : Type u} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (_hLK : L.toSubgroup ≤ K.toSubgroup) :
    Subgroup K.toSubgroup :=
  L.toSubgroup.subgroupOf K.toSubgroup

/-- The actual coefficient module `A_L` for an abstract Galois extension
`L | K`: restrict the global representation to `G_K`, take `G_L`-fixed
vectors, and descend the action to `G_K / G_L`.

The subgroup occurring in the quotient is `G_L` viewed inside `G_K`. -/
noncomputable def extensionFixedRepresentation {G : Type} [Group G]
    [TopologicalSpace G] (A : Rep.{0} ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    Rep ℤ (K.toSubgroup ⧸ extensionSubgroup K L hLK) := by
  exact Rep.quotientToInvariants
    (Rep.res K.toSubgroup.subtype A)
    (extensionSubgroup K L hLK)

/-- Continuity of the action on the coefficient module when its carrier has
the discrete topology, exactly as in the source's definition of a continuous
`G`-module. -/
def IsContinuousDiscreteRepresentation {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep.{0} ℤ G) : Prop :=
  -- Mathlib orders topologies by reverse inclusion, so `⊥` is discrete.
  letI : TopologicalSpace A.V := ⊥
  Continuous fun p : G × A.V => A.ρ p.1 p.2

/-- **The cyclic norm-kernel vanishing condition.**  `H⁻¹(G(L | K), A_L)` is
trivial for every finite cyclic abstract extension `L | K`.

Profinite-ness of `G` and continuity of `A` are ambient hypotheses in the
source construction, not parts of this condition, so this predicate records
only the vanishing condition.  `hLK` expresses `G_L ≤ G_K`, `hnormal` that
the extension is Galois, `hfinite` that it is finite, and `g, hg` that its
Galois group is cyclic. -/
def SatisfiesCyclicNormKernelVanishing {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep.{0} ℤ G) : Prop :=
  ∀ (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (_hg : ∀ x, x ∈ Subgroup.zpowers g),
      letI := hnormal
      letI := hfinite
      letI := Fintype.ofFinite
        (K.toSubgroup ⧸ extensionSubgroup K L hLK)
      Limits.IsZero
        (tateCohomology (extensionFixedRepresentation A K L hLK hnormal) (-1))

end

end Langlands.NYLL.CyclicCohomology
