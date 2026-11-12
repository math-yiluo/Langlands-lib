# Jacquet exclusion and unwanted inertia components

Worker 137. Supporting construction and proved comparisons for Task 5352. The module formalizes the passage from the published condition (iii) to the absence of all constituents in each prohibited Levi inertia orbit. It does not prove the full Bernstein block characterization.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, VI.7.2 Proposition and proof, printed pp.184–185 / PDF pp.190–191. The target statement's Markdown explains this translation but leaves it unformalized. These are derived internal helpers for that translation.

The proof first uses compact containment of the standard radicals, proved from the published standard-cocharacter theorem. Intersecting with the closed standard Levi preserves compact containment. Mapping a compact subgroup through the canonical homeomorphism into the Levi scheme places it in the rational common norm kernel, so every actual unramified character kills the radical. The normalized Jacquet twist equivalence then shows that inertia-related actions have the same vanishing of proper standard Jacquet modules.

An inertia-related irreducible action therefore replaces the representation of a Bernstein datum on the same Levi. Identity conjugation proves that the new datum is Bernstein-inertia-related to the old one. Given condition (iii), any constituent of an unwanted Jacquet inertia orbit would be the action of such a replacement datum, contradicting (iii). Conversely, excluding the entire orbit excludes the original action by reflexivity.

The Jacquet module is transported to the actual Levi scheme by the canonical group homeomorphism. The subquotient transport is proved by pulling back along the homeomorphism and its inverse, whose composites have identity carrier maps. No admissibility or finite-length hypothesis, Bernstein decomposition, or support uniqueness is used.

The setting is exactly a published `BernsteinStandardFamily i ν`, over an arbitrary nonarchimedean local field, with the canonical rational-point topology and the local compactness and nonarchimedean group instances of the target. The field universe `uF` and carrier universe `uV` remain independent. `bernsteinSchemeJacquet` and the transport/cuspidality helpers allow arbitrary `uV`; `BernsteinJacquetExclusion` and its complement equivalence use the target's saturated carrier universe `max uF uV`.

The entry construction is `bernsteinSchemeJacquet`. The proved comparison `isSubquotient_bernsteinSchemeJacquet_iff` moves occurrences to the literal Levi. `bernsteinLeviUnramifiedCharacter_radical` and `isLeviCuspidal_bernsteinLiteralLeviRep_of_inertia` supply the inertia replacement `BernsteinCuspidalDatum.replaceInertia`; `BernsteinCuspidalDatum.inertia_replaceInertia` proves its class is unchanged. Finally `bernsteinJacquetExclusion_iff_inertiaComplement` proves the stated equivalence for the actual published objects.

The result concerns absence of constituents in unwanted inertia orbits. Identifying that absence with zero components of a chosen inertia decomposition still uses the separately stated decomposition theorem. Membership of `V` in its Bernstein block, the induction embeddings of conditions (i) and (ii), and the three equivalences of `BernsteinBlockCharacterizationStatement` are not proved by this module. The published target and its imports are unchanged.

## Name of the file-local topology

The file-local instance `TopologicalSpace (rationalPoints G)`, the canonical point topology, is named `instBernsteinJacquetInertiaExclusionTopology`. It used to be anonymous, and Lean gave it the generated name `Langlands.CuspidalSupport.instTopologicalSpaceRationalPoints`. `RationalUniversalProgenerator` declares its own anonymous topology on rational points, with a different type, and Lean gives it the same generated name. A file-local instance is still a declaration in the namespace `Langlands.CuspidalSupport`. Neither module imports the other, so each built on its own, but any module that imports both failed with a duplicate-declaration error. Only the name changed: the type and value are as before, and no file refers to the instance by name. The other file-local instances of this module keep their generated names, which no other module declares.

Integration also gives the local affine, closed-immersion, finite-type and
Levi point-topology instances explicit module-specific names. Their types,
bodies and local scope are preserved; no consumer refers to their former
automatically generated names.
