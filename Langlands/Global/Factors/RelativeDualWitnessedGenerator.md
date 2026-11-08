# Actual duals of relative witnessed generators

This internal construction combines the existing actual-object contragredient
interfaces with the local restriction and support transport results. It is
derived from those interfaces and asserts no new cuspidality, association or
local compatibility theorem.

`RelativeGlobal.WitnessedGenerator.dual` takes a witnessed generator, a unitary
central-character witness for its actual cuspidal realization, and proofs of
four published prerequisite statements: actual unitary cuspidal dual existence,
spectral-presentation existence, local smooth-dual compatibility, and presented
contragredient association. Both input and chosen output presentations have the
original factor universe; the Weil carrier universe remains independent.

The theorem `WitnessedGenerator.exists_dual` first obtains an actual dual
cuspidal realization and a presentation whose finite local components are
irreducible and admissible. The associated Weil representation is the actual
algebraic dual. Its irreducibility and unitarity come from the proved
finite-dimensional duality results, and its continuity comes from the supplied
presented association proof. Classical choice selects a completed generator from
this existence proof to define `WitnessedGenerator.dual`.

The construction retains the original place above the finite place, reciprocity
candidate and characterized local map. The full exact expansion of the original
local restriction transports through `localExactExpansion_dual`. On the
automorphic side, the proved smooth-contragredient support theorem transports the
actual support, and the supplied local compatibility equivalence identifies it
with the chosen presentation's actual local component.

The accompanying simplification theorems identify the two local lattice elements
with the genuine unitary dual and contragredient operations, and identify the
retained local map and global dual Weil representation. They follow from the
specification of classical choice. A further theorem records the unitary central
character of the chosen generator's actual cuspidal realization. The prerequisite
proofs remain explicit arguments of this helper; using it for the unconditional
relative isometry operation target still requires discharging every such
prerequisite and the original central-character witness.
