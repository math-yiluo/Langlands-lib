/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions

/-!
# NYLL M296: finite abelian subextension data

Modified by Worker 159, 13 November 2026: extract the data, abbreviation and
instance units M296.001–.010 (source lines 44–108) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the single published import
these declarations use, and drop the unused `open KummerTheory`. Declarations,
binders, attributes, docstrings and bodies are otherwise unchanged. The paired
Markdown records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite abelian extension `L | K`: a finite Galois extension together
with commutativity of its actual quotient `G_K/G_L`. -/
structure FiniteAbelianSubextension (K : ClosedSubgroup G) where
  /-- The underlying finite Galois subextension. -/
  toFiniteGaloisExtension : FiniteGaloisSubextension K
  /-- Commutativity of the relative Galois quotient. -/
  commutative : IsMulCommutative toFiniteGaloisExtension.extensionQuotient

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- Introduces the abbreviation `field`. -/
abbrev field (L : FiniteAbelianSubextension K) : ClosedSubgroup G :=
  L.toFiniteGaloisExtension.field

/-- Introduces the abbreviation `below`. -/
abbrev below (L : FiniteAbelianSubextension K) :
    L.field.toSubgroup ≤ K.toSubgroup :=
  L.toFiniteGaloisExtension.below

/-- Introduces the abbreviation `normal`. -/
abbrev normal (L : FiniteAbelianSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.toFiniteGaloisExtension.normal

/-- Introduces the abbreviation `finite`. -/
abbrev finite (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.finite

/-- The finite abelian quotient carried by the extension.  Its representation
is inherited through the finite Galois extension boundary rather than exposed
as a transparent quotient abbreviation. -/
@[implicit_reducible]
def extensionQuotient (L : FiniteAbelianSubextension K) : Type u :=
  L.toFiniteGaloisExtension.extensionQuotient

/-- The quotient attached to a finite abelian subextension is a commutative group. -/
@[implicit_reducible]
instance extensionQuotient_commGroup (L : FiniteAbelianSubextension K) :
    CommGroup L.extensionQuotient := by
  unfold extensionQuotient
  letI : IsMulCommutative
      L.toFiniteGaloisExtension.extensionQuotient := L.commutative
  exact
    { (inferInstance :
        Group L.toFiniteGaloisExtension.extensionQuotient) with
      mul_comm := L.commutative.is_comm.comm }

/-- The quotient attached to a finite abelian subextension is finite. -/
instance extensionQuotient_finite (L : FiniteAbelianSubextension K) :
    Finite L.extensionQuotient := by
  unfold extensionQuotient
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteAbelianSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv

/-- The canonical quotient projection for a finite abelian extension. -/
def extensionQuotientMk (L : FiniteAbelianSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  L.toFiniteGaloisExtension.extensionQuotientMk

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
