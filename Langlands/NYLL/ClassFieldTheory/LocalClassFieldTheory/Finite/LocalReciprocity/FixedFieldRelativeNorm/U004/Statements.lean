/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted types of M276.004
abstractFixedFieldCosetToAlgHom_surjective, M276.005
abstractFixedFieldCosetToAlgHom_injective and M276.007
relativeCosetAction_abstractFixedFieldUnit_val from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Package each theorem's complete telescope, including the section variables
it uses, inside a closed Prop-valued definition with the suffix Statement,
preserving binder order, binder kinds and the source's universe-zero field
types. The two private source theorems are named by their source rows in
Langlands.NYLL.PortInternal.M276 (d004Statement, d005Statement); the public
one keeps its source name with the Langlands.NYLL prefix. Write published
names in full instead of using the source namespace openings, and replace
the source imports by the published modules defining the coset embedding,
the relative coset action and the relative fixed-field unit equivalence.
Defer the truth proofs; install no instance or simp registration. Omit all
other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U002.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Relative.Definitions

/-!
# Cosets as field embeddings: bijectivity and the coset action, statements

Closed propositions saying that the map from relative left cosets to field
embeddings is surjective when the upper fixed field is finite over the lower
one and is always injective, and that the class-formation coset action on a
fixed unit is evaluation of the corresponding embedding.
-/

namespace Langlands.NYLL.PortInternal.M276

/-- Statement target for the private theorem
`abstractFixedFieldCosetToAlgHom_surjective`, source unit M276.004: every
embedding of a finite upper fixed field into the separably closed ambient
field comes from a relative left coset. -/
def d004Statement : Prop :=
  ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional
      (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField k Ω K)
      (Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField
        k Ω hLK)],
    Function.Surjective
      (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
        k Ω K L hLK)

/-- Statement target for the private theorem
`abstractFixedFieldCosetToAlgHom_injective`, source unit M276.005: distinct
relative left cosets give distinct embeddings of the upper fixed field. -/
def d005Statement : Prop :=
  ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup),
    Function.Injective
      (Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldCosetToAlgHom
        k Ω K L hLK)

end Langlands.NYLL.PortInternal.M276

namespace Langlands.NYLL.LocalClassFieldTheory

/-- States the theorem `relativeCosetAction_abstractFixedFieldUnit_val`. -/
def relativeCosetAction_abstractFixedFieldUnit_valStatement : Prop :=
  ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸
      Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK),
    ((Additive.toMul
      (Langlands.NYLL.ClassFormation.relativeCosetAction
        (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      abstractFixedFieldCosetToAlgHom k Ω K L hLK q
        (x : abstractRelativeFixedField k Ω hLK)

end Langlands.NYLL.LocalClassFieldTheory
