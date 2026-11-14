/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Representation.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions

/-!
# Concrete Galois action on abstract fixed-field units

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology ClassFormation
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
/-- On a quotient representative, the concrete relative Galois
automorphism is restriction of the same ambient automorphism. -/
def abstractExtensionQuotientEquivGaloisGroup_mk_apply_valStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) : Prop :=
    letI := hnormal
    σ.1 (x : Ω) =
      (((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal
          (QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup) σ)) x :
        abstractRelativeFixedField k Ω hLK) : Ω)

/-- The abstract coset action on an upper fixed-field unit is the ordinary
action of the corresponding concrete relative Galois automorphism. -/
def relativeCosetAction_abstractRelativeFixedFieldUnit_valStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) : Prop :=
    letI := hnormal
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK x) q) : Ωˣ) : Ω) =
      (((Additive.toMul
        ((Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)).ρ
            (abstractExtensionQuotientEquivGaloisGroup
              k Ω K L hLK hnormal q) x) :
          (abstractRelativeFixedField k Ω hLK)ˣ) :
        abstractRelativeFixedField k Ω hLK) : Ω)

/-- The carrier comparison intertwines the descended quotient action with
the actual relative Galois action. -/
def abstractExtensionFixedRepresentationUnitsEquiv_actionStatement
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) : Prop :=
    letI := hnormal
    abstractExtensionFixedRepresentationUnitsEquiv k Ω K L hLK hnormal
        ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
          K L hLK hnormal).ρ q x) =
      (Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            k Ω K L hLK hnormal q)
          (abstractExtensionFixedRepresentationUnitsEquiv
            k Ω K L hLK hnormal x)

end
end Langlands.NYLL.LocalClassFieldTheory
