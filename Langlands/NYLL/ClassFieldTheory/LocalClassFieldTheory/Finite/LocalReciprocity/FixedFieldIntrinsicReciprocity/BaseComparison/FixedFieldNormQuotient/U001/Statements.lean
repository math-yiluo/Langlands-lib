/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 14 November 2026:
Extract only the asserted type of M278.001
map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroup from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/FixedFieldNormQuotient.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Package the theorem's complete
telescope inside a closed Prop-valued definition with the suffix Statement,
preserving binder order, binder kinds and the source's universe-zero field
types; the two named instance binders become anonymous. Write published
names in full instead of using the source namespace openings, and replace
the source imports by the published modules defining the objects named in
the statement. Defer the truth proof; install no instance or simp
registration. Omit all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.IsSepClosed
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Initial.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions

/-!
# Fixed-field finite norm subgroups: statement

A closed proposition saying that the identification of fixed coefficients
with units of the concrete fixed field sends the class-formation finite norm
subgroup to the additive form of the ordinary field-norm subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The fixed-field units equivalence sends the cohomological finite norm
subgroup to the additive form of the ordinary field-norm subgroup. -/
def map_fixedFieldFiniteNormSubgroup_eq_additiveNormSubgroupStatement : Prop :=
  ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsSepClosed Ω]
    (K L : ClosedSubgroup Gal(Ω/k))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite
      (K.toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK)]
    [Finite
      ((Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)).toSubgroup ⧸
        Langlands.NYLL.CyclicCohomology.extensionSubgroup
          (Langlands.NYLL.ClassFormation.baseField Gal(Ω/k)) K
          (Langlands.NYLL.ClassFormation.le_baseField K))],
    (Langlands.NYLL.ClassFormation.finiteNormSubgroup
        (galoisAmbientUnitsRep k Ω) K L hLK).map
        (abstractFixedFieldUnitsEquivGaloisFixed
          k Ω K).symm.toAddMonoidHom =
      Langlands.NYLL.CyclicCohomology.additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end Langlands.NYLL.LocalClassFieldTheory
