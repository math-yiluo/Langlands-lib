/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract the proof of M099.005 (abstractFixedField_finiteDimensional) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published FiniteAbstractFixedField
Finiteness Statements module. Because the M099.003 and M099.004 proofs
(ambientQuotientFiniteOfAbstractFinite, abstractFiniteClosedSubgroup_isOpen)
are not yet in the Library, include their source proofs as the private
lemmas ambientQuotientFiniteOfAbstractFinite_local and
abstractFiniteClosedSubgroup_isOpen_local, each calling the local copy where
the source calls the original. Merge the source namespace openings into one
line, omit the unused `open RamificationTheory KummerTheory`, keep the
noncomputable section, the section variable line, the `omit [IsGalois k Ω] in`
lines and the docstrings, and state the theorem as the published Statement
applied to the source parameters. The proof is otherwise unchanged. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Statements

/-!
# Finite abstract fields have finite-dimensional fixed fields

The proof that the fixed field of an abstract closed subgroup of finite index
in the distinguished base is a finite-dimensional extension of the base field.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology ClassFormation
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

omit [IsGalois k Ω] in
/-- Local private copy of the M099.003 source theorem
`ambientQuotientFiniteOfAbstractFinite`, with its source proof unchanged:
absolute finiteness in the abstract class-formation quotient presentation
gives a finite quotient of the ambient absolute Galois group by the same
subgroup. -/
private theorem ambientQuotientFiniteOfAbstractFinite_local
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) :
    Finite (Gal(Ω/k) ⧸ H.toSubgroup) := by
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (extensionSubgroup (baseField (Gal(Ω/k))) H
    (le_baseField H)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω/k))).toSubgroup _
    (extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
    hfinite

omit [IsGalois k Ω] in
/-- Local private copy of the M099.004 source theorem
`abstractFiniteClosedSubgroup_isOpen`, with its source proof unchanged except
that it calls `ambientQuotientFiniteOfAbstractFinite_local`: an abstract field
finite over the distinguished base is represented by an open subgroup of the
absolute Galois group. -/
private theorem abstractFiniteClosedSubgroup_isOpen_local
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) :
    IsOpen H.carrier := by
  let : Finite (Gal(Ω/k) ⧸ H.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite_local k Ω H hfinite
  let : Subgroup.FiniteIndex H.toSubgroup :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H.toSubgroup H.isClosed'

/-- The fixed field of an abstract field finite over the distinguished base
is an actual finite field extension. -/
theorem abstractFixedField_finiteDimensional
    (H : ClosedSubgroup (Gal(Ω/k)))
    (hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))) :
    abstractFixedField_finiteDimensionalStatement k Ω H hfinite := by
  apply (InfiniteGalois.isOpen_iff_finite
    (K := Ω) (abstractFixedField k Ω H)).1
  rw [InfiniteGalois.fixingSubgroup_fixedField H]
  exact abstractFiniteClosedSubgroup_isOpen_local k Ω H hfinite

end
end Langlands.NYLL.LocalClassFieldTheory
