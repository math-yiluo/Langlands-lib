/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M033.015 (finite_extension_of_le) from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean
(lines 247–269) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix and import only the published
ReciprocityIndependence U015 Statements module. Keep the universe, the
section variable line, the noncomputable section, the docstring, the binders
(including the name `hPfinite`), and state the
theorem as the published Statement applied to the source parameters. The
finiteness instance is written with the Mathlib body
`P.toSubgroup.subgroupOf K.toSubgroup` of `extensionSubgroup K P hPK`, as in
the published Statement. Integrator reuses the existing M040.025 proof
`FiniteGaloisSubextension.finite_extension_over_intermediate` rather than
repeating the identical finite-index argument. Open `Langlands.NYLL.CyclicCohomology` for `extensionSubgroup`
and omit the unused `open KummerTheory`, the other section declarations and
the section name. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.U015.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U025.Proofs

/-!
# Finite extensions between finite intermediate fields

The proof that if `P | K` is finite and `P ≤ M ≤ K`, then `P | M` is finite:
the index of `P` in `M` divides into the finite index of `P` in `K`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open Langlands.NYLL.CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- If `P | K` is finite and `P` contains the intermediate field `M`, then
`P | M` is finite. -/
theorem finite_extension_of_le
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPfinite : Finite
      (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)] :
    finite_extension_of_leStatement hPK hMK hPM :=
  FiniteGaloisSubextension.finite_extension_over_intermediate hPK hMK hPM

end FiniteIntermediateField

end

end Langlands.NYLL.ClassFormation
