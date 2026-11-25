/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Exact sections on the affine-neighbourhood strict henselization

Source: Stacks Project, Tag 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Global sections on the spectrum of the pointed-neighbourhood colimit are exact.

Source: Stacks Project, Tag 03QO.
(blueprint: lem-weil-pbc-strict-henselization-scheme-sections-exact).

Proof: strictHenselizationLocalStructure supplies the local and strictly henselian
structures on the actual coordinate-ring colimit. Sections at the terminal etale
object preserve epimorphisms on the spectrum of any strictly henselian local ring.
The canonical global-sections comparison transfers preservation of epimorphisms
to global sections. This functor preserves kernels, so it preserves homology and
therefore finite colimits. No comparison with a different strict localization is
needed. The result applies to every geometric point and to the zero sheaf. -/
instance strictHenselizationScheme_globalSections_preservesFiniteColimits
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) := by
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure s
  let := hlocal
  let := hstrict
  let E := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
    AddCommGrpCat.{v + 1}
  have hE : ((sheafSections (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).obj
        (op (Scheme.etaleTerminal (Scheme.strictHenselizationRing s)))).PreservesEpimorphisms := by
    exact Scheme.preservesEpimorphisms_sheafSections_of_isStrictlyHenselianLocalRing
      (Scheme.strictHenselizationRing s)
  have : E.PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso
      (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{v + 1}
        (Scheme.isTerminalEtaleTerminal (Scheme.strictHenselizationRing s))).symm
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  exact E.preservesFiniteColimits_of_preservesHomology

end AlgebraicGeometry.Etale
