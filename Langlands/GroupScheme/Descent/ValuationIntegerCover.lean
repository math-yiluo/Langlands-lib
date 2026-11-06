import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # The actual fpqc cover associated to an extension of valued fields -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
    {ΓK : Type v} {ΓL : Type w}
    [LinearOrderedCommGroupWithZero ΓK] [LinearOrderedCommGroupWithZero ΓL]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL) [vK.HasExtension vL]

/-- An extension of valuation-integer rings is flat, without a finiteness premise. -/
theorem valuationInteger_flat : Module.Flat vK.integer vL.integer := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- The canonical integer-ring map of a valued-field extension is faithfully flat. -/
theorem valuationInteger_faithfullyFlat :
    Module.FaithfullyFlat vK.integer vL.integer := by
  let := valuationInteger_flat vK vL
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The actual map of integer spectra is surjective, flat and quasi-compact. -/
theorem valuationInteger_fpqc :
    Surjective (Spec.algebraMap vK.integer vL.integer) ∧
      Flat (Spec.algebraMap vK.integer vL.integer) ∧
      QuasiCompact (Spec.algebraMap vK.integer vL.integer) := by
  have h : Flat (Spec.algebraMap vK.integer vL.integer) ∧
      Surjective (Spec.algebraMap vK.integer vL.integer) := by
    apply (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap vK.integer vL.integer))).2
    change (algebraMap vK.integer vL.integer).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact valuationInteger_faithfullyFlat vK vL
  exact ⟨h.2, h.1, inferInstance⟩

/-- The singleton fpqc cover with its actual valuation-integer inclusion map. -/
def valuationIntegerCover :
    (Spec (.of vK.integer)).Cover Scheme.fpqcPrecoverage where
  I₀ := PUnit
  X _ := Spec (.of vL.integer)
  f _ := Spec.algebraMap vK.integer vL.integer
  mem₀ := by
    let := (valuationInteger_fpqc vK vL).1
    let := (valuationInteger_fpqc vK vL).2.1
    let := (valuationInteger_fpqc vK vL).2.2
    change Presieve.ofArrows (fun _ : PUnit => Spec (.of vL.integer))
      (fun _ => Spec.algebraMap vK.integer vL.integer) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

@[simp]
theorem valuationIntegerCover_f (i : (valuationIntegerCover vK vL).I₀) :
    (valuationIntegerCover vK vL).f i = Spec.algebraMap vK.integer vL.integer := rfl

end Langlands.GroupScheme
