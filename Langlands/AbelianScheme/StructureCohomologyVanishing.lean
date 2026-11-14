import Langlands.AbelianScheme.FieldStructureSheafH1DimensionStatement
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof
import Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.Modules.CechDegreeOne

/-!
# Vanishing of structure-sheaf cohomology of an abelian variety above its dimension

For an abelian scheme `A` over a field `K` of relative dimension `g`, the right-derived
cohomology `Hⁿ(A, 𝒪_A)` vanishes for every `n > g`
(`isZero_structureCohomology_of_lt`, `subsingleton_structureCohomology_of_lt`). This combines
the published proofs `Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim` (dimension at
most `g`) and `Langlands.AlgebraicGeometry.Modules.noetherianSeparatedQuasicoherentVanishing`.

Every abelian scheme over a field has some relative dimension
(`exists_hasRelativeDimension_of_field`); `fieldRelativeDimension A` is a chosen one. Hence the
lower bound `fieldRelativeDimension A ≤ dim H¹(A, 𝒪_A)` turns the vanishing into vanishing
above `dim H¹(A, 𝒪_A)`
(`subsingleton_structureCohomology_of_finrank_lt`); the unproved published equality
`FieldStructureSheafH1DimensionStatement` supplies such a lower bound
(`subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Every abelian scheme over a field is smooth of some relative dimension. -/
theorem exists_hasRelativeDimension_of_field : ∃ g : ℕ, A.HasRelativeDimension g := by
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  exact Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _ A.X.hom
    inferInstance inferInstance

/-- **Vanishing above the dimension.** For an abelian scheme `A` of relative dimension `g` over a
field, `Hⁿ(A, 𝒪_A) = 0` for every `n > g`. -/
theorem isZero_structureCohomology_of_lt {g : ℕ} (hg : A.HasRelativeDimension g) {n : ℕ}
    (hn : g < n) :
    IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) := by
  let πX : A.X.left ⟶ Spec (CommRingCat.of K) := A.X.hom
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace πX
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian πX
  have : IsNoetherian A.X.left := {}
  have : A.X.left.IsSeparated := ⟨by
    rw [show terminal.from A.X.left = πX ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  exact noetherianSeparatedQuasicoherentVanishing (CommRingCat.of K) A.X.left πX g
    (Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K A.X.left πX g hg
      inferInstance)
    (SheafOfModules.unit A.X.left.ringCatSheaf) (CechDegreeOne.isQuasicoherent_unit A.X.left)
    n hn

/-- `Hⁿ(A, 𝒪_A)` is the zero module for every `n` above the relative dimension `g`. -/
theorem subsingleton_structureCohomology_of_lt {g : ℕ} (hg : A.HasRelativeDimension g)
    {n : ℕ} (hn : g < n) :
    Subsingleton ((DerivedSections.relativeCohomology A.X.hom n).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) :=
  ModuleCat.isZero_iff_subsingleton.mp (isZero_structureCohomology_of_lt A hg hn)

/-- A chosen relative dimension of an abelian scheme over a field
(`exists_hasRelativeDimension_of_field`). -/
noncomputable def fieldRelativeDimension : ℕ :=
  Classical.choose (exists_hasRelativeDimension_of_field A)

/-- `A` has relative dimension `fieldRelativeDimension A`. -/
theorem hasRelativeDimension_fieldRelativeDimension :
    A.HasRelativeDimension (fieldRelativeDimension A) :=
  Classical.choose_spec (exists_hasRelativeDimension_of_field A)

/-- `Hⁿ(A, 𝒪_A) = 0` for every `n > fieldRelativeDimension A`. -/
theorem subsingleton_structureCohomology_of_fieldRelativeDimension_lt {n : ℕ}
    (hn : fieldRelativeDimension A < n) :
    Subsingleton ((DerivedSections.relativeCohomology A.X.hom n).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) :=
  subsingleton_structureCohomology_of_lt A (hasRelativeDimension_fieldRelativeDimension A) hn

/-- **Vanishing above `dim H¹`, from a lower bound.** If
`fieldRelativeDimension A ≤ dim H¹(A, 𝒪_A)`, then `Hⁿ(A, 𝒪_A) = 0` whenever
`dim H¹(A, 𝒪_A) < n`. -/
theorem subsingleton_structureCohomology_of_finrank_lt
    (hlow : fieldRelativeDimension A ≤
      Module.finrank K ((DerivedSections.relativeCohomology A.X.hom 1).obj
        (SheafOfModules.unit A.X.left.ringCatSheaf)))
    (n : ℕ)
    (hn : Module.finrank K ((DerivedSections.relativeCohomology A.X.hom 1).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) < n) :
    Subsingleton ((DerivedSections.relativeCohomology A.X.hom n).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) :=
  subsingleton_structureCohomology_of_fieldRelativeDimension_lt A (hlow.trans_lt hn)

/-- **Vanishing above `dim H¹`, from the dimension equality.** The published (unproved)
statement `FieldStructureSheafH1DimensionStatement` gives `Hⁿ(A, 𝒪_A) = 0` for every abelian
scheme `A` over a field and every `n > dim H¹(A, 𝒪_A)`. -/
theorem subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension
    (h : FieldStructureSheafH1DimensionStatement.{u}) (n : ℕ)
    (hn : Module.finrank K ((DerivedSections.relativeCohomology A.X.hom 1).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) < n) :
    Subsingleton ((DerivedSections.relativeCohomology A.X.hom n).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) :=
  subsingleton_structureCohomology_of_finrank_lt A
    (h K A _ (hasRelativeDimension_fieldRelativeDimension A)).2.ge n hn

end Langlands.AbelianScheme
