import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement
import Langlands.AlgebraicGeometry.CechH1Bound
import Langlands.AlgebraicGeometry.CechKunneth
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement
import Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement

/-!
# The `H¹` dimension bound for abelian schemes over a field, from Künneth and vanishing

This module applies `Langlands.Cohomology.Cech.finiteDimensional_and_finrank_le` to an abelian
scheme `A` over a field `k`: the multiplication `μ`, the unit `η` and the two unit axes come from
the group structure of `A`, global functions are constant because `A` is smooth, proper and
geometrically connected, and a finite affine cover with affine finite intersections exists
because `A` is quasi-compact and separated. The Čech complex is exact in degree `g + 1` when
`H^{g + 1}(A, 𝒪_A) = 0` (`CechShift.exactAt_of_isZero`).

The resulting theorem `fieldStructureSheafH1DimensionBound_of` proves the published statement
from two hypotheses: the Čech Künneth detection statement and the vanishing of
`H^{g + 1}(A, 𝒪_A)` for abelian schemes of relative dimension `g`. The vanishing follows from
the published statements `FieldSmoothTopologicalKrullDimStatement` (dimension at most `g`) and
`NoetherianSeparatedQuasicoherentVanishingStatement` (`vanishing_of`), which gives
`fieldStructureSheafH1DimensionBound_of_statements`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.Cohomology Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard

/-- The published `H¹` dimension bound, assuming the Čech Künneth detection statement and the
vanishing of `H^{g + 1}(A, 𝒪_A)` for abelian schemes `A` of relative dimension `g` over a
field. -/
theorem fieldStructureSheafH1DimensionBound_of (hK : Cech.KunnethDetectionStatement.{u, u, u})
    (hvan : ∀ (k : Type u) [Field k]
      (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) (g : ℕ),
      A.HasRelativeDimension g →
        Limits.IsZero ((DerivedSections.relativeCohomology A.X.hom (g + 1)).obj
          (Langlands.Scheme.Modules.structureSheaf A.X.left))) :
    FieldStructureSheafH1DimensionBoundStatement.{u} := by
  intro k _ A g hg
  let _ := HasDerivedCategory.standard A.X.left.Modules
  let _ := HasDerivedCategory.standard (ModuleCat.{u} k)
  let πX : A.X.left ⟶ Spec (CommRingCat.of k) := A.X.hom
  -- The group law.
  let m : pullback πX πX ⟶ A.X.left := μ[A.X].left
  let e : Spec (CommRingCat.of k) ⟶ A.X.left := η[A.X].left
  have he : e ≫ πX = 𝟙 _ := Over.w η[A.X]
  let i₁ : A.X.left ⟶ pullback πX πX := (lift (𝟙 A.X) (toUnit A.X ≫ η[A.X])).left
  let i₂ : A.X.left ⟶ pullback πX πX := (lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X)).left
  have h₁₁ : i₁ ≫ pullback.fst πX πX = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))
  have h₁₂ : i₁ ≫ pullback.snd πX πX = πX ≫ e :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))
  have hm₁ : i₁ ≫ m = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg CommaMorphism.left (MonObj.lift_comp_one_right (𝟙 A.X) (toUnit A.X)))
  have h₂₁ : i₂ ≫ pullback.fst πX πX = πX ≫ e :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))
  have h₂₂ : i₂ ≫ pullback.snd πX πX = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))
  have hm₂ : i₂ ≫ m = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg CommaMorphism.left (MonObj.lift_comp_one_left (toUnit A.X) (𝟙 A.X)))
  -- A finite affine cover with affine finite intersections.
  obtain ⟨I, _, U, hU, -, hcov⟩ := exists_affineCover πX
  have hinf : ∀ V W : A.X.left.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W) :=
    fun V W hV hW => (isAffineHom_diagonal_iff (f := πX)).mp inferInstance ⊤ (isAffineOpen_top _)
      _ (by simp) _ (by simp) hV hW
  have hUall := Cech.isAffineOpen_inter hinf hU
  -- Čech exactness in degree `g + 1`.
  have hM : AffineVanishing.IsCechAcyclic (SheafOfModules.unit A.X.left.ringCatSheaf) :=
    @AffineVanishing.isCechAcyclic_of_isQuasicoherent _ _
      (CechDegreeOne.isQuasicoherent_unit A.X.left)
  have hex : Cech.ExactAt (Cech.ab A.X.left.presheaf) U g :=
    CechShift.exactAt_of_isZero πX hUall hcov g (SheafOfModules.unit A.X.left.ringCatSheaf) hM
      (hvan k A g hg)
  exact Cech.finiteDimensional_and_finrank_le hK (IsPullback.of_hasPullback πX πX)
    (surjective_secHom_top πX) m e he i₁ h₁₁ h₁₂ hm₁ i₂ h₂₁ h₂₂ hm₂ U hUall hcov hex

/-- `H^{g + 1}(A, 𝒪_A) = 0` for an abelian scheme of relative dimension `g` over a field, from the
dimension bound and the vanishing theorem for noetherian separated schemes. -/
theorem vanishing_of (hdim : Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement.{u})
    (hvan : NoetherianSeparatedQuasicoherentVanishingStatement.{u}) (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) (g : ℕ)
    (hg : A.HasRelativeDimension g) :
    Limits.IsZero ((DerivedSections.relativeCohomology A.X.hom (g + 1)).obj
      (Langlands.Scheme.Modules.structureSheaf A.X.left)) := by
  let πX : A.X.left ⟶ Spec (CommRingCat.of k) := A.X.hom
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace πX
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian πX
  have : IsNoetherian A.X.left := {}
  have : A.X.left.IsSeparated := ⟨by
    rw [show terminal.from A.X.left = πX ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  exact hvan (CommRingCat.of k) A.X.left πX g (hdim k A.X.left πX g hg inferInstance)
    (SheafOfModules.unit A.X.left.ringCatSheaf) (CechDegreeOne.isQuasicoherent_unit A.X.left)
    (g + 1) (Nat.lt_succ_self g)

/-- The published `H¹` dimension bound, assuming the Čech Künneth detection statement, the
dimension bound for smooth schemes over a field and the vanishing theorem for noetherian
separated schemes. -/
theorem fieldStructureSheafH1DimensionBound_of_statements
    (hK : Cech.KunnethDetectionStatement.{u, u, u})
    (hdim : Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement.{u})
    (hvan : NoetherianSeparatedQuasicoherentVanishingStatement.{u}) :
    FieldStructureSheafH1DimensionBoundStatement.{u} :=
  fieldStructureSheafH1DimensionBound_of hK (vanishing_of hdim hvan)

/-- The published `H¹` dimension bound from the dimension bound for smooth schemes over a field
and the vanishing theorem for noetherian separated schemes; the Künneth detection statement is
`Cech.kunnethDetection`. -/
theorem fieldStructureSheafH1DimensionBound_of_dim_of_vanishing
    (hdim : Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimStatement.{u})
    (hvan : NoetherianSeparatedQuasicoherentVanishingStatement.{u}) :
    FieldStructureSheafH1DimensionBoundStatement.{u} :=
  fieldStructureSheafH1DimensionBound_of_statements Cech.kunnethDetection hdim hvan

end Langlands.AbelianScheme
