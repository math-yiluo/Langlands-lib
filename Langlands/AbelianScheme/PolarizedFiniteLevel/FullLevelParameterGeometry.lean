import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameter
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiniteLimitsCoproductsProof
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Finite étale geometry of the supplied-family full-level parameter -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.FiniteEtale

private theorem finiteEtale_product {S : Scheme.{u}} {I : Type*} [Finite I]
    (X : I → Over S) (hX : ∀ i, IsFinite (X i).hom ∧ Etale (X i).hom) :
    IsFinite (∏ᶜ X).hom ∧ Etale (∏ᶜ X).hom := by
  let F : I → MorphismProperty.Over finiteEtale ⊤ S :=
    fun i => ⟨X i, hX i⟩
  let forget := MorphismProperty.Over.forget finiteEtale ⊤ S
  let e : forget.obj (∏ᶜ F) ≅ ∏ᶜ X := PreservesProduct.iso forget F
  exact (MorphismProperty.over_iso_iff finiteEtale e).mp (∏ᶜ F).prop

variable {S : Scheme.{u}} (A : AbelianScheme S) (g n : ℕ)

/-- The actual finite relative power of the torsion kernel is finite étale. -/
theorem torsionTupleScheme_finiteEtale
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsFinite (torsionTupleScheme A g n).hom ∧
      Etale (torsionTupleScheme A g n).hom :=
  finiteEtale_product _ (fun _ => torsionFiniteEtale S A n hn hunit)

/-- The full-level open is also closed in the actual tuple parameter. -/
theorem fullLevelParameterInclusion_isClosedImmersion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsClosedImmersion (fullLevelParameterInclusion A g n hn hunit).left := by
  change IsClosedImmersion (fullLevelParameterLocus A g n hn hunit).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι]
  exact (fullLevelLocusSet_isClopen (tautologicalTorsionTuple A g n) hn
    (Tate.isUnit_natCast_pullback (torsionTupleScheme A g n).hom n hunit)).isClosed

/-- The scheme classifying the unchanged full levels in a supplied family
has a finite étale structure map, without a nonemptiness assumption. -/
theorem fullLevelParameterScheme_finiteEtale
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsFinite (fullLevelParameterScheme A g n hn hunit).hom ∧
      Etale (fullLevelParameterScheme A g n hn hunit).hom := by
  obtain ⟨hfin, het⟩ := torsionTupleScheme_finiteEtale A g n hn hunit
  have : IsFinite (torsionTupleScheme A g n).hom := hfin
  have : Etale (torsionTupleScheme A g n).hom := het
  have : IsClosedImmersion (fullLevelParameterLocus A g n hn hunit).ι :=
    fullLevelParameterInclusion_isClosedImmersion A g n hn hunit
  change IsFinite ((fullLevelParameterLocus A g n hn hunit).ι ≫
      (torsionTupleScheme A g n).hom) ∧
    Etale ((fullLevelParameterLocus A g n hn hunit).ι ≫
      (torsionTupleScheme A g n).hom)
  constructor <;> infer_instance

/-- The actual full-level parameter as a finite étale cover of the supplied base. -/
def fullLevelParameterFiniteEtaleCover
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) : Cover S :=
  ⟨fullLevelParameterScheme A g n hn hunit,
    fullLevelParameterScheme_finiteEtale A g n hn hunit⟩

/-- Forgetting finite étaleness gives exactly the original parameter object. -/
@[simp]
theorem fullLevelParameterFiniteEtaleCover_obj
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    (fullLevelParameterFiniteEtaleCover A g n hn hunit).obj =
      fullLevelParameterScheme A g n hn hunit :=
  rfl

/-- Over a locally noetherian base, the actual full-level parameter is
locally noetherian as well. -/
theorem fullLevelParameterScheme_isLocallyNoetherian [IsLocallyNoetherian S]
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    IsLocallyNoetherian (fullLevelParameterScheme A g n hn hunit).left := by
  have : IsFinite (fullLevelParameterScheme A g n hn hunit).hom :=
    (fullLevelParameterScheme_finiteEtale A g n hn hunit).1
  exact LocallyOfFiniteType.isLocallyNoetherian
    (fullLevelParameterScheme A g n hn hunit).hom

end Langlands.AbelianScheme.PolarizedFiniteLevel
