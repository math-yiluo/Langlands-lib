import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.Representation.Plancherel.RationalCentralQuotient
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge

/-! # Renard VI.3.2(ii): finite semisimple restriction to the rational norm kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV

section Algebra

variable {k Γ V : Type*} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V]

/-- A representation spanned by a finite family of irreducible subrepresentations
has finite composition length over its monoid algebra. -/
theorem isFiniteLength_of_finite_irreducible_family
    (ρ : Representation k Γ V) {I : Type*} [Finite I]
    (W : I → Subrepresentation ρ)
    (hW : ∀ i, Representation.IsIrreducible (W i).toRepresentation)
    (hspan : (⨆ i, (W i).toSubmodule) = ⊤) :
    IsFiniteLength (MonoidAlgebra k Γ) ρ.asModule := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have htop : (⨆ i, W i) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact (Langlands.Subrepresentation.toSubmodule_iSup W).trans hspan
  have hsum : (⨆ i, e (W i)) = ⊤ := by
    rw [← e.map_iSup, htop, e.map_top]
  have hsimple (i : I) : IsSimpleModule (MonoidAlgebra k Γ) (e (W i)) := by
    let S := W i
    let inclusion : S.toRepresentation.IntertwiningMap ρ :=
      { toLinearMap := S.toSubmodule.subtype
        isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }
    let j : S.toRepresentation.asModule →ₗ[MonoidAlgebra k Γ] e S :=
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ inclusion).codRestrict
        (e S) (fun v => v.property)
    have hj : Function.Bijective j :=
      ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
        fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
    exact (j.isSimpleModule_iff_of_bijective hj).mp
      ((Representation.irreducible_iff_isSimpleModule_asModule _).mp (hW i))
  let (i : I) := hsimple i
  rw [isFiniteLength_iff_isNoetherian_isArtinian, ← isNoetherian_top_iff,
    ← Submodule.topEquiv.isArtinian_iff, ← hsum]
  exact ⟨isNoetherian_iSup, isArtinian_iSup⟩

end Algebra

/-- **Renard VI.3.2(ii)** with its finite spanning-family consequence: the restriction
of an irreducible smooth complex representation of the rational points of a connected
reductive group to the actual rational common norm kernel is semisimple, has finite
length over the subgroup group algebra, and is spanned by finitely many irreducible
subrepresentations. -/
theorem rationalNormKernelFiniteRestriction :
    RationalNormKernelFiniteRestrictionStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro π hπ
  let H := Plancherel.rationalCommonNormKernel G
  have : (H ⊔ Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex :=
    rationalCommonNormKernel_sup_center_finiteIndex F G hG
  obtain ⟨hsemi, m, W, hW, hspan⟩ :=
    FiniteIndexRestriction.finite_irreducible_restriction π.representation H hπ
      (exists_scalar_rationalPoint_center F G hG π hπ)
  exact ⟨hsemi, isFiniteLength_of_finite_irreducible_family _ W hW hspan,
    m, W, hW, hspan⟩

end Langlands.CuspidalSupport
