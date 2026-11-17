import Langlands.GroupScheme.KernelPresentation
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteSubgroupSpreadingStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeMonomorphismSpreadingStatement

/-! # Kernel reduction for local monomorphism spreading -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The unit-fibre clause of finite-subgroup spreading proves local monomorphism
spreading once the source's affine finite-presentation geometry is supplied. -/
theorem mono_near_of_finiteSubgroupSpreading
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (f : H ⟶ G) [IsSeparated G.X.hom] (s : S)
    (hs : Mono ((baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    ∃ U : S.Opens, s ∈ U ∧ Mono ((baseChange U.ι).map f).hom.hom := by
  have hkfp : LocallyOfFinitePresentation (kernel f).X.hom :=
    locallyOfFinitePresentation_kernel_of_source f (hbase.imp_right fun h => by
      let := h
      infer_instance)
  have : IsAffineHom (kernel f).X.hom := isAffineHom_kernel_of_closed f
  have hs' : IsIso ((baseChange (S.fromSpecResidueField s)).obj (kernel f)).X.hom :=
    (baseChange_kernel_hom_isIso_iff _ f).mpr hs
  obtain ⟨U, hsU, hU⟩ := (hspread S H (kernel f) (kernelι f) hH inferInstance
    hkfp inferInstance inferInstance s).2 hs'
  exact ⟨U, hsU, (baseChange_kernel_hom_isIso_iff _ f).mp hU⟩

/-- An open neighbourhood of a base point on which the specified homomorphism
is monomorphic. -/
structure MonomorphismNeighbourhood (f : H ⟶ G) (s : S) where
  openSet : S.Opens
  mem : s ∈ openSet
  monomorphism : Mono ((baseChange openSet.ι).map f).hom.hom

/-- Choose the open neighbourhood supplied by finite-subgroup spreading,
retaining its membership and monomorphism certificates. -/
def monomorphismNeighbourhoodOfFiniteSubgroupSpreading
    (hspread : MultiplicativeTypeFiniteSubgroupSpreadingStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [IsAffineHom H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (hbase : IsLocallyNoetherian S ∨ LocallyOfFinitePresentation G.X.hom)
    (f : H ⟶ G) [IsSeparated G.X.hom] (s : S)
    (hs : Mono ((baseChange (S.fromSpecResidueField s)).map f).hom.hom) :
    MonomorphismNeighbourhood f s :=
  let h := mono_near_of_finiteSubgroupSpreading hspread hH hbase f s hs
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end Langlands.GroupScheme
