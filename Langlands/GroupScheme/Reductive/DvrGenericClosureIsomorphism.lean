import Langlands.GroupScheme.Reductive.EtaleDvrOpenIsomorphism
import Langlands.GroupScheme.Reductive.SmoothTargetGenericClosure
import Langlands.GroupScheme.Reductive.DvrMatrixMonomorphismStatement
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # The actual generic closure isomorphism over a DVR -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ReductiveGenericClosure

section Generic

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Flat M.X.hom] [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left]

/-- The canonical factor through the actual generic closure is generically
the canonical generic-closure isomorphism. -/
theorem genericFactor_isIso :
    IsIso ((baseChange (algebraBaseMap R K)).map (factor (K := K) f)) := by
  change IsIso ((baseChange (Spec.algebraMap R K)).map
    (GenericSubgroupClosure.factor G (genericMap (K := K) f) f (𝟙 _) _))
  rw [GenericSubgroupClosure.baseChange_factor, Category.id_comp]
  infer_instance

end Generic

section Dvr

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Flat M.X.hom] [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left] (hM : IsReductive M)

include hM

/-- The canonical factor identifies the reductive source with the entire
schematic closure of its generic image over a DVR. -/
theorem factor_isIso_of_dvr : IsIso (factor (K := K) f) := by
  let : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
  let : IsOpenImmersion (factor (K := K) f).hom.hom.left :=
    factor_isOpenImmersion f hM
  let := genericFactor_isIso (K := K) f
  exact EtaleOpenGenericIsomorphism.isIso_of_dvr (K := K) hM (factor (K := K) f)

/-- The actual isomorphism with the source's generic-image closure. -/
def factorDvrIso : M ≅ closure (K := K) f := by
  let := factor_isIso_of_dvr (K := K) f hM
  exact asIso (factor (K := K) f)

@[simp]
theorem factorDvrIso_hom : (factorDvrIso (K := K) f hM).hom = factor (K := K) f := rfl

@[reassoc (attr := simp)]
theorem factorDvrIso_hom_inclusion :
    (factorDvrIso (K := K) f hM).hom ≫ inclusion (K := K) f = f :=
  factor_inclusion f

/-- A monomorphism from a reductive group to a smooth affine group over a
DVR is a closed immersion. -/
theorem isClosedImmersion_of_dvr :
    IsClosedImmersion f.hom.hom.left := by
  let := factor_isIso_of_dvr (K := FractionRing R) f hM
  have : IsIso (factor (K := FractionRing R) f).hom.hom.left :=
    (inferInstance : IsIso
      ((Over.forget _).mapIso
        ((Grp.forget _).mapIso (factorDvrIso (K := FractionRing R) f hM))).hom)
  have hfac :
      (factor (K := FractionRing R) f).hom.hom.left ≫
        (inclusion (K := FractionRing R) f).hom.hom.left = f.hom.hom.left :=
    congrArg (fun a => a.hom.hom.left) (factor_inclusion (K := FractionRing R) f)
  rw [← hfac]
  infer_instance

end Dvr

/-- The reductive DVR matrix case, with no connected-fibre premise. -/
theorem dvrMatrixCase : ReductiveDvrMatrixMonomorphismStatement.{u} := by
  intro R _ _ _ M hM N ρ hρ
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Mono ρ.hom.hom.left := hρ
  let : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of R)).X.hom :=
    GeneralLinear.smoothStatement _ _
  exact isClosedImmersion_of_dvr ρ hM

end Langlands.GroupScheme.ReductiveGenericClosure
