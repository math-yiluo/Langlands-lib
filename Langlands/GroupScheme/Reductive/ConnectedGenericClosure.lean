import Langlands.GroupScheme.Reductive.SmoothTargetGenericClosure
import Langlands.GroupScheme.Reductive.ConnectedFibreLocusClosedStatement
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.DvrMatrixMonomorphismStatement
import Langlands.GroupScheme.Dynamic.FiberwiseContainment
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # Generic closure closedness from the connected-fibre theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.ReductiveGenericClosure

section Dedekind

variable {R K : Type u} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {M G : GroupScheme (Spec (CommRingCat.of R))}
    [Flat M.X.hom] [LocallyOfFiniteType M.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : M ⟶ G) [Mono f.hom.hom.left] (hM : IsReductive M)

include hM

omit [Flat M.X.hom] in
/-- The generic residue-field fibre of the actual closure is connected. -/
theorem connected_generic_residueFiber :
    ConnectedSpace (RelativeIdentityComponent.residueFiber (closure (K := K) f)
      (genericPoint (Spec (CommRingCat.of R)))).X.left := by
  have hK := hM.isConnectedReductive_algebraMap K
  have hC := hK.of_iso
    (GenericSubgroupClosure.genericToClosureIso G (genericMap (K := K) f)).symm
  let e := (Arrow.leftFunc : Arrow Scheme.{u} ⥤ Scheme.{u}).mapIso
    (fractionFieldFiberArrowIso R K (closure (K := K) f).X.hom)
  exact (Scheme.homeoOfIso e).connectedSpace_iff.mp hC.connectedSpace

/-- The supplied connected-fibre theorem forces every residue fibre of the closure
to be connected. -/
theorem connected_residueFiber_of_connectedFibreLocusClosed
    (hconnected : ConnectedFibreLocusClosedStatement.{u})
    (s : Spec (CommRingCat.of R)) :
    ConnectedSpace (RelativeIdentityComponent.residueFiber (closure (K := K) f) s).X.left := by
  let : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
  exact (hconnected _ (closure (K := K) f)
    (identityComponentReductiveLocus_eq_univ f hM)).2
      (genericPoint (Spec (CommRingCat.of R))) (genericPoint_spec _)
      (connected_generic_residueFiber f hM) s

/-- The canonical open factor is an isomorphism if the connected-fibre theorem
is available. -/
theorem factor_isIso_of_connectedFibreLocusClosed
    (hconnected : ConnectedFibreLocusClosedStatement.{u}) :
    IsIso (factor (K := K) f).hom.hom.left := by
  let : Smooth M.X.hom := hM.smooth
  let : Smooth (closure (K := K) f).X.hom := closure_smooth f hM
  have : IsOpenImmersion (factor (K := K) f).hom.hom.left := factor_isOpenImmersion f hM
  have : Mono (factor (K := K) f).hom.hom := Over.mono_of_mono_left _
  apply DynamicContainment.isIso_of_residueFibres (factor (K := K) f).hom.hom
  intro s
  let b := (Spec (CommRingCat.of R)).fromSpecResidueField s
  let Cb := (baseChange b).obj (closure (K := K) f)
  let Mb := (baseChange b).obj M
  let a := (baseChange b).map (factor (K := K) f)
  have hMb := hM.isConnectedReductive_residueFiber s
  let : Smooth Mb.X.hom := hMb.smooth
  let : IsAffineHom Mb.X.hom := hMb.isAffineHom
  let : ConnectedSpace Mb.X.left := hMb.connectedSpace
  let : ConnectedSpace Cb.X.left :=
    connected_residueFiber_of_connectedFibreLocusClosed f hM hconnected s
  let : LocallyOfFiniteType Cb.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd (closure (K := K) f).X.hom b))
  let : IsAffineHom Cb.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd (closure (K := K) f).X.hom b))
  have : Mono a.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map (factor (K := K) f).hom.hom))
  have : IsClosedImmersion a.hom.hom.left := HomImage.isClosedSubgroup_of_mono a
  have : IsOpenImmersion a.hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b
      (factor (K := K) f).hom.hom inferInstance
  have hr : IsClopen (Set.range a.hom.hom.left) :=
    ⟨a.hom.hom.left.isClosedEmbedding.isClosed_range, IsOpenImmersion.isOpen_range _⟩
  have hs : Surjective a.hom.hom.left :=
    ⟨Set.range_eq_univ.mp (hr.eq_univ (Set.range_nonempty _))⟩
  exact (isIso_iff_isOpenImmersion_and_surjective a.hom.hom.left).mpr ⟨inferInstance, hs⟩

/-- The source is the whole generic closure, conditionally on the connected-fibre theorem. -/
def factorIsoOfConnectedFibreLocusClosed
    (hconnected : ConnectedFibreLocusClosedStatement.{u}) :
    M ≅ closure (K := K) f := by
  letI := factor_isIso_of_connectedFibreLocusClosed (K := K) f hM hconnected
  letI := TorusIsomorphismLocus.isIso_of_underlying (factor (K := K) f)
  exact asIso (factor (K := K) f)

@[reassoc (attr := simp)]
theorem factorIsoOfConnectedFibreLocusClosed_hom_inclusion
    (hconnected : ConnectedFibreLocusClosedStatement.{u}) :
    (factorIsoOfConnectedFibreLocusClosed f hM hconnected).hom ≫ inclusion (K := K) f = f :=
  factor_inclusion f

/-- Closedness over a Dedekind domain, with the connected-fibre theorem retained explicitly. -/
theorem isClosedImmersion_of_connectedFibreLocusClosed
    (hconnected : ConnectedFibreLocusClosedStatement.{u}) :
    IsClosedImmersion f.hom.hom.left := by
  let := factor_isIso_of_connectedFibreLocusClosed
    (K := FractionRing R) f hM hconnected
  have hfac :
      (factor (K := FractionRing R) f).hom.hom.left ≫
        (inclusion (K := FractionRing R) f).hom.hom.left = f.hom.hom.left :=
    congrArg (fun a => a.hom.hom.left) (factor_inclusion (K := FractionRing R) f)
  rw [← hfac]
  infer_instance

end Dedekind

/-- The DVR matrix case follows from the connected-fibre theorem. -/
theorem dvrMatrixCase_of_connectedFibreLocusClosed
    (hconnected : ConnectedFibreLocusClosedStatement.{u}) :
    ReductiveDvrMatrixMonomorphismStatement.{u} := by
  intro R _ _ _ M hM N ρ hρ
  let : Smooth M.X.hom := hM.smooth
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Mono ρ.hom.hom.left := hρ
  let : Smooth (GeneralLinear.groupScheme (Fin N) (CommRingCat.of R)).X.hom :=
    GeneralLinear.smoothStatement _ _
  exact isClosedImmersion_of_connectedFibreLocusClosed ρ hM hconnected

end Langlands.GroupScheme.ReductiveGenericClosure
