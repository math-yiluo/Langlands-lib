import Langlands.GroupScheme.Absolute.NormalSolvableDiagonalConjugation
import Langlands.GroupScheme.Reductive.NormalUnipotentCommutation
import Langlands.GroupScheme.UnitriangularUnipotentProof
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # Normal solvable subgroups of pseudo-reductive groups are central -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}

namespace SolvableSubgroupTriangularRepresentation

/-- The scheme-theoretic diagonal kernel is a closed subgroup of the original subgroup. -/
theorem closed_diagonalKernel (Q : SolvableSubgroupTriangularRepresentation i) :
    IsClosedSubgroup (kernelι Q.diagonalHom) := by
  let e : Fin Q.dimension → ℤ := fun j => -(j.val : ℤ)
  let m := GeneralLinear.blockLeviHom (Fin Q.dimension) (CommRingCat.of k) e
  let : IsClosedImmersion m.hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockLeviHom _ _ _
  let : IsAffineHom (GeneralLinear.groupScheme
      (Fin Q.dimension) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  let : IsAffineHom (GeneralLinear.blockLeviScheme
      (Fin Q.dimension) (CommRingCat.of k) e).X.hom := by
    have h : IsAffineHom (m.hom.hom.left ≫ (GeneralLinear.groupScheme
        (Fin Q.dimension) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  change IsClosedImmersion (kernelι Q.diagonalHom).hom.hom.left
  infer_instance

/-- The induced morphism to the kernel of the concrete triangular projection. -/
def diagonalKernelMap (Q : SolvableSubgroupTriangularRepresentation i) :
    kernel Q.diagonalHom ⟶ kernel (GeneralLinear.blockLimitHom
      (Fin Q.dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ))) :=
  pullback.lift (kernelι Q.diagonalHom ≫ Q.triangular)
    (pullback.snd Q.diagonalHom (kernelUnit _)) (by
      change (pullback.fst Q.diagonalHom (kernelUnit _) ≫ Q.triangular) ≫ _ = _
      rw [Category.assoc]
      change pullback.fst Q.diagonalHom (kernelUnit _) ≫ Q.diagonalHom = _
      exact pullback.condition)

theorem diagonalKernelMap_comp (Q : SolvableSubgroupTriangularRepresentation i) :
    Q.diagonalKernelMap ≫ kernelι (GeneralLinear.blockLimitHom
      (Fin Q.dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ))) =
      kernelι Q.diagonalHom ≫ Q.triangular :=
  pullback.lift_fst _ _ _

/-- The actual embedding of the diagonal kernel into the concrete unitriangular group. -/
def diagonalKernelEmbedding (Q : SolvableSubgroupTriangularRepresentation i) :
    kernel Q.diagonalHom ⟶ GeneralLinear.blockUnipotentScheme
      (Fin Q.dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ)) :=
  Q.diagonalKernelMap ≫ (GeneralLinear.blockUnipotentIsoKernel
    (Fin Q.dimension) (CommRingCat.of k) (fun j => -(j.val : ℤ))).inv

/-- No smoothness or connectedness of the diagonal kernel is needed for its closed embedding. -/
theorem closed_diagonalKernelEmbedding (Q : SolvableSubgroupTriangularRepresentation i) :
    IsClosedSubgroup Q.diagonalKernelEmbedding := by
  let d := GeneralLinear.blockLimitHom (Fin Q.dimension) (CommRingCat.of k)
    (fun j => -(j.val : ℤ))
  let instClosedTriangular : IsClosedImmersion Q.triangular.hom.hom.left := Q.closed_triangular
  let instClosedKernel : IsClosedImmersion (kernelι Q.diagonalHom).hom.hom.left :=
    Q.closed_diagonalKernel
  have hcomp : IsClosedImmersion
      (Q.diagonalKernelMap.hom.hom.left ≫ (kernelι d).hom.hom.left) := by
    change IsClosedSubgroup (Q.diagonalKernelMap ≫ kernelι d)
    rw [diagonalKernelMap_comp]
    exact Q.closed_diagonalKernel.comp Q.closed_triangular
  let instClosedMap : IsClosedImmersion Q.diagonalKernelMap.hom.hom.left :=
    IsClosedImmersion.of_comp Q.diagonalKernelMap.hom.hom.left (kernelι d).hom.hom.left
  let t := GeneralLinear.blockUnipotentIsoKernel (Fin Q.dimension) (CommRingCat.of k)
    (fun j => -(j.val : ℤ))
  let instIsoKernel : IsIso t.inv.hom.hom.left :=
    ((Grp.forget (Over _)) ⋙ Over.forget _).map_isIso t.inv
  change IsClosedImmersion (Q.diagonalKernelMap.hom.hom.left ≫ t.inv.hom.hom.left)
  infer_instance

/-- The diagonal kernel is unipotent, including when it is not smooth or connected. -/
theorem isUnipotent_diagonalKernel (Q : SolvableSubgroupTriangularRepresentation i) :
    IsUnipotent (kernel Q.diagonalHom) := by
  let e : Fin Q.dimension → ℤ := fun j => -(j.val : ℤ)
  let m := GeneralLinear.blockUnipotentHom (Fin Q.dimension) (CommRingCat.of k) e
  let : IsClosedImmersion m.hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockUnipotentHom _ _ _
  let : IsAffineHom (GeneralLinear.groupScheme
      (Fin Q.dimension) (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme _ _
  let : Smooth (GeneralLinear.groupScheme
      (Fin Q.dimension) (CommRingCat.of k)).X.hom := GeneralLinear.smoothStatement _ _
  let : IsAffineHom (GeneralLinear.blockUnipotentScheme
      (Fin Q.dimension) (CommRingCat.of k) e).X.hom := by
    have h : IsAffineHom (m.hom.hom.left ≫ (GeneralLinear.groupScheme
        (Fin Q.dimension) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  let : LocallyOfFiniteType (GeneralLinear.blockUnipotentScheme
      (Fin Q.dimension) (CommRingCat.of k) e).X.hom := by
    have h : LocallyOfFiniteType (m.hom.hom.left ≫ (GeneralLinear.groupScheme
        (Fin Q.dimension) (CommRingCat.of k)).X.hom) := inferInstance
    simpa only [Over.w] using h
  exact unipotentClosedSubgroup k _ (kernel Q.diagonalHom)
    Q.diagonalKernelEmbedding Q.closed_diagonalKernelEmbedding
    (unitriangularUnipotent k Q.dimension)

/-- A normally embedded subgroup with a compatible faithful triangular
representation is central when the ambient connected group has trivial
unipotent radical. -/
theorem isCentral_of_normal_of_trivialRadical
    (Q : SolvableSubgroupTriangularRepresentation i)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hi : IsClosedSubgroup i) (hin : (SubgroupFunctor.range i).IsNormal)
    (hG : HasTrivialUnipotentRadical G) : IsCentral i := by
  let instClosedSubgroup : IsClosedImmersion i.hom.hom.left := hi
  let instMonoSubgroup : Mono i.hom.hom := Over.mono_of_mono_left _
  let a := AutomorphicAction.ofNormalizedConjugation i (𝟙 G)
    (fun T g h _ hh => hin T g h (Subgroup.mem_top _) hh)
  have ha : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X) (h : V ⟶ H.X),
      a.act g h ≫ i.hom.hom = g * (h ≫ i.hom.hom) * g⁻¹ := by
    intro V g h
    simpa only [a, Grp.id_hom_hom, Category.comp_id] using
      AutomorphicAction.ofNormalizedConjugation_act_comp i (𝟙 G) _ g h
  let j := kernelι Q.diagonalHom ≫ i
  have hj : IsClosedSubgroup j := Q.closed_diagonalKernel.comp hi
  have hf : FactorsThrough (commutatorMap (𝟙 G) i) j := by
    refine ⟨Q.commutatorKernelFactor a ha, ?_⟩
    change Q.commutatorKernelFactor a ha ≫
      ((kernelι Q.diagonalHom).hom.hom ≫ i.hom.hom) = _
    rw [← Category.assoc, Q.commutatorKernelFactor_comp a ha,
      MonObj.mul_comp, GrpObj.inv_comp, ha]
    simpa only [Category.id_comp, Category.comp_id, Grp.id_hom_hom] using
      (commutatorMap_points (𝟙 G) i (𝟙 (G.X ⊗ H.X))).symm
  have hid : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  have hidn : (SubgroupFunctor.range (𝟙 G)).IsNormal := by
    intro T g x _ _
    exact SubgroupFunctor.mem_range.2 ⟨g * x * g⁻¹, by simp⟩
  let D := (normalCommutator (𝟙 G) i hid hi hidn hin).val
  have hD := (normalCommutator (𝟙 G) i hid hi hidn hin).property
  let instSmoothEnvelope : Smooth D.group.X.hom := hD.1.1
  let instGeoConnectedEnvelope : GeometricallyConnected D.group.X.hom := hD.1.2.2.1
  have hDc : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  let p := D.minimalHom j hj hf
  have hp : p ≫ j = D.inclusion := D.minimalHom_comp j hj hf
  have hpc : IsClosedSubgroup p :=
    IsClosedSubgroup.of_comp hj (by rw [hp]; exact D.closed)
  let instClosedKernel : IsClosedImmersion (kernelι Q.diagonalHom).hom.hom.left :=
    Q.closed_diagonalKernel
  let instAffineKernel : IsAffineHom (kernel Q.diagonalHom).X.hom := by
    rw [← (kernelι Q.diagonalHom).hom.hom.w]
    infer_instance
  let instFiniteTypeKernel : LocallyOfFiniteType (kernel Q.diagonalHom).X.hom := by
    rw [← (kernelι Q.diagonalHom).hom.hom.w]
    infer_instance
  have hDu : IsUnipotent D.group :=
    unipotentClosedSubgroup k (kernel Q.diagonalHom) D.group p hpc
      Q.isUnipotent_diagonalKernel
  have hbot : SubgroupFunctor.range D.inclusion = ⊥ :=
    hG D.group D.inclusion D.closed inferInstance hDc hDu hD.2
  intro T h V b g
  have hx : (lift g (b ≫ h) ≫ D.factor) ≫ D.inclusion.hom.hom ∈
      (SubgroupFunctor.range D.inclusion).carrier V :=
    SubgroupFunctor.mem_range.2 ⟨lift g (b ≫ h) ≫ D.factor, rfl⟩
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
  rw [D.factor_comp_points, commutatorMap_lift, Grp.id_hom_hom,
    Category.comp_id] at hx
  have hcomm : Commute g ((b ≫ h) ≫ i.hom.hom) := by
    apply (commute_iff_eq _ _).2
    exact (mul_inv_eq_iff_eq_mul).mp (mul_inv_eq_one.mp hx)
  simpa only [Category.assoc] using hcomm.symm

end SolvableSubgroupTriangularRepresentation

/-- A smooth connected solvable normal closed subgroup of an algebraically
closed pseudo-reductive group is central on every test scheme. -/
theorem IsSolvableGroupScheme.isCentral_of_normal_of_isPseudoReductive
    [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) (hG : IsPseudoReductive G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hin : (SubgroupFunctor.range i).IsNormal) :
    IsCentral i := by
  let instSmoothAmbient : Smooth G.X.hom := hG.smooth
  let instAffineAmbient : IsAffineHom G.X.hom := hG.isAffineHom
  let instConnectedAmbient : ConnectedSpace G.X.left := hG.connectedSpace
  exact (hH.ambientTriangularRepresentation i hi).isCentral_of_normal_of_trivialRadical
    hi hin hG.hasTrivialUnipotentRadical

/-- The connected reductive specialization, with no torusness premise. -/
theorem IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive
    [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) (hG : IsConnectedReductive G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hin : (SubgroupFunctor.range i).IsNormal) :
    IsCentral i :=
  hH.isCentral_of_normal_of_isPseudoReductive hG.isPseudoReductive i hi hin

end Langlands.GroupScheme
