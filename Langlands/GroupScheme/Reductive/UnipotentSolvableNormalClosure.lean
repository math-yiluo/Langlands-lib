import Langlands.GroupScheme.Absolute.NormalSolvableCentrality
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus

/-! # Unipotent sources with solvable normal closure -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

namespace SmoothConnectedNormalClosure

/-- The actual closed embedding of the normal closure of a unipotent source
into the diagonal kernel of any compatible triangular representation. -/
def diagonalKernelEmbedding
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : H ⟶ G} (D : SmoothConnectedNormalClosure j)
    (hH : IsUnipotent H) (Q : SolvableSubgroupTriangularRepresentation D.inclusion) :
    {p : D.group ⟶ kernel Q.diagonalHom //
      p ≫ (kernelι Q.diagonalHom ≫ D.inclusion) = D.inclusion ∧
        IsClosedSubgroup p} := by
  let instSmoothClosure : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  let instGeoConnectedClosure : GeometricallyConnected D.group.X.hom :=
    D.hasSmoothConnectedGeneration.2.2.1
  let instConnectedClosure : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  let instClosedClosure : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let instAffineClosure : IsAffineHom D.group.X.hom := by
    rw [← D.inclusion.hom.hom.w]
    infer_instance
  let instMonoClosure : Mono D.inclusion.hom.hom := D.represents.1
  let a := AutomorphicAction.ofNormalizedConjugation D.inclusion (𝟙 G)
    (fun T g h _ hh => D.isNormal T g h (Subgroup.mem_top _) hh)
  have ha : ∀ (V : Over (Spec (CommRingCat.of k))) (g : V ⟶ G.X)
      (h : V ⟶ D.group.X),
      a.act g h ≫ D.inclusion.hom.hom =
        g * (h ≫ D.inclusion.hom.hom) * g⁻¹ := by
    intro V g h
    simpa only [a, Grp.id_hom_hom, Category.comp_id] using
      AutomorphicAction.ofNormalizedConjugation_act_comp D.inclusion (𝟙 G) _ g h
  have hrep : (SubgroupFunctor.range D.inclusion).IsRepresentedBy D.inclusion :=
    ⟨D.represents.1, rfl⟩
  let f : H ⟶ D.group := hrep.factorHom j D.contains
  have hf : f ≫ D.inclusion = j := hrep.factorHom_comp j D.contains
  have hsplit : IsSplitTorus (GeneralLinear.blockLeviScheme
      (Fin Q.dimension) (CommRingCat.of k) (fun l => -(l.val : ℤ))) := by
    have he : Function.Injective (fun l : Fin Q.dimension => -(l.val : ℤ)) := by
      intro l m h
      exact Fin.ext (Int.ofNat_inj.mp (neg_injective h))
    exact ⟨ULift.{u} (Fin Q.dimension), inferInstance,
      ⟨(GeneralLinear.diagonalTorusIso _ he (CommRingCat.of k)).symm⟩⟩
  let V := G.X ⊗ H.X
  let z : V ⟶ D.group.X := a.act (fst G.X H.X) (snd G.X H.X ≫ f.hom.hom)
  have hz : z ≫ Q.diagonalHom.hom.hom = 1 := by
    rw [Q.diagonalHom_conjugation a ha]
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      hH.comp_eq_one_of_isSplitTorus hsplit (f ≫ Q.diagonalHom) V (snd G.X H.X)
  let w : V ⟶ (kernel Q.diagonalHom).X :=
    (kernelPointsEquiv Q.diagonalHom V).symm ⟨z, hz⟩
  have hw : w ≫ (kernelι Q.diagonalHom).hom.hom = z :=
    congrArg Subtype.val ((kernelPointsEquiv Q.diagonalHom V).apply_symm_apply ⟨z, hz⟩)
  let r := kernelι Q.diagonalHom ≫ D.inclusion
  have hr : IsClosedSubgroup r := Q.closed_diagonalKernel.comp D.closed
  have hfactor : FactorsThrough (SubgroupFunctor.conjugationMap j (𝟙 G)) r := by
    refine ⟨w, ?_⟩
    change w ≫ ((kernelι Q.diagonalHom).hom.hom ≫ D.inclusion.hom.hom) = _
    rw [← Category.assoc, hw, ha]
    have hf' : f.hom.hom ≫ D.inclusion.hom.hom = j.hom.hom :=
      congrArg (fun t => t.hom.hom) hf
    simp only [Category.assoc, hf', SubgroupFunctor.conjugationMap,
      Grp.id_hom_hom, Category.comp_id]
  let p := D.toGeneratedImage.minimalHom r hr hfactor
  have hp : p ≫ r = D.inclusion := D.toGeneratedImage.minimalHom_comp r hr hfactor
  have hpc : IsClosedSubgroup p :=
    IsClosedSubgroup.of_comp hr (by rw [hp]; exact D.closed)
  exact ⟨p, hp, hpc⟩

/-- A solvable smooth connected normal closure of a unipotent source is
unipotent, without any smoothness assumption on its diagonal kernel. -/
theorem isUnipotent_of_isSolvable
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : H ⟶ G} (D : SmoothConnectedNormalClosure j)
    (hH : IsUnipotent H) (hD : IsSolvableGroupScheme D.group) :
    IsUnipotent D.group := by
  let instSmoothClosure : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  let instGeoConnectedClosure : GeometricallyConnected D.group.X.hom :=
    D.hasSmoothConnectedGeneration.2.2.1
  let instConnectedClosure : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  let instClosedClosure : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let instAffineClosure : IsAffineHom D.group.X.hom := by
    rw [← D.inclusion.hom.hom.w]
    infer_instance
  let Q := hD.ambientTriangularRepresentation D.inclusion D.closed
  let p := D.diagonalKernelEmbedding hH Q
  let instClosedKernel : IsClosedImmersion (kernelι Q.diagonalHom).hom.hom.left :=
    Q.closed_diagonalKernel
  let instAffineKernel : IsAffineHom (kernel Q.diagonalHom).X.hom := by
    rw [← (kernelι Q.diagonalHom).hom.hom.w]
    infer_instance
  let instFiniteTypeKernel : LocallyOfFiniteType (kernel Q.diagonalHom).X.hom := by
    rw [← (kernelι Q.diagonalHom).hom.hom.w]
    infer_instance
  exact unipotentClosedSubgroup k (kernel Q.diagonalHom) D.group p.val p.property.2
    Q.isUnipotent_diagonalKernel

/-- A unipotent source with solvable smooth normal closure has trivial
all-test image in a pseudo-reductive group. -/
theorem range_eq_bot_of_isSolvable_of_isPseudoReductive
    (hG : IsPseudoReductive G) {j : H ⟶ G}
    (D : SmoothConnectedNormalClosure j)
    (hH : IsUnipotent H) (hD : IsSolvableGroupScheme D.group) :
    SubgroupFunctor.range j = ⊥ := by
  let instSmoothAmbient : Smooth G.X.hom := hG.smooth
  let instAffineAmbient : IsAffineHom G.X.hom := hG.isAffineHom
  let instConnectedAmbient : ConnectedSpace G.X.left := hG.connectedSpace
  let instGeoConnectedClosure : GeometricallyConnected D.group.X.hom :=
    D.hasSmoothConnectedGeneration.2.2.1
  have hbot : SubgroupFunctor.range D.inclusion = ⊥ :=
    hG.hasTrivialUnipotentRadical D.group D.inclusion D.closed
      D.hasSmoothConnectedGeneration.1
      (GeometricallyConnected.connectedSpace_of_subsingleton
        (f := D.group.X.hom))
      (D.isUnipotent_of_isSolvable hH hD) D.isNormal
  refine le_antisymm (hbot ▸ D.contains) ?_
  intro T x hx
  have hx' : x = 1 := Subgroup.mem_bot.mp hx
  rw [hx']
  exact (SubgroupFunctor.range j).carrier T |>.one_mem

end SmoothConnectedNormalClosure

end Langlands.GroupScheme
