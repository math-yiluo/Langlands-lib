import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationField

/-! # Rational points of dominant pointed products -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ConnectedGenerationField

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A rational point in the topological image of a finite-type morphism lifts
as a rational point over an algebraically closed field. -/
theorem exists_point_lift {V W : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType V.hom] [LocallyOfFiniteType W.hom]
    (q : V ⟶ W) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ W)
    (hx : x.left (IsLocalRing.closedPoint k) ∈ Set.range q.left) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V, a ≫ q = x := by
  let : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace V.hom
  have hxc : IsClosed {x.left (IsLocalRing.closedPoint k)} :=
    ((pointEquivClosedPoint W.hom) ⟨x.left, Over.w x⟩).2
  obtain ⟨z₀, hz₀⟩ := hx
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := q.left ⁻¹' {x.left (IsLocalRing.closedPoint k)})
    ⟨z₀, hz₀⟩ (hxc.preimage q.left.continuous).isLocallyClosed
  let a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V :=
    Over.homMk (pointOfClosedPoint V.hom z hzc) (pointOfClosedPoint_comp V.hom z hzc)
  refine ⟨a, Over.OverMorphism.ext ?_⟩
  apply ext_of_apply_closedPoint_eq W.hom (Over.w (a ≫ q)) (Over.w x)
  change q.left (pointOfClosedPoint V.hom z hzc (IsLocalRing.closedPoint k)) = _
  rw [pointOfClosedPoint_apply]
  exact hz

/-- A subgroup containing all rational points of a dominant finite-type
parametrization contains every rational point of a smooth connected group. -/
theorem points_mem_of_dominant
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    {V : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType V.hom] [IsAffineHom V.hom]
    (q : V ⟶ H.X) [IsDominant q.left] (j : H ⟶ G)
    (U : Subgroup (rationalPoints G))
    (hU : ∀ a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V,
      (a ≫ q) ≫ j.hom.hom ∈ U) (x : rationalPoints H) :
    rationalPoints.map j x ∈ U := by
  let : IsAffine V.left := isAffine_of_isAffineHom V.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  let : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  let : IsNoetherian V.left := ⟨⟩
  let : IsNoetherian H.X.left := ⟨⟩
  let : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  let : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  let : IrreducibleSpace H.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton H.X.hom
  let : LocallyOfFiniteType (q.left ≫ H.X.hom) := by rw [Over.w]; infer_instance
  let : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left H.X.hom
  have hc : IsConstructible (Set.range q.left) := by
    simpa only [Set.image_univ] using
      q.left.isConstructible_image (s := Set.univ) IsConstructible.univ
  obtain ⟨O, hO, hOne, hOq⟩ := ClosedOrbit.exists_isOpen_subset_of_dense hc
    (show DenseRange q.left from q.left.denseRange)
  let τ : H.X ⟶ H.X := (GrpObj.mulRight x).hom
  let : IsIso τ.left := (Over.forget _).map_isIso τ
  have hτne : (τ.left ⁻¹' O).Nonempty :=
    τ.left.homeomorph.surjective.nonempty_preimage.mpr hOne
  have hI : (O ∩ τ.left ⁻¹' O).Nonempty := by
    simpa using (IrreducibleSpace.isIrreducible_univ H.X.left).2
      O (τ.left ⁻¹' O) hO (hO.preimage τ.left.continuous)
      (by simpa using hOne) (by simpa using hτne)
  obtain ⟨z, ⟨hzO, hzτ⟩, hzc⟩ := nonempty_inter_closedPoints hI
    (hO.inter (hO.preimage τ.left.continuous)).isLocallyClosed
  let a : rationalPoints H :=
    Over.homMk (pointOfClosedPoint H.X.hom z hzc) (pointOfClosedPoint_comp H.X.hom z hzc)
  have ha : a.left (IsLocalRing.closedPoint k) ∈ O := by
    change pointOfClosedPoint H.X.hom z hzc _ ∈ O
    simpa using hzO
  have hat : (a ≫ τ).left (IsLocalRing.closedPoint k) ∈ O := by
    change τ.left (pointOfClosedPoint H.X.hom z hzc _) ∈ O
    simpa using hzτ
  obtain ⟨b, hb⟩ := exists_point_lift q a (hOq ha)
  obtain ⟨c, hc⟩ := exists_point_lift q (a ≫ τ) (hOq hat)
  have hbU : rationalPoints.map j a ∈ U := by
    change a ≫ j.hom.hom ∈ U
    rw [← hb]
    exact hU b
  have hcU : rationalPoints.map j (a * x) ∈ U := by
    have hat' : a ≫ τ = a * x := by
      change a ≫ ((𝟙 H.X) * (toUnit H.X ≫ x)) = _
      rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      rfl
    rw [← hat']
    change (a ≫ τ) ≫ j.hom.hom ∈ U
    rw [← hc]
    exact hU c
  have hu := U.mul_mem (U.inv_mem hbU) hcU
  simpa only [map_mul, inv_mul_cancel_left] using hu

/-- A generated image has no additional rational points beyond a subgroup
already containing its parametrized points. -/
theorem generatedImage_range_le
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {V : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [LocallyOfFiniteType V.hom]
    [GeometricallyIntegral V.hom]
    {f : V ⟶ G.X} (D : GeneratedImage f) (hD : D.HasSmoothConnectedGeneration)
    (U : Subgroup (rationalPoints G))
    (hf : ∀ a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V, a ≫ f ∈ U) :
    (rationalPoints.map D.inclusion).range ≤ U := by
  let : Smooth D.group.X.hom := hD.1
  let : IsAffineHom D.group.X.hom := hD.2.1
  let : GeometricallyConnected D.group.X.hom := hD.2.2.1
  let : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  obtain ⟨n, _, hdom⟩ := hD.2.2.2
  let : IsDominant (D.powerMap n).left := hdom
  have hgood := ImageGeneration.finitePowerGood_finitePower V
    (ImageGeneration.finitePowerGood_of_geometricallyIntegral V
      inferInstance inferInstance inferInstance) n
  let : IsAffineHom (finitePower V n).hom := hgood.1
  let : LocallyOfFiniteType (finitePower V n).hom := hgood.2.1
  rintro _ ⟨x, rfl⟩
  apply points_mem_of_dominant (D.powerMap n) D.inclusion U ?_ x
  intro a
  rw [D.powerMap_comp_points, orderedPowerMap_points]
  apply U.list_prod_mem
  intro y hy
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  exact hf (a ≫ Pi.π (fun _ : Fin n => V) j)

end Langlands.GroupScheme.ConnectedGenerationField
