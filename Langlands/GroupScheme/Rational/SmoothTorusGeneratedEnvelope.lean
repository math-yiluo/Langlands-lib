import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.Torus.HeightExistence

/-! # A smooth connected representative of the envelope of ground-field tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SmoothTorusEnvelope

open BorelExistence

attribute [local instance]
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k]
    {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- Smooth connected closed subgroups whose points lie in the fixed torus envelope. -/
def IsAdmissible (i : H ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
    SubgroupFunctor.range i ≤ closedTorusEnvelope G

private theorem exists_admissible (G : GroupScheme (Spec (CommRingCat.of k))) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsAdmissible i := by
  obtain ⟨T, i, hT, hi⟩ := exists_isTorus_isClosedSubgroup G
  exact ⟨T.toGrp, i, hi, hT.smooth, hT.connectedSpace,
    closedTorusEnvelope_containsTori G T i hT hi⟩

private theorem exists_minimal_height_admissible
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsAdmissible i ∧
      ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ G), IsAdmissible j →
        (coordinateKernel i).height ≤ (coordinateKernel j).height := by
  let P : ℕ∞ → Prop := fun r =>
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsAdmissible i ∧ (coordinateKernel i).height = r
  have hP : Set.Nonempty {r | P r} := by
    obtain ⟨H, i, hi⟩ := exists_admissible G
    exact ⟨_, H, i, hi, rfl⟩
  obtain ⟨_, ⟨H, i, hi, rfl⟩, hmin⟩ :=
    WellFounded.has_min wellFounded_lt {r | P r} hP
  exact ⟨H, i, hi, fun K j hj => not_lt.1 (hmin _ ⟨K, j, hj, rfl⟩)⟩

/-- The actual multiplication map from two subgroup schemes. -/
def productMap (i : H ⟶ G) (j : K ⟶ G) : H.X ⊗ K.X ⟶ G.X :=
  (fst _ _ ≫ i.hom.hom) * (snd _ _ ≫ j.hom.hom)

private theorem range_left_le (i : H ⟶ G) (j : K ⟶ G)
    (D : GeneratedImage (productMap i j)) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range D.inclusion := by
  intro U x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨lift h 1 ≫ D.factor, ?_⟩
  rw [Category.assoc, D.factor_comp, productMap, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, mul_one]

private theorem range_right_le (i : H ⟶ G) (j : K ⟶ G)
    (D : GeneratedImage (productMap i j)) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range D.inclusion := by
  intro U x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨lift 1 h ≫ D.factor, ?_⟩
  rw [Category.assoc, D.factor_comp, productMap, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, one_mul]

private theorem generated_range_le_envelope
    (i : H ⟶ G) (hi : SubgroupFunctor.range i ≤ closedTorusEnvelope G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (D : GeneratedImage (productMap i j)) :
    SubgroupFunctor.range D.inclusion ≤ closedTorusEnvelope G := by
  intro U x hx K a ha ht
  apply D.range_le a ha ?_ U hx
  apply (factorsThrough_iff_containsImage _ a).mpr
  intro V z
  rw [productMap, MonObj.comp_mul]
  exact ((SubgroupFunctor.range a).carrier V).mul_mem
    (hi V (SubgroupFunctor.mem_range.mpr ⟨z ≫ fst _ _, rfl⟩) K a ha ht)
    (ht T j hT hj V (SubgroupFunctor.mem_range.mpr ⟨z ≫ snd _ _, rfl⟩))

private theorem minimal_containsTori [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsAdmissible i)
    (hmin : ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (j : K ⟶ G),
      IsAdmissible j → (coordinateKernel i).height ≤ (coordinateKernel j).height) :
    (SubgroupFunctor.range i).ContainsTori := by
  intro T j hT hj
  have : Smooth H.X.hom := hi.2.1
  have : ConnectedSpace H.X.left := hi.2.2.1
  have : IsClosedImmersion i.hom.hom.left := hi.1
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨hAff, hFin, -, hInt⟩ := smoothConnectedAffineGeometry.2 k H T.toGrp
    inferInstance inferInstance inferInstance hT.smooth inferInstance hT.connectedSpace
  have hunit : (lift 1 1 :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X ⊗ T.toGrp.X) ≫
      productMap i j = 1 := by
    simp only [productMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      MonObj.one_comp, mul_one]
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G
    inferInstance inferInstance (H.X ⊗ T.toGrp.X) hAff hFin hInt _ _ hunit
  have : Smooth D.group.X.hom := hD.1
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have hconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have hbelow := generated_range_le_envelope i hi.2.2.2 j hT hj D
  let f : H ⟶ D.group := D.represents.factorHom i (by
    rw [← D.represents.2]
    exact range_left_le i j D)
  have hf : f ≫ D.inclusion = i := D.represents.factorHom_comp _ _
  have : ConnectedSpace D.group.X.left := hconn
  have : IsIso f := isIso_of_coordinateKernel_height_le i D.inclusion f hi.1 D.closed
    hf (hmin D.group D.inclusion ⟨D.closed, hD.1, hconn, hbelow⟩)
  intro U x hx
  obtain ⟨d, hd⟩ := SubgroupFunctor.mem_range.mp (range_right_le i j D U hx)
  refine SubgroupFunctor.mem_range.mpr ⟨d ≫ (inv f).hom.hom, ?_⟩
  have hfi := congrArg (fun a : H ⟶ G => inv f ≫ a) hf
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at hfi
  rw [Category.assoc, ← Grp.comp_hom_hom, ← hfi]
  exact hd

end Langlands.GroupScheme.SmoothTorusEnvelope

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- The fixed closed envelope of all ground-field tori in a smooth affine group
has a smooth connected actual representative. -/
theorem exists_smoothConnected_torusGeneratedEnvelope
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ D : TorusGeneratedEnvelope G,
      Smooth D.group.X.hom ∧ ConnectedSpace D.group.X.left := by
  obtain ⟨H, i, hi, hmin⟩ := SmoothTorusEnvelope.exists_minimal_height_admissible G
  have hcontains := SmoothTorusEnvelope.minimal_containsTori i hi hmin
  have hrange : SubgroupFunctor.range i = closedTorusEnvelope G :=
    le_antisymm hi.2.2.2 (closedTorusEnvelope_le i hi.1 hcontains)
  have : IsClosedImmersion i.hom.hom.left := hi.1
  exact ⟨⟨H, i, hi.1, Over.mono_of_mono_left _, hrange⟩, hi.2.1, hi.2.2.1⟩

/-- A choice of a smooth connected actual representative of the torus envelope. -/
def smoothTorusGeneratedEnvelope
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] : TorusGeneratedEnvelope G :=
  Classical.choose (exists_smoothConnected_torusGeneratedEnvelope G)

theorem smoothTorusGeneratedEnvelope_smooth
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    Smooth (smoothTorusGeneratedEnvelope G).group.X.hom :=
  (Classical.choose_spec (exists_smoothConnected_torusGeneratedEnvelope G)).1

theorem smoothTorusGeneratedEnvelope_connectedSpace
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ConnectedSpace (smoothTorusGeneratedEnvelope G).group.X.left :=
  (Classical.choose_spec (exists_smoothConnected_torusGeneratedEnvelope G)).2

end Langlands.GroupScheme
