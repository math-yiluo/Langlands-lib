import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.GroupScheme.Torus.PowerDomination
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Pointed domination of the torus envelope by a torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual dominant morphism from a ground-field torus, taking identity to identity.
The morphism is not required to be a group homomorphism. -/
def HasPointedTorusDomination (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P.X ⟶ H.X),
    IsTorus P ∧ IsDominant p.left ∧
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p = 1

namespace PointedTorusEnvelope

open BorelExistence

attribute [local instance]
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- The finite-power comparison followed by a pointed ordered product is pointed. -/
theorem piFinitePowerHom_orderedPowerMap_one
    {B : Scheme.{u}} {P Q : GroupScheme B} {U : Over B}
    (p : P.X ⟶ Q.X) (hp : (1 : U ⟶ P.X) ≫ p = 1) (n : ℕ) :
    (1 : U ⟶ (GroupScheme.pi fun _ : ULift.{u} (Fin n) => P).X) ≫
      (piFinitePowerHom P n ≫ orderedPowerMap p n) = 1 := by
  rw [← Category.assoc, orderedPowerMap_points]
  refine List.prod_eq_one (List.forall_mem_ofFn_iff.2 ?_)
  intro l
  rw [Category.assoc (1 : U ⟶ _) (piFinitePowerHom P n), piFinitePowerHom,
    Limits.Pi.lift_comp_π, MonObj.one_comp, hp]

/-- A dominant pointed finite power of a torus supplies pointed torus domination. -/
theorem domination_of_power {P : GroupScheme (Spec (CommRingCat.of k))}
    (hP : IsTorus P) (p : P.X ⟶ H.X)
    (hp : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p = 1)
    (n : ℕ) (hd : IsDominant (orderedPowerMap p n).left) :
    HasPointedTorusDomination H := by
  let Q := GroupScheme.pi fun _ : ULift.{u} (Fin n) => P
  let q := piFinitePowerHom P n ≫ orderedPowerMap p n
  refine ⟨Q, q, IsTorus.pi _ fun _ => hP, ⟨?_⟩,
    piFinitePowerHom_orderedPowerMap_one p hp n⟩
  apply hd.denseRange.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨(finitePowerPiHom P n).left x, ?_⟩
  have h := congrArg (fun h => (h ≫ orderedPowerMap p n).left x)
    (finitePowerPiHom_comp P n)
  simpa only [q, Category.assoc, Category.id_comp, Over.comp_left,
    Scheme.Hom.comp_apply] using h

/-- Smooth connected closed subgroups inside the envelope with pointed torus domination. -/
def IsAdmissible (i : H ⟶ G) : Prop :=
  IsClosedSubgroup i ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
    SubgroupFunctor.range i ≤ closedTorusEnvelope G ∧ HasPointedTorusDomination H

private theorem exists_admissible (G : GroupScheme (Spec (CommRingCat.of k))) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsAdmissible i := by
  obtain ⟨T, i, hT, hi⟩ := exists_isTorus_isClosedSubgroup G
  exact ⟨T.toGrp, i, hi, hT.smooth, hT.connectedSpace,
    closedTorusEnvelope_containsTori G T i hT hi,
    T.toGrp, 𝟙 _, hT, (show IsDominant (𝟙 T.X.left) from inferInstance),
      Category.comp_id _⟩

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

/-- Multiplication of a parametrized subgroup and one further torus. -/
def productMap {P : GroupScheme (Spec (CommRingCat.of k))}
    (p : P.X ⟶ H.X) (i : H ⟶ G) (j : K ⟶ G) :
    (P ⊗ K).X ⟶ G.X :=
  (fst _ _ ≫ p ≫ i.hom.hom) * (snd _ _ ≫ j.hom.hom)

private theorem range_left_le
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (p : P.X ⟶ H.X) [IsSchemeTheoreticallyDominant p.left]
    (i : H ⟶ G) (j : K ⟶ G) (D : GeneratedImage (productMap p i j)) :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range D.inclusion := by
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  have he : p ≫ i.hom.hom =
      (lift (𝟙 P.X) 1 ≫ D.factor) ≫ D.inclusion.hom.hom := by
    rw [Category.assoc, D.factor_comp, productMap, MonObj.comp_mul]
    simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp,
      mul_one]
  obtain ⟨a, ha⟩ := exists_over_factor_of_schematic_precomp
    D.inclusion.hom.hom p i.hom.hom (lift (𝟙 P.X) 1 ≫ D.factor) he
  intro U x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨h ≫ a, by rw [Category.assoc, ha]⟩

private theorem range_right_le
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (p : P.X ⟶ H.X)
    (hp : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p = 1)
    (i : H ⟶ G) (j : K ⟶ G) (D : GeneratedImage (productMap p i j)) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range D.inclusion := by
  have hp' : (1 : K.X ⟶ P.X) ≫ p = 1 := by
    have h := congrArg (fun a => (toUnit K.X) ≫ a) hp
    simpa only [← Category.assoc, MonObj.comp_one] using h
  intro U x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨h ≫ lift 1 (𝟙 K.X) ≫ D.factor, ?_⟩
  rw [Category.assoc, Category.assoc, D.factor_comp, productMap, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd, hp', MonObj.one_comp,
    Category.comp_id, one_mul]

private theorem generated_range_le_envelope
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (p : P.X ⟶ H.X) (i : H ⟶ G)
    (hi : SubgroupFunctor.range i ≤ closedTorusEnvelope G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (j : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hj : IsClosedSubgroup j)
    (D : GeneratedImage (productMap p i j)) :
    SubgroupFunctor.range D.inclusion ≤ closedTorusEnvelope G := by
  intro U x hx K a ha ht
  apply D.range_le a ha ?_ U hx
  apply (factorsThrough_iff_containsImage _ a).mpr
  intro V z
  rw [productMap, MonObj.comp_mul]
  exact ((SubgroupFunctor.range a).carrier V).mul_mem
    (hi V (SubgroupFunctor.mem_range.mpr ⟨z ≫ fst _ _ ≫ p, by simp⟩) K a ha ht)
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
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : GeometricallyIntegral H.X.hom := smoothConnectedAffineGeometry.1 k H
    inferInstance inferInstance inferInstance
  have : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  obtain ⟨P, p, hP, hpdom, hp⟩ := hi.2.2.2.2
  have : IsDominant p.left := hpdom
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P hP
  have : IsAffineHom P.X.hom := inferInstance
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom T.toGrp.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨hAff, hFin, -, hInt⟩ := smoothConnectedAffineGeometry.2 k P T.toGrp
    hP.smooth inferInstance hP.connectedSpace hT.smooth inferInstance hT.connectedSpace
  have hunit : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (P ⊗ T.toGrp).X) ≫ productMap p i j = 1 := by
    rw [productMap, MonObj.comp_mul]
    simp only [← Category.assoc, MonObj.one_comp, hp, mul_one]
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G
    inferInstance inferInstance (P ⊗ T.toGrp).X hAff hFin hInt _ _ hunit
  have : Smooth D.group.X.hom := hD.1
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have hconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have : Mono D.inclusion.hom.hom := D.represents.1
  have hpoint : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (P ⊗ T.toGrp).X) ≫ D.factor = 1 := by
    apply (cancel_mono D.inclusion.hom.hom).mp
    rw [Category.assoc, D.factor_comp, hunit, MonObj.one_comp]
  obtain ⟨n, -, hn⟩ := hD.2.2.2
  have hdom : HasPointedTorusDomination D.group :=
    domination_of_power (hP.tensor hT) D.factor hpoint n hn
  have hbelow := generated_range_le_envelope p i hi.2.2.2.1 j hT hj D
  let f : H ⟶ D.group := D.represents.factorHom i (by
    rw [← D.represents.2]
    exact range_left_le p i j D)
  have hf : f ≫ D.inclusion = i := D.represents.factorHom_comp _ _
  have : ConnectedSpace D.group.X.left := hconn
  have : IsIso f := isIso_of_coordinateKernel_height_le i D.inclusion f hi.1 D.closed
    hf (hmin D.group D.inclusion ⟨D.closed, hD.1, hconn, hbelow, hdom⟩)
  intro U x hx
  obtain ⟨d, hd⟩ := SubgroupFunctor.mem_range.mp (range_right_le p hp i j D U hx)
  refine SubgroupFunctor.mem_range.mpr ⟨d ≫ (inv f).hom.hom, ?_⟩
  have hfi := congrArg (fun a : H ⟶ G => inv f ≫ a) hf
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at hfi
  rw [Category.assoc, ← Grp.comp_hom_hom, ← hfi]
  exact hd

end PointedTorusEnvelope

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The fixed all-tori envelope has a smooth connected representative dominated
by a pointed morphism from a ground-field torus. -/
theorem exists_pointed_torusDominated_envelope
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ D : TorusGeneratedEnvelope G, Smooth D.group.X.hom ∧
      ConnectedSpace D.group.X.left ∧ HasPointedTorusDomination D.group := by
  obtain ⟨H, i, hi, hmin⟩ := PointedTorusEnvelope.exists_minimal_height_admissible G
  have hcontains := PointedTorusEnvelope.minimal_containsTori i hi hmin
  have hrange : SubgroupFunctor.range i = closedTorusEnvelope G :=
    le_antisymm hi.2.2.2.1 (closedTorusEnvelope_le i hi.1 hcontains)
  have : IsClosedImmersion i.hom.hom.left := hi.1
  exact ⟨⟨H, i, hi.1, Over.mono_of_mono_left _, hrange⟩,
    hi.2.1, hi.2.2.1, hi.2.2.2.2⟩

/-- Pointed torus domination is independent of the representative of the envelope. -/
theorem TorusGeneratedEnvelope.hasPointedTorusDomination
    (D : TorusGeneratedEnvelope G) [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    HasPointedTorusDomination D.group := by
  obtain ⟨E, -, -, P, p, hP, hpdom, hp⟩ := exists_pointed_torusDominated_envelope G
  let e := E.iso D
  have : IsDominant p.left := hpdom
  have : IsIso e.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) e.hom
  refine ⟨P, p ≫ e.hom.hom.hom, hP, ?_, ?_⟩
  · change IsDominant (p.left ≫ e.hom.hom.hom.left)
    infer_instance
  · rw [← Category.assoc, hp, MonObj.one_comp]

/-- A smooth affine group generated by its ground-field tori admits pointed torus domination. -/
theorem IsTorusGenerated.hasPointedTorusDomination
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hG : IsTorusGenerated G) :
    HasPointedTorusDomination G := by
  let D : TorusGeneratedEnvelope G := {
    group := G
    inclusion := 𝟙 G
    closed := by
      change IsClosedImmersion (𝟙 G.X.left)
      infer_instance
    represents := ⟨by change Mono (𝟙 G.X); infer_instance, by
      rw [show closedTorusEnvelope G = ⊤ from hG]
      apply SubgroupFunctor.ext
      intro U
      apply le_antisymm le_top
      intro x _
      exact SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id x⟩⟩ }
  exact D.hasPointedTorusDomination

end Langlands.GroupScheme
