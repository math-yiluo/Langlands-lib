import Langlands.GroupScheme.SmoothFieldComponent

/-! # Normality and field base change of smooth field identity components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SmoothFieldComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom]

instance : Mono (inclusion H) where
  right_cancellation _ _ h := IdentityComponent.hom_ext_of_isOpenImmersion _ h

@[reassoc (attr := simp)]
theorem one_inclusion : η[(group H).X] ≫ (inclusion H).hom.hom = η[H.X] :=
  IsMonHom.one_hom _

/-- The conjugation map `(g, x) ↦ g x g⁻¹` from `H ×_k H⁰` to `H`. -/
def conjOver : H.X ⊗ (group H).X ⟶ H.X :=
  (H.X ◁ (inclusion H).hom.hom) ≫ GrpObj.conj H.X

theorem lift_conjOver {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ H.X)
    (y : T ⟶ (group H).X) :
    lift g y ≫ conjOver H = g * (y ≫ (inclusion H).hom.hom) * g⁻¹ := by
  rw [conjOver, lift_whiskerLeft_assoc, GrpObj.lift_conj_eq_mul_mul_inv]

/-- Conjugation by an arbitrary point of `H` maps `H⁰` into the connected component of the
identity: each fibre of the projection `H ×_k H⁰ ⟶ H` is connected and contains a point sent
to the identity point. -/
theorem range_conjOver_subset : Set.range (conjOver H).left ⊆ IdentityComponent.identitySet H := by
  rintro _ ⟨z, rfl⟩
  let p : (H.X ⊗ (group H).X).left ⟶ H.X.left :=
    pullback.fst H.X.hom ((group H).X).hom
  let s : H.X ⟶ H.X ⊗ (group H).X := lift (𝟙 _) (toUnit _ ≫ η[(group H).X])
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hs : s ≫ conjOver H = toUnit _ ≫ η[H.X] := by
    rw [lift_conjOver, Category.assoc, one_inclusion, ← CategoryTheory.Hom.one_def]
    simp
  have hsz : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ fst _ _).left (p z) = p z
    rw [lift_fst]
    rfl
  have hconn : _root_.IsConnected ((conjOver H).left '' (p ⁻¹' {p z})) :=
    hF.image _ (conjOver H).left.continuous.continuousOn
  refine hconn.isPreconnected.subset_connectedComponent ⟨_, hsz, ?_⟩
    ⟨z, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, Over.comp_left, Scheme.Hom.comp_apply,
    IdentityComponent.unit_left_apply]

/-- The range subgroup functor of `H⁰ ⟶ H` is normal, with the all-test meaning: conjugation by
every point of `H` over every test scheme preserves the points of `H⁰`. -/
theorem isNormal_range_inclusion :
    (SubgroupFunctor.range (inclusion H)).IsNormal := by
  intro T g x _ hx
  rw [SubgroupFunctor.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨liftOver ((inclusion H).hom.hom) (lift g y ≫ conjOver H) ?_, ?_⟩
  · rw [range_inclusion]
    rintro _ ⟨t, rfl⟩
    exact range_conjOver_subset H ⟨(lift g y).left t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rw [liftOver_fac, lift_conjOver]

section Characterization

variable {P : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace P.X.left]
  (j : P ⟶ H) [IsOpenImmersion j.hom.hom.left] [IsClosedImmersion j.hom.hom.left]

/-- A connected open and closed subgroup is the actual identity component. -/
def isoOfIsOpenImmersion : P ≅ group H where
  hom := factor H j
  inv := IdentityComponent.liftHom j (inclusion H) (by
    rw [range_inclusion, IdentityComponent.range_eq_identitySet])
  hom_inv_id := IdentityComponent.hom_ext_of_isOpenImmersion j (by simp)
  inv_hom_id := IdentityComponent.hom_ext_of_isOpenImmersion (inclusion H) (by simp)

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_hom_inclusion :
    (isoOfIsOpenImmersion H j).hom ≫ inclusion H = j :=
  factor_inclusion H j

@[reassoc (attr := simp)]
theorem isoOfIsOpenImmersion_inv_comp :
    (isoOfIsOpenImmersion H j).inv ≫ j = inclusion H :=
  IdentityComponent.liftHom_fac _ _ _

end Characterization

section BaseChange

variable {L : Type u} [Field L] (φ : k →+* L)

/-- The field-extension morphism on spectra. -/
abbrev specMap : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom φ)

instance : Smooth ((GroupScheme.baseChange (specMap φ)).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom (specMap φ)))

instance : IsOpenImmersion
    ((GroupScheme.baseChange (specMap φ)).map (inclusion H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) (specMap φ)
    (inclusion H).hom.hom inferInstance

instance : IsClosedImmersion
    ((GroupScheme.baseChange (specMap φ)).map (inclusion H)).hom.hom.left :=
  MorphismProperty.overPullbackMap (P := @IsClosedImmersion) (specMap φ)
    (inclusion H).hom.hom inferInstance

instance : ConnectedSpace
    ((GroupScheme.baseChange (specMap φ)).obj (group H)).X.left :=
  @GeometricallyConnected.connectedSpace_of_subsingleton _ _
    (pullback.snd (group H).X.hom (specMap φ))
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @GeometricallyConnected.{u})
      (IsPullback.of_hasPullback _ _) inferInstance) _ _

/-- The actual smooth identity-component group commutes with every field extension. -/
def baseChangeIso :
    (GroupScheme.baseChange (specMap φ)).obj (group H) ≅
      group ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion _ ((GroupScheme.baseChange (specMap φ)).map (inclusion H))

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_inclusion :
    (baseChangeIso H φ).hom ≫ inclusion ((GroupScheme.baseChange (specMap φ)).obj H) =
      (GroupScheme.baseChange (specMap φ)).map (inclusion H) :=
  isoOfIsOpenImmersion_hom_inclusion _ _

@[reassoc (attr := simp)]
theorem baseChangeIso_inv_comp :
    (baseChangeIso H φ).inv ≫ (GroupScheme.baseChange (specMap φ)).map (inclusion H) =
      inclusion ((GroupScheme.baseChange (specMap φ)).obj H) :=
  isoOfIsOpenImmersion_inv_comp _ _

end BaseChange

end Langlands.GroupScheme.SmoothFieldComponent
