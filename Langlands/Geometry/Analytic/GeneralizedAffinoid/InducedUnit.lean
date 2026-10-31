import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAtlasComparison

/-! # Bounded identity-coset unit for actual affinoid induction -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] (H : Subgroup G)

/-- The identity coset, without any choice of a normalized representative. -/
def identityCoset : G ⧸ H := QuotientGroup.mk 1

/-- The chosen representative of the identity coset belongs to the subgroup. -/
def identityRepresentative : H :=
  ⟨(identityCoset H).out, by
    have he := QuotientGroup.eq.mp (QuotientGroup.out_eq' (identityCoset H)).symm
    simpa [identityCoset] using he⟩

@[simp]
theorem identityCoset_smul (h : H) : (h : G) • identityCoset H = identityCoset H := by
  change (QuotientGroup.mk ((h : G) * 1) : G ⧸ H) = QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  simp

/-- At the identity coset the correction is conjugation by its representative. -/
theorem correction_identityCoset (h : H) :
    correction H (h : G) (identityCoset H) =
      (identityRepresentative H)⁻¹ * h * identityRepresentative H := by
  apply Subtype.ext
  simp [correction_coe, mul_assoc, identityRepresentative]

variable [TopologicalSpace G]

/-- A genuine one-component family, retaining its algebra even when empty. -/
def localFamily (X : NormContinuousSpace K H) : AffinoidFamily.{u, v} K :=
  ⟨PUnit.{v+1}, fun _ => X.unop.obj.V⟩

/-- The original geometric action uses inverse bounded algebra operators. -/
def localActionMap (X : NormContinuousSpace K H) (h : H) :
    localFamily H X ⟶ localFamily H X where
  indexMap := id
  pullback _ := (X.unop.actionAut h).inv

@[simp]
theorem localActionMap_one (X : NormContinuousSpace K H) :
    localActionMap H X 1 = 𝟙 (localFamily H X) := by
  apply AffinoidFamily.Hom.ext
    (f := localActionMap H X 1) (g := 𝟙 (localFamily H X)) rfl
  apply heq_of_eq
  funext i
  change (X.unop.actionAut 1).inv = BoundedAlgHom.id K X.unop.obj.V
  rw [map_one]
  rfl

theorem localActionMap_mul (X : NormContinuousSpace K H) (h k : H) :
    localActionMap H X (h * k) = localActionMap H X k ≫ localActionMap H X h := by
  apply AffinoidFamily.Hom.ext
    (f := localActionMap H X (h * k))
    (g := localActionMap H X k ≫ localActionMap H X h) rfl
  apply heq_of_eq
  funext i
  change (X.unop.actionAut (h * k)).inv =
    ((X.unop.actionAut k).inv).comp (X.unop.actionAut h).inv
  rw [map_mul]
  rfl

/-- The one-component family carries the actual original subgroup action. -/
def localAction (X : NormContinuousSpace K H) : Action (AffinoidFamily.{u, v} K) H where
  V := localFamily H X
  ρ :=
    { toFun := localActionMap H X
      map_one' := localActionMap_one H X
      map_mul' := localActionMap_mul H X }

/-- Original bounded maps on the one-component families. -/
def localFamilyMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    localFamily H X ⟶ localFamily H Y where
  indexMap := id
  pullback _ := NormContinuousAction.homMap f.unop

theorem localFamilyMap_equivariant {X Y : NormContinuousSpace K H}
    (f : X ⟶ Y) (h : H) :
    localActionMap H X h ≫ localFamilyMap H f =
      localFamilyMap H f ≫ localActionMap H Y h := by
  apply AffinoidFamily.Hom.ext
    (f := localActionMap H X h ≫ localFamilyMap H f)
    (g := localFamilyMap H f ≫ localActionMap H Y h) rfl
  apply heq_of_eq
  funext i
  apply BoundedAlgHom.ext
  intro a
  exact (NormContinuousAction.homMap_apply_action f.unop h⁻¹ a).symm

/-- The original actions as actual one-component affinoid families. -/
def localFunctor : NormContinuousSpace K H ⥤ Action (AffinoidFamily.{u, v} K) H where
  obj := localAction H
  map f := ⟨localFamilyMap H f, localFamilyMap_equivariant H f⟩
  map_id X := by
    apply Action.Hom.ext
    apply AffinoidFamily.Hom.ext rfl
    exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)
  map_comp f k := by
    apply Action.Hom.ext
    apply AffinoidFamily.Hom.ext rfl
    exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)

/-- The forward algebra operator compensates for the unnormalized representative. -/
def unitFamilyMap (X : NormContinuousSpace K H) :
    localFamily H X ⟶ family H X.unop where
  indexMap _ := identityCoset H
  pullback _ := (X.unop.actionAut (identityRepresentative H)).hom

theorem unitFamilyMap_equivariant (X : NormContinuousSpace K H) (h : H) :
    localActionMap H X h ≫ unitFamilyMap H X =
      unitFamilyMap H X ≫ actionMap H X.unop (h : G) := by
  apply AffinoidFamily.Hom.ext
    (f := localActionMap H X h ≫ unitFamilyMap H X)
    (g := unitFamilyMap H X ≫ actionMap H X.unop (h : G))
    (funext fun _ => (identityCoset_smul H h).symm)
  apply heq_of_eq
  funext i
  apply BoundedAlgHom.ext
  intro a
  have he : h⁻¹ * identityRepresentative H = identityRepresentative H *
      (correction H (h : G) (identityCoset H))⁻¹ := by
    rw [correction_identityCoset]
    simp [mul_inv_rev, mul_assoc]
  change ((X.unop.actionAut h⁻¹ * X.unop.actionAut (identityRepresentative H)).hom).toAlgHom a =
    ((X.unop.actionAut (identityRepresentative H) *
      X.unop.actionAut (correction H (h : G) (identityCoset H))⁻¹).hom).toAlgHom a
  rw [← map_mul, ← map_mul, he]

theorem unitFamilyMap_naturality {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    localFamilyMap H f ≫ unitFamilyMap H Y = unitFamilyMap H X ≫ familyMap H f := by
  apply AffinoidFamily.Hom.ext
    (f := localFamilyMap H f ≫ unitFamilyMap H Y)
    (g := unitFamilyMap H X ≫ familyMap H f) rfl
  apply heq_of_eq
  funext i
  apply BoundedAlgHom.ext
  intro a
  exact NormContinuousAction.homMap_apply_action f.unop (identityRepresentative H) a

/-- A natural bounded subgroup-equivariant unit into the induced family action. -/
def familyUnit : localFunctor (K := K) H ⟶
    functor H ⋙ Action.res (AffinoidFamily.{u, v} K) H.subtype where
  app X := ⟨unitFamilyMap H X, unitFamilyMap_equivariant H X⟩
  naturality _ _ f := Action.Hom.ext (unitFamilyMap_naturality H f)

/-- The forward operator pulls points back by the inverse representative action. -/
theorem unitFamilyMap_spectrumMap (X : NormContinuousSpace K H)
    (x : LocalSpectrum H X.unop) :
    (unitFamilyMap H X).spectrumMap ⟨PUnit.unit, x⟩ =
      ⟨identityCoset H, (identityRepresentative H)⁻¹ • x⟩ := by
  have he : BanachSpectrum.comap
      (X.unop.actionAut (identityRepresentative H)).hom.toBoundedRingHom x =
      (identityRepresentative H)⁻¹ • x := by
    change BanachSpectrum.comap
        (X.unop.actionAut (identityRepresentative H)).hom.toBoundedRingHom x =
      BanachSpectrum.comap
        (X.unop.actionAut (identityRepresentative H)⁻¹).inv.toBoundedRingHom x
    rw [map_inv]
    rfl
  exact congrArg (fun y : LocalSpectrum H X.unop =>
    (⟨identityCoset H, y⟩ : (family H X.unop).Space)) he

variable [IsTopologicalGroup G] (hH : IsOpen (H : Set G))

/-- The actual unit is normalized on the balanced quotient, independently of out. -/
theorem unitFamilyMap_realization (X : NormContinuousSpace K H) (x : LocalSpectrum H X.unop) :
    spectrumHomeomorph H X.unop hH ((unitFamilyMap H X).spectrumMap ⟨PUnit.unit, x⟩) =
      TopologicalInduction.unit H x := by
  rw [unitFamilyMap_spectrumMap]
  change TopologicalInduction.mk H (identityRepresentative H : G)
      ((identityRepresentative H)⁻¹ • x) = TopologicalInduction.mk H 1 x
  simpa using (TopologicalInduction.mk_subgroup_smul
    (H := H) (identityRepresentative H)⁻¹ (1 : G) x)

variable [CompleteSpace K]

/-- Realize the original action on the disjoint atlas of its one-component family. -/
def localAtlasFunctor : NormContinuousSpace K H ⥤
    Action (AffinoidAtlasPresentation.{u, max u v, v} K) H :=
  localFunctor H ⋙ (AffinoidFamily.atlasFunctor (K := K)).mapAction H

/-- The actual normalized unit retains a bounded pullback on the original algebra. -/
def unitAtlasMap (X : NormContinuousSpace K H) :
    (localFamily H X).atlasPresentation ⟶ atlasPresentation H hH X :=
  (unitFamilyMap H X).atlasMap ≫ atlasComparisonHom H hH X

/-- Subgroup equivariance compares all bounded atlas morphism data. -/
theorem unitAtlasMap_equivariant (X : NormContinuousSpace K H) (h : H) :
    (localActionMap H X h).atlasMap ≫ unitAtlasMap H hH X =
      unitAtlasMap H hH X ≫ atlasActionMap H hH X (h : G) := by
  unfold unitAtlasMap
  rw [← Category.assoc, ← AffinoidFamily.Hom.atlasMap_comp,
    unitFamilyMap_equivariant, AffinoidFamily.Hom.atlasMap_comp,
    Category.assoc, atlasComparisonHom_equivariant, ← Category.assoc]

/-- Every original equivariant bounded arrow commutes with the complete atlas unit. -/
theorem unitAtlasMap_naturality {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    (localFamilyMap H f).atlasMap ≫ unitAtlasMap H hH Y =
      unitAtlasMap H hH X ≫ atlasMap H hH f := by
  unfold unitAtlasMap
  rw [← Category.assoc, ← AffinoidFamily.Hom.atlasMap_comp,
    unitFamilyMap_naturality, AffinoidFamily.Hom.atlasMap_comp,
    Category.assoc, atlasComparisonHom_naturality, ← Category.assoc]

/-- A natural subgroup-equivariant bounded atlas unit for actual affinoid induction. -/
def equivariantAtlasUnit : localAtlasFunctor (K := K) H ⟶
    equivariantAtlasFunctor H hH ⋙
      Action.res (AffinoidAtlasPresentation.{u, max u v, v} K) H.subtype where
  app X := ⟨unitAtlasMap H hH X, unitAtlasMap_equivariant H hH X⟩
  naturality _ _ f := Action.Hom.ext (unitAtlasMap_naturality H hH f)

@[simp]
theorem unitAtlasMap_indexMap (X : NormContinuousSpace K H)
    (i : (localFamily H X).atlas.Index) :
    ((unitAtlasMap H hH X).indexMap i).val = identityCoset H := rfl

/-- The chart pullback is the forward bounded operator at the chosen representative. -/
@[simp]
theorem unitAtlasMap_pullback (X : NormContinuousSpace K H)
    (i : (localFamily H X).atlas.Index) :
    (unitAtlasMap H hH X).pullback i =
      (X.unop.actionAut (identityRepresentative H)).hom :=
  BoundedAlgHom.ext fun _ => rfl

/-- The continuous base map is exactly the balanced-quotient unit x mapped to [1,x]. -/
@[simp]
theorem unitAtlasMap_baseMap_apply (X : NormContinuousSpace K H)
    (x : LocalSpectrum H X.unop) :
    (unitAtlasMap H hH X).baseMap ⟨PUnit.unit, x⟩ = TopologicalInduction.unit H x :=
  unitFamilyMap_realization H hH X x

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
