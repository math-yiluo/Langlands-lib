import Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityStatement

/-! # Comparing cube products with the relative rigidified family -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (X : Over S)

/-- The relative space `T ×_S X` is the underlying scheme of the actual product `X ⨯ T`. -/
def relativeSpaceProdIso (T : Over S) :
    (relativeSpace X.hom).obj T ≅ (X ⨯ T).left :=
  relativeSpaceSymmetry X.hom T ≪≫ (Over.prodLeftIsoPullback X T).symm

@[reassoc (attr := simp)]
lemma relativeSpaceProdIso_hom_fst (T : Over S) :
    (relativeSpaceProdIso X T).hom ≫ (prod.fst : X ⨯ T ⟶ X).left =
      pullback.snd T.hom X.hom := by
  simp [relativeSpaceProdIso, relativeSpaceSymmetry]

@[reassoc (attr := simp)]
lemma relativeSpaceProdIso_hom_snd (T : Over S) :
    (relativeSpaceProdIso X T).hom ≫ (prod.snd : X ⨯ T ⟶ T).left =
      (relativeProjection X.hom).app T := by
  simp [relativeSpaceProdIso, relativeSpaceSymmetry, relativeProjection]

@[reassoc (attr := simp)]
lemma relativeSpaceProdIso_inv_snd (T : Over S) :
    (relativeSpaceProdIso X T).inv ≫ pullback.snd T.hom X.hom =
      (prod.fst : X ⨯ T ⟶ X).left := by
  rw [← relativeSpaceProdIso_hom_fst, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma relativeSpaceProdIso_inv_projection (T : Over S) :
    (relativeSpaceProdIso X T).inv ≫ (relativeProjection X.hom).app T =
      (prod.snd : X ⨯ T ⟶ T).left := by
  rw [← relativeSpaceProdIso_hom_snd, Iso.inv_hom_id_assoc]

/-- Naturality of the comparison for an actual morphism of `S`-schemes. -/
@[reassoc]
lemma relativeSpaceProdIso_naturality {T U : Over S} (h : T ⟶ U) :
    (relativeSpace X.hom).map h ≫ (relativeSpaceProdIso X U).hom =
      (relativeSpaceProdIso X T).hom ≫ (prod.map (𝟙 X) h).left := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X U)).hom_ext
  · simp [relativeSpace, Over.pullback, ← Over.comp_left, Category.assoc,
      pullback.lift_snd]
  · simp [relativeProjection, relativeSpace, Over.pullback, ← Over.comp_left,
      Category.assoc, pullback.lift_fst]
    simp [Over.comp_left, relativeProjection]

/-- A section in the slice category supplies the ordinary section law. -/
lemma overSection_comp (x₀ : Over.mk (𝟙 S) ⟶ X) :
    x₀.left ≫ X.hom = 𝟙 S :=
  x₀.w

/-- The induced relative section is the product map inserting the chosen section. -/
@[reassoc]
lemma relativeSection_prodIso (x₀ : Over.mk (𝟙 S) ⟶ X) (T : Over S) :
    (relativeSection X.hom x₀.left (overSection_comp X x₀)).app T ≫
        (relativeSpaceProdIso X T).hom =
      (prod.lift (Over.mkIdTerminal.from T ≫ x₀) (𝟙 T)).left := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X T)).hom_ext
  · simp [← Over.comp_left]
    simp [Over.comp_left]
  · simp [← Over.comp_left]

/-- The first cube face is the relative section under the comparison. -/
lemma relativeSection_cubeFirst (Y Z : Over S) (x₀ : Over.mk (𝟙 S) ⟶ X) :
    (relativeSection X.hom x₀.left (overSection_comp X x₀)).app (Y ⨯ Z) ≫
        (relativeSpaceProdIso X (Y ⨯ Z)).hom =
      (CubeFace.first X Y Z x₀).left :=
  relativeSection_prodIso X x₀ (Y ⨯ Z)

namespace CubeFace

/-- The actual pointed axis in `Y ⨯ Z` obtained by fixing the `Y` coordinate. -/
def secondAxis (Y Z : Over S) (y₀ : Over.mk (𝟙 S) ⟶ Y) : Z ⟶ Y ⨯ Z :=
  prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z)

/-- The actual pointed axis in `Y ⨯ Z` obtained by fixing the `Z` coordinate. -/
def thirdAxis (Y Z : Over S) (z₀ : Over.mk (𝟙 S) ⟶ Z) : Y ⟶ Y ⨯ Z :=
  prod.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀)

lemma map_secondAxis (Y Z : Over S) (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    prod.map (𝟙 X) (secondAxis Y Z y₀) = second X Y Z y₀ := by
  apply prod.hom_ext
  · simp [second]
  · apply prod.hom_ext <;>
      simp [second, secondAxis, ← Category.assoc, Over.mkIdTerminal.comp_from]

lemma map_thirdAxis (Y Z : Over S) (z₀ : Over.mk (𝟙 S) ⟶ Z) :
    prod.map (𝟙 X) (thirdAxis Y Z z₀) = third X Y Z z₀ := by
  apply prod.hom_ext
  · simp [third]
  · apply prod.hom_ext <;>
      simp [third, thirdAxis, ← Category.assoc, Over.mkIdTerminal.comp_from]

end CubeFace

/-- Restriction along the first pointed axis becomes the second actual cube face. -/
lemma relativeSpaceProdIso_cubeSecond (Y Z : Over S)
    (y₀ : Over.mk (𝟙 S) ⟶ Y) :
    (relativeSpace X.hom).map (CubeFace.secondAxis Y Z y₀) ≫
        (relativeSpaceProdIso X (Y ⨯ Z)).hom =
      (relativeSpaceProdIso X Z).hom ≫ (CubeFace.second X Y Z y₀).left := by
  rw [relativeSpaceProdIso_naturality, CubeFace.map_secondAxis]

/-- Restriction along the other pointed axis becomes the third actual cube face. -/
lemma relativeSpaceProdIso_cubeThird (Y Z : Over S)
    (z₀ : Over.mk (𝟙 S) ⟶ Z) :
    (relativeSpace X.hom).map (CubeFace.thirdAxis Y Z z₀) ≫
        (relativeSpaceProdIso X (Y ⨯ Z)).hom =
      (relativeSpaceProdIso X Y).hom ≫ (CubeFace.third X Y Z z₀).left := by
  rw [relativeSpaceProdIso_naturality, CubeFace.map_thirdAxis]

namespace CubeRelativeTransport

/-- The actual module-sheaf pullback comparison induced by any commuting square. -/
def pullbackSquareIso {A B C D : Scheme.{u}} (f : A ⟶ B) (i : B ⟶ D)
    (j : A ⟶ C) (g : C ⟶ D) (comm : f ≫ i = j ≫ g) (M : D.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback i).obj M) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp f i).app M ≪≫
    (Scheme.Modules.pullbackCongr comm).app M ≪≫
      ((Scheme.Modules.pullbackComp j g).app M).symm

/-- An ordinary trivialization transports across a commuting square. -/
def pullbackSquareTrivialization {A B C D : Scheme.{u}} (f : A ⟶ B) (i : B ⟶ D)
    (j : A ⟶ C) (g : C ⟶ D) (comm : f ≫ i = j ≫ g) (M : D.Modules)
    (τ : (Scheme.Modules.pullback g).obj M ≅ Langlands.Scheme.Modules.structureSheaf C) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback i).obj M) ≅
      Langlands.Scheme.Modules.structureSheaf A :=
  pullbackSquareIso f i j g comm M ≪≫
    (Scheme.Modules.pullback j).mapIso τ ≪≫ Langlands.Scheme.Modules.pullbackUnitIso j

/-- Recover an ordinary trivialization from its pullback along a scheme isomorphism. -/
def recoverTrivialization {A B : Scheme.{u}} (i : A ≅ B) (M : B.Modules)
    (τ : (Scheme.Modules.pullback i.hom).obj M ≅
      Langlands.Scheme.Modules.structureSheaf A) :
    M ≅ Langlands.Scheme.Modules.structureSheaf B :=
  ((Scheme.Modules.pullbackId B).app M).symm ≪≫
    ((Scheme.Modules.pullbackCongr i.inv_hom_id).app M).symm ≪≫
      ((Scheme.Modules.pullbackComp i.inv i.hom).app M).symm ≪≫
        (Scheme.Modules.pullback i.inv).mapIso τ ≪≫
          Langlands.Scheme.Modules.pullbackUnitIso i.inv

/-- An actual line bundle on `X ⨯ T`, transported to the relative space. -/
def relativeLineBundle (T : Over S) (L : LineBundle (X ⨯ T).left) :
    LineBundle ((relativeSpace X.hom).obj T) :=
  (LineBundle.pullback (relativeSpaceProdIso X T).hom).obj L

/-- Pullback by the relative section is pullback by the actual first-coordinate face. -/
def sectionPullbackIso (x₀ : Over.mk (𝟙 S) ⟶ X) (T : Over S)
    (M : (X ⨯ T).left.Modules) :
    (Scheme.Modules.pullback
      ((relativeSection X.hom x₀.left (overSection_comp X x₀)).app T)).obj
        ((Scheme.Modules.pullback (relativeSpaceProdIso X T).hom).obj M) ≅
      (Scheme.Modules.pullback
        (prod.lift (Over.mkIdTerminal.from T ≫ x₀) (𝟙 T)).left).obj M :=
  (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (relativeSection_prodIso X x₀ T)).app M

/-- A first-coordinate trivialization rigidifies the transported actual line bundle. -/
def rigidify (x₀ : Over.mk (𝟙 S) ⟶ X) (T : Over S)
    (L : LineBundle (X ⨯ T).left)
    (τ : (Scheme.Modules.pullback
      (prod.lift (Over.mkIdTerminal.from T ≫ x₀) (𝟙 T)).left).obj L.obj ≅
        Langlands.Scheme.Modules.structureSheaf T.left) :
    RigidifiedLineBundle.relative X.hom x₀.left (overSection_comp X x₀) T :=
  RigidifiedLineBundle.ofLineBundle (relativeLineBundle X T L)
    (sectionPullbackIso X x₀ T L.obj ≪≫ τ).symm

/-- The comparison on actual modules for every relative restriction. -/
def restrictionPullbackIso {T U : Over S} (h : T ⟶ U)
    (M : (X ⨯ U).left.Modules) :
    (Scheme.Modules.pullback ((relativeSpace X.hom).map h)).obj
      ((Scheme.Modules.pullback (relativeSpaceProdIso X U).hom).obj M) ≅
        (Scheme.Modules.pullback (relativeSpaceProdIso X T).hom).obj
          ((Scheme.Modules.pullback (prod.map (𝟙 X) h).left).obj M) :=
  pullbackSquareIso _ _ _ _ (relativeSpaceProdIso_naturality X h) M

/-- The first cube face equips the relative cube family with its rigidification. -/
abbrev cubeRigidified (Y Z : Over S) (x₀ : Over.mk (𝟙 S) ⟶ X)
    (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (τ₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left) :
    RigidifiedLineBundle.relative X.hom x₀.left (overSection_comp X x₀) (Y ⨯ Z) :=
  rigidify X x₀ (Y ⨯ Z) L τ₁

/-- Ordinary second-face triviality gives ordinary triviality of the relative restriction. -/
def cubeSecondTrivialization (Y Z : Over S) (x₀ : Over.mk (𝟙 S) ⟶ X)
    (y₀ : Over.mk (𝟙 S) ⟶ Y) (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (τ₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left)
    (τ₂ : (Scheme.Modules.pullback (CubeFace.second X Y Z y₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (X ⨯ Z).left) :
    ((RigidifiedLineBundle.relativePullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.secondAxis Y Z y₀)).obj (cubeRigidified X Y Z x₀ L τ₁)).obj.carrier ≅
        Langlands.Scheme.Modules.structureSheaf ((relativeSpace X.hom).obj Z) :=
  pullbackSquareTrivialization _ _ _ _
    (relativeSpaceProdIso_cubeSecond X Y Z y₀) L.obj τ₂

/-- Ordinary third-face triviality gives ordinary triviality of the other restriction. -/
def cubeThirdTrivialization (Y Z : Over S) (x₀ : Over.mk (𝟙 S) ⟶ X)
    (z₀ : Over.mk (𝟙 S) ⟶ Z) (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (τ₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left)
    (τ₃ : (Scheme.Modules.pullback (CubeFace.third X Y Z z₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (X ⨯ Y).left) :
    ((RigidifiedLineBundle.relativePullback X.hom x₀.left (overSection_comp X x₀)
      (CubeFace.thirdAxis Y Z z₀)).obj (cubeRigidified X Y Z x₀ L τ₁)).obj.carrier ≅
        Langlands.Scheme.Modules.structureSheaf ((relativeSpace X.hom).obj Y) :=
  pullbackSquareTrivialization _ _ _ _
    (relativeSpaceProdIso_cubeThird X Y Z z₀) L.obj τ₃

/-- An ordinary trivialization of the relative family recovers one of the original cube. -/
def cubeRecoverTrivialization (Y Z : Over S) (x₀ : Over.mk (𝟙 S) ⟶ X)
    (L : LineBundle (X ⨯ (Y ⨯ Z)).left)
    (τ₁ : (Scheme.Modules.pullback (CubeFace.first X Y Z x₀).left).obj L.obj ≅
      Langlands.Scheme.Modules.structureSheaf (Y ⨯ Z).left)
    (τ : (cubeRigidified X Y Z x₀ L τ₁).obj.carrier ≅
      Langlands.Scheme.Modules.structureSheaf ((relativeSpace X.hom).obj (Y ⨯ Z))) :
    L.obj ≅ Langlands.Scheme.Modules.structureSheaf (X ⨯ (Y ⨯ Z)).left :=
  recoverTrivialization (relativeSpaceProdIso X (Y ⨯ Z)) L.obj τ

end CubeRelativeTransport

end Langlands.AlgebraicGeometry.Picard
