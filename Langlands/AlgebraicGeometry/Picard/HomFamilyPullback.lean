import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Rigidified-family pullback along an abelian-scheme homomorphism -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

variable {S : Scheme.{u}} {A B C : AbelianScheme S}

@[simp]
lemma unitSection_hom (f : A ⟶ B) :
    unitSection A ≫ hom f = unitSection B := by
  exact congrArg (fun k : Over.mk (𝟙 S) ⟶ B.X ↦ k.left)
    (map_one (((GroupScheme.pointsMap (groupHom f)).app (op (Over.mk (𝟙 S)))).hom))

/-- The actual map `T ×_S A → T ×_S B`, natural in the parameter scheme. -/
def homFamilySpaceMap (f : A ⟶ B) :
    relativeSpace A.X.hom ⟶ relativeSpace B.X.hom where
  app T := pullback.lift (pullback.fst T.hom A.X.hom)
    (pullback.snd T.hom A.X.hom ≫ hom f) (by
      rw [Category.assoc, (groupHom f).hom.hom.w]
      exact pullback.condition)
  naturality {T U} h := by
    apply pullback.hom_ext
    · simp [relativeSpace, Over.pullback, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp [relativeSpace, Over.pullback, pullback.lift_snd,
        pullback.lift_snd_assoc]

@[reassoc (attr := simp)]
lemma homFamilySpaceMap_fst (f : A ⟶ B) (T : Over S) :
    (homFamilySpaceMap f).app T ≫ pullback.fst T.hom B.X.hom =
      pullback.fst T.hom A.X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma homFamilySpaceMap_snd (f : A ⟶ B) (T : Over S) :
    (homFamilySpaceMap f).app T ≫ pullback.snd T.hom B.X.hom =
      pullback.snd T.hom A.X.hom ≫ hom f :=
  pullback.lift_snd _ _ _

@[simp]
lemma relativeSection_homFamilySpaceMap (f : A ⟶ B) (T : Over S) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
      (homFamilySpaceMap f).app T =
    (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app T := by
  apply pullback.hom_ext
  · simp [Category.assoc, relativeSection, pullback.lift_fst]
  · simp [Category.assoc, relativeSection, pullback.lift_snd_assoc, pullback.lift_snd]

@[simp]
lemma homFamilySpaceMap_id (A : AbelianScheme S) (T : Over S) :
    (homFamilySpaceMap (𝟙 A)).app T = 𝟙 ((relativeSpace A.X.hom).obj T) := by
  apply pullback.hom_ext <;> simp

@[simp]
lemma homFamilySpaceMap_comp (f : A ⟶ B) (g : B ⟶ C) (T : Over S) :
    (homFamilySpaceMap (f ≫ g)).app T =
      (homFamilySpaceMap f).app T ≫ (homFamilySpaceMap g).app T := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Pull back actual rigidified line bundles using preservation of the unit section. -/
def homFamilyPullback (f : A ⟶ B) (T : Over S) :
    RigidifiedFamily B T ⥤ RigidifiedFamily A T :=
  RigidifiedLineBundle.pullback ((homFamilySpaceMap f).app T) (𝟙 T.left)
    (by simp)

/-- The induced contravariant map on isomorphism classes of rigidified families. -/
def homClassesPullback (f : A ⟶ B) (T : Over S) :
    RigidifiedClasses B T → RigidifiedClasses A T :=
  Quotient.map (homFamilyPullback f T).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(homFamilyPullback f T).mapIso e⟩)

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

/-- Identity comparison for pullback along an abelian-scheme homomorphism. -/
def homFamilyPullbackId (A : AbelianScheme S) (T : Over S) :
    homFamilyPullback (𝟙 A) T ≅ 𝟭 (RigidifiedFamily A T) :=
  RigidifiedLineBundle.pullbackCongr (homFamilySpaceMap_id A T) rfl _ _ ≪≫
    RigidifiedLineBundle.pullbackId coherence _

/-- Composition comparison for actual pullback of rigidified families. -/
def homFamilyPullbackComp (f : A ⟶ B) (g : B ⟶ C) (T : Over S) :
    homFamilyPullback g T ⋙ homFamilyPullback f T ≅
      homFamilyPullback (f ≫ g) T :=
  RigidifiedLineBundle.pullbackComp coherence
    ((homFamilySpaceMap g).app T) (𝟙 T.left)
    ((homFamilySpaceMap f).app T) (𝟙 T.left) _ _
    (by simp [← Category.assoc]) ≪≫
    RigidifiedLineBundle.pullbackCongr (homFamilySpaceMap_comp f g T).symm
      (Category.id_comp _) _ _

include coherence in
lemma homClassesPullback_id (A : AbelianScheme S) (T : Over S)
    (q : RigidifiedClasses A T) :
    homClassesPullback (𝟙 A) T q = q := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨(homFamilyPullbackId coherence A T).app L⟩

include coherence in
lemma homClassesPullback_comp (f : A ⟶ B) (g : B ⟶ C) (T : Over S)
    (q : RigidifiedClasses C T) :
    homClassesPullback (f ≫ g) T q =
      homClassesPullback f T (homClassesPullback g T q) := by
  refine Quotient.inductionOn q (fun L ↦ ?_)
  exact Quotient.sound ⟨((homFamilyPullbackComp coherence f g T).app L).symm⟩

end Langlands.AbelianScheme
