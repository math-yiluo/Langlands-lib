import Langlands.AlgebraicGeometry.Picard.HomFamilyPullback
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # Families with trivial homomorphism pullback -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)

/-- An actual line bundle on `T ×_S B` has trivial pullback along the actual `f_T`. -/
def HasTrivialHomPullback (T : Over S) (L : LineBundle ((relativeSpace B.X.hom).obj T)) :
    Prop :=
  Nonempty ((Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj L.obj ≅
    SheafOfModules.unit ((relativeSpace A.X.hom).obj T).ringCatSheaf)

/-- The condition depends only on the actual line-bundle isomorphism class. -/
lemma hasTrivialHomPullback_iff_of_iso (T : Over S)
    {L M : LineBundle ((relativeSpace B.X.hom).obj T)} (e : L ≅ M) :
    HasTrivialHomPullback f T L ↔ HasTrivialHomPullback f T M := by
  constructor
  · rintro ⟨α⟩
    exact ⟨((Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).mapIso
      ((LineBundle.forget _).mapIso e)).symm ≪≫ α⟩
  · rintro ⟨α⟩
    exact ⟨(Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).mapIso
      ((LineBundle.forget _).mapIso e) ≪≫ α⟩

/-- The actual commutative square identifies the two orders of module pullback. -/
def homFamilyModulePullbackIso {U T : Over S} (a : U ⟶ T)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) :
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app U)).obj
        ((Scheme.Modules.pullback ((relativeSpace B.X.hom).map a)).obj L.obj) ≅
      (Scheme.Modules.pullback ((relativeSpace A.X.hom).map a)).obj
        ((Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj L.obj) :=
  (Scheme.Modules.pullbackComp ((homFamilySpaceMap f).app U)
      ((relativeSpace B.X.hom).map a)).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr ((homFamilySpaceMap f).naturality a).symm).app L.obj ≪≫
      ((Scheme.Modules.pullbackComp ((relativeSpace A.X.hom).map a)
        ((homFamilySpaceMap f).app T)).app L.obj).symm

/-- Change of test scheme preserves the existence of an actual trivialization. -/
lemma hasTrivialHomPullback_pullback {U T : Over S} (a : U ⟶ T)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    HasTrivialHomPullback f U ((LineBundle.pullback ((relativeSpace B.X.hom).map a)).obj L) := by
  obtain ⟨α⟩ := hL
  exact ⟨homFamilyModulePullbackIso f a L ≪≫
    (Scheme.Modules.pullback ((relativeSpace A.X.hom).map a)).mapIso α ≪≫
      Langlands.Scheme.Modules.pullbackUnitIso ((relativeSpace A.X.hom).map a)⟩

/-- The trivial line bundle has an actual trivial homomorphism pullback. -/
lemma hasTrivialHomPullback_trivial (T : Over S) :
    HasTrivialHomPullback f T (LineBundle.trivial ((relativeSpace B.X.hom).obj T)) :=
  ⟨Langlands.Scheme.Modules.pullbackUnitIso ((homFamilySpaceMap f).app T)⟩

/-- Actual line bundles with trivial homomorphism pullback; no trivialization is chosen. -/
abbrev TrivialHomPullbackFamily (T : Over S) :=
  ObjectProperty.FullSubcategory (HasTrivialHomPullback f T)

/-- Forget the existence-of-trivialization property. -/
def trivialHomPullbackForget (T : Over S) :
    TrivialHomPullbackFamily f T ⥤ LineBundle ((relativeSpace B.X.hom).obj T) :=
  ObjectProperty.ι (HasTrivialHomPullback f T)

/-- Restrict actual families using the usual pullback of line bundles. -/
def trivialHomPullbackRestriction {U T : Over S} (a : U ⟶ T) :
    TrivialHomPullbackFamily f T ⥤ TrivialHomPullbackFamily f U :=
  ObjectProperty.lift (HasTrivialHomPullback f U)
    (trivialHomPullbackForget f T ⋙ LineBundle.pullback ((relativeSpace B.X.hom).map a))
    (fun L ↦ hasTrivialHomPullback_pullback f a L.obj L.property)

/-- Isomorphism classes of actual families satisfying the trivial-pullback condition. -/
abbrev TrivialHomPullbackClasses (T : Over S) :=
  Quotient (isIsomorphicSetoid (TrivialHomPullbackFamily f T))

/-- The class of an actual line bundle with the stated property. -/
def trivialHomPullbackClassOf {T : Over S}
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    TrivialHomPullbackClasses f T :=
  Quotient.mk _ ⟨L, hL⟩

/-- Pullback on isomorphism classes of the input families. -/
def trivialHomPullbackClassesRestrict {U T : Over S} (a : U ⟶ T) :
    TrivialHomPullbackClasses f T → TrivialHomPullbackClasses f U :=
  Quotient.map (trivialHomPullbackRestriction f a).obj
    (fun _ _ ⟨e⟩ ↦ ⟨(trivialHomPullbackRestriction f a).mapIso e⟩)

@[simp]
lemma trivialHomPullbackClassesRestrict_classOf {U T : Over S} (a : U ⟶ T)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    trivialHomPullbackClassesRestrict f a (trivialHomPullbackClassOf f L hL) =
      trivialHomPullbackClassOf f
        ((LineBundle.pullback ((relativeSpace B.X.hom).map a)).obj L)
        (hasTrivialHomPullback_pullback f a L hL) := rfl

/-- Classes forget every choice of a pullback trivialization and preserve bundle isomorphism. -/
lemma trivialHomPullbackClassOf_eq_of_iso {T : Over S}
    {L M : LineBundle ((relativeSpace B.X.hom).obj T)}
    (hL : HasTrivialHomPullback f T L) (hM : HasTrivialHomPullback f T M) (e : L ≅ M) :
    trivialHomPullbackClassOf f L hL = trivialHomPullbackClassOf f M hM :=
  Quotient.sound ⟨ObjectProperty.isoMk _ e⟩

/-- The identity restriction is the identity on classes. -/
lemma trivialHomPullbackClassesRestrict_id (T : Over S) (q : TrivialHomPullbackClasses f T) :
    trivialHomPullbackClassesRestrict f (𝟙 T) q = q := by
  refine Quotient.inductionOn q fun L ↦ ?_
  apply Quotient.sound
  refine ⟨ObjectProperty.isoMk _ ?_⟩
  change (LineBundle.pullback ((relativeSpace B.X.hom).map (𝟙 T))).obj L.obj ≅ L.obj
  rw [(relativeSpace B.X.hom).map_id]
  exact (LineBundle.pullbackId _).app L.obj

/-- Restriction of classes composes contravariantly. -/
lemma trivialHomPullbackClassesRestrict_comp {V U T : Over S} (a : V ⟶ U) (b : U ⟶ T)
    (q : TrivialHomPullbackClasses f T) :
    trivialHomPullbackClassesRestrict f (a ≫ b) q =
      trivialHomPullbackClassesRestrict f a (trivialHomPullbackClassesRestrict f b q) := by
  refine Quotient.inductionOn q fun L ↦ ?_
  apply Quotient.sound
  refine ⟨ObjectProperty.isoMk _ ?_⟩
  change (LineBundle.pullback ((relativeSpace B.X.hom).map (a ≫ b))).obj L.obj ≅
    (LineBundle.pullback ((relativeSpace B.X.hom).map a)).obj
      ((LineBundle.pullback ((relativeSpace B.X.hom).map b)).obj L.obj)
  rw [(relativeSpace B.X.hom).map_comp]
  exact ((LineBundle.pullbackComp _ _).app L.obj).symm

/-- The input presheaf for the intrinsic character: actual trivial-pullback bundle classes. -/
def trivialHomPullbackClassPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := TrivialHomPullbackClasses f T.unop
  map a := TypeCat.ofHom (trivialHomPullbackClassesRestrict f a.unop)
  map_id T := by
    ext q
    exact trivialHomPullbackClassesRestrict_id f T.unop q
  map_comp a b := by
    ext q
    exact trivialHomPullbackClassesRestrict_comp f b.unop a.unop q

end Langlands.AbelianScheme
