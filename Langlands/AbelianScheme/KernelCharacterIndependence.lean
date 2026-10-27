import Langlands.AbelianScheme.IntrinsicKernelCharacter

/-! # Independence of the intrinsic kernel character -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule

/-- Changing a pullback trivialization conjugates the canonical comparison by
its two pulled-back structure-module automorphisms. -/
lemma equalCompositeUnitAut_change_trivialization {U X Y : Scheme.{u}}
    (p : X ⟶ Y) (a b : U ⟶ X) (hab : a ≫ p = b ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ structureModule X)
    (e : structureModule X ≅ structureModule X) :
    equalCompositeUnitAut p a b hab (α ≪≫ e) =
      (structureAutPullback a e).symm ≪≫ equalCompositeUnitAut p a b hab α ≪≫
        structureAutPullback b e := by
  ext1
  simp [equalCompositeUnitAut, structureAutPullback]

end Langlands.Scheme.Modules

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} {M N : ((relativeSpace B.X.hom).obj T).Modules}
  (α β : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (h : UniversalGlobalFunctions A)

include h

/-- An ordinary family map and its kernel translate pull back every global unit
identically, because every such unit comes from the parameter scheme. -/
lemma kernelShear_units_eq {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X)
    (c : Γ((relativeSpace A.X.hom).obj T, ⊤)ˣ) :
    Units.map ((relativeSpace A.X.hom).map a).appTop.hom.toMonoidHom c =
      Units.map (kernelShear f a k).appTop.hom.toMonoidHom c := by
  rw [← relativeUnitsPullback_descend A h T c,
    relativeUnitsPullback_map A a _ ((relativeProjection A.X.hom).naturality a),
    relativeUnitsPullback_map A a _ (kernelShear_fst f a k)]

/-- The actual scalar of the canonical action is independent of its trivialization. -/
lemma kernelTranslationScalar_independent {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f α a k = kernelTranslationScalar f β a k := by
  let e := α.symm ≪≫ β
  have he : β = α ≪≫ e := by simp [e]
  rw [he]
  unfold kernelTranslationScalar kernelTranslationAut
  rw [equalCompositeUnitAut_change_trivialization]
  rw [structureAutScalar_trans, structureAutScalar_trans, structureAutScalar_symm,
    structureAutScalar_pullback, structureAutScalar_pullback]
  rw [← kernelShear_units_eq f h a k (structureAutScalar e)]
  simp only [mul_left_comm, inv_mul_cancel, mul_one]

/-- The unique descended parameter unit is independent of its trivialization. -/
lemma kernelTranslationUnit_independent {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f α h a k = kernelTranslationUnit f β h a k := by
  exact congrArg (relativeUnitDescend A h U)
    (kernelTranslationScalar_independent f α β h a k)

/-- Independence holds for the actual homomorphism of group schemes. -/
lemma intrinsicKernelCharacterHom_independent :
    intrinsicKernelCharacterHom f α h = intrinsicKernelCharacterHom f β h := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro U k
  apply (Gm.pointsEquiv T.left U).injective
  rw [intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points]
  exact kernelTranslationUnit_independent f α β h _ _

/-- Independence holds in the existing Cartier character presheaf. -/
lemma intrinsicKernelCharacter_independent :
    intrinsicKernelCharacter f α h = intrinsicKernelCharacter f β h := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).injective
  rw [characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter]
  exact intrinsicKernelCharacterHom_independent f α β h

/-- Isomorphic modules give the same scalar after any choices of trivialization. -/
lemma kernelTranslationScalar_of_iso (e : M ≅ N)
    (alphaN : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj N ≅
      structureModule ((relativeSpace A.X.hom).obj T))
    {U : Over S} (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f α a k = kernelTranslationScalar f alphaN a k := by
  rw [kernelTranslationScalar_independent f α
    ((Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).mapIso e ≪≫ alphaN) h]
  unfold kernelTranslationScalar kernelTranslationAut
  rw [equalCompositeUnitAut_of_iso]

/-- Isomorphic modules give the same actual character for arbitrary trivializations. -/
lemma intrinsicKernelCharacter_of_iso (e : M ≅ N)
    (alphaN : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj N ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    intrinsicKernelCharacter f α h = intrinsicKernelCharacter f alphaN h := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).injective
  rw [characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter]
  apply Additive.toMul.injective
  apply hom_ext_points
  intro U k
  apply (Gm.pointsEquiv T.left U).injective
  rw [intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points]
  unfold kernelTranslationUnit
  rw [kernelTranslationScalar_of_iso f α h e alphaN]

/-- An actual line bundle with a trivial homomorphism pullback has a canonical character. -/
def trivialHomPullbackCharacter (L : LineBundle ((relativeSpace B.X.hom).obj T))
    (hL : HasTrivialHomPullback f T L) :
    (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  intrinsicKernelCharacter f hL.some h

/-- The canonical character can be computed using any actual trivialization. -/
lemma trivialHomPullbackCharacter_eq (L : LineBundle ((relativeSpace B.X.hom).obj T))
    (hL : HasTrivialHomPullback f T L)
    (alphaN : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj L.obj ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    trivialHomPullbackCharacter f h L hL = intrinsicKernelCharacter f alphaN h :=
  intrinsicKernelCharacter_independent f hL.some alphaN h

/-- The canonical character depends only on the actual line-bundle isomorphism class. -/
lemma trivialHomPullbackCharacter_of_iso
    {L K : LineBundle ((relativeSpace B.X.hom).obj T)}
    (hL : HasTrivialHomPullback f T L) (hK : HasTrivialHomPullback f T K) (e : L ≅ K) :
    trivialHomPullbackCharacter f h L hL = trivialHomPullbackCharacter f h K hK :=
  intrinsicKernelCharacter_of_iso f hL.some h ((LineBundle.forget _).mapIso e) hK.some

/-- The intrinsic character map on isomorphism classes, without a trivialization choice. -/
def trivialHomPullbackClassCharacter : TrivialHomPullbackClasses f T →
    (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  Quotient.lift (fun L ↦ trivialHomPullbackCharacter f h L.obj L.property)
    (by
      intro L K e
      obtain ⟨e⟩ := e
      exact trivialHomPullbackCharacter_of_iso f h L.property K.property
        ((trivialHomPullbackForget f T).mapIso e))

@[simp]
lemma trivialHomPullbackClassCharacter_classOf
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    trivialHomPullbackClassCharacter f h (trivialHomPullbackClassOf f L hL) =
      trivialHomPullbackCharacter f h L hL := rfl

end Langlands.AbelianScheme
