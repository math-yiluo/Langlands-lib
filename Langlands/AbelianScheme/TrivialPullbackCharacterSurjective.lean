import Langlands.AbelianScheme.KernelPairFactorization
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentStatements

/-! # Surjectivity of the normalized character from effective descent -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B) {T : Over S}
  (χ : Cartier.CharacterHom (kernelCommGroupScheme f) T)

/-- The unit on `U` obtained by evaluating a character at a kernel point over `U`. -/
def characterValue {U : Over T.left}
    (k : (Over.map T.hom).obj U ⟶ (GroupScheme.kernel (groupHom f)).X) : Γ(U.left, ⊤)ˣ :=
  Gm.pointsEquiv T.left U
    ((baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U).symm k ≫
      χ.toMul.hom.hom)

lemma characterValue_mul {U : Over T.left}
    (k l : (Over.map T.hom).obj U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    characterValue f χ (k * l) = characterValue f χ k * characterValue f χ l := by
  unfold characterValue
  rw [map_mul, MonObj.mul_comp, map_mul]

lemma characterValue_naturality {U V : Over T.left} (m : V ⟶ U)
    (k : (Over.map T.hom).obj U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    characterValue f χ ((Over.map T.hom).map m ≫ k) =
      Units.map m.left.appTop.hom.toMonoidHom (characterValue f χ k) := by
  unfold characterValue
  have hk : (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp V).symm
      ((Over.map T.hom).map m ≫ k) =
        m ≫ (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U).symm k := by
    apply (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp V).injective
    rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
  rw [hk, Category.assoc, Gm.pointsEquiv_naturality]

variable {U V : Scheme.{u}}

/-- Precomposition as a map of pair parameters. -/
def pairParameterMap (q : V ⟶ U) (a : U ⟶ (relativeSpace A.X.hom).obj T) :
    pairParameter (q ≫ a) ⟶ pairParameter a :=
  Over.homMk q (Category.assoc _ _ _).symm

lemma pairPoint_precomp (q : V ⟶ U) (a c : U ⟶ (relativeSpace A.X.hom).obj T)
    (hc : c ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom)
    (hc' : (q ≫ c) ≫ pullback.fst T.hom A.X.hom = (q ≫ a) ≫ pullback.fst T.hom A.X.hom) :
    (Over.map T.hom).map (pairParameterMap q a) ≫ pairPoint a c hc = pairPoint (q ≫ a) (q ≫ c) hc' := by
  ext
  exact (Category.assoc _ _ _).symm

lemma pairKernelPoint_precomp (q : V ⟶ U) (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T)
    (h' : (q ≫ a) ≫ (homFamilySpaceMap f).app T = (q ≫ b) ≫ (homFamilySpaceMap f).app T) :
    pairKernelPoint f (q ≫ a) (q ≫ b) h' =
      (Over.map T.hom).map (pairParameterMap q a) ≫ pairKernelPoint f a b h := by
  apply (cancel_mono (GroupScheme.kernelι (groupHom f)).hom.hom).mp
  rw [Category.assoc, pairKernelPoint_ι, pairKernelPoint_ι, MonObj.comp_mul, GrpObj.comp_inv,
    pairPoint_precomp, pairPoint_precomp]

/-- The identity map between the parameters of two maps with equal parameter. -/
def pairParameterEq (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (hb : b ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom) :
    pairParameter a ⟶ pairParameter b :=
  Over.homMk (𝟙 U) (by simpa using hb)

lemma pairPoint_eq (a b c : U ⟶ (relativeSpace A.X.hom).obj T)
    (hb : b ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom)
    (hc : c ≫ pullback.fst T.hom A.X.hom = b ≫ pullback.fst T.hom A.X.hom)
    (hc' : c ≫ pullback.fst T.hom A.X.hom = a ≫ pullback.fst T.hom A.X.hom) :
    (Over.map T.hom).map (pairParameterEq a b hb) ≫ pairPoint b c hc = pairPoint a c hc' := by
  ext
  exact Category.id_comp _

/-- Kernel points of consecutive pairs multiply. -/
lemma pairKernelPoint_trans (a b d : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T)
    (h' : b ≫ (homFamilySpaceMap f).app T = d ≫ (homFamilySpaceMap f).app T)
    (h'' : a ≫ (homFamilySpaceMap f).app T = d ≫ (homFamilySpaceMap f).app T) :
    pairKernelPoint f a d h'' =
      ((Over.map T.hom).map (pairParameterEq a b (pair_fst_eq f a b h)) ≫
        pairKernelPoint f b d h') * pairKernelPoint f a b h := by
  apply (cancel_mono (GroupScheme.kernelι (groupHom f)).hom.hom).mp
  rw [MonObj.mul_comp, Category.assoc, pairKernelPoint_ι, pairKernelPoint_ι, pairKernelPoint_ι,
    MonObj.comp_mul, GrpObj.comp_inv, pairPoint_eq, pairPoint_eq, mul_assoc,
    inv_mul_cancel_left]
  exact pair_fst_eq f a b h

/-- The character values of a character on all equal-composite pairs along `f_T`. -/
def pairCharacterValue (U : Scheme.{u}) (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) : Γ(U, ⊤)ˣ :=
  characterValue f χ (pairKernelPoint f a b h)

lemma pairCharacterValue_precomp (q : V ⟶ U) (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T)
    (h' : (q ≫ a) ≫ (homFamilySpaceMap f).app T = (q ≫ b) ≫ (homFamilySpaceMap f).app T) :
    pairCharacterValue f χ V (q ≫ a) (q ≫ b) h' =
      Units.map q.appTop.hom.toMonoidHom (pairCharacterValue f χ U a b h) := by
  unfold pairCharacterValue
  rw [pairKernelPoint_precomp f q a b h h', characterValue_naturality]
  rfl

lemma pairCharacterValue_trans (a b d : U ⟶ (relativeSpace A.X.hom).obj T)
    (h : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T)
    (h' : b ≫ (homFamilySpaceMap f).app T = d ≫ (homFamilySpaceMap f).app T)
    (h'' : a ≫ (homFamilySpaceMap f).app T = d ≫ (homFamilySpaceMap f).app T) :
    pairCharacterValue f χ U a b h * pairCharacterValue f χ U b d h' =
      pairCharacterValue f χ U a d h'' := by
  unfold pairCharacterValue
  rw [pairKernelPoint_trans f a b d h h' h'', characterValue_mul, characterValue_naturality,
    mul_comm]
  congr 1

/-- The projection from the parameter of an ordinary change-of-parameter map. -/
def pairParameterProj (W : Over T.left) :
    pairParameter ((relativeSpace A.X.hom).map (kernelCharacterParameter W)) ⟶ W :=
  Over.homMk (pullback.fst _ A.X.hom)
    (relativeSpace_map_fst A (kernelCharacterParameter W)).symm

/-- The kernel point of the pair given by a kernel translation is that kernel point. -/
lemma pairKernelPoint_kernelShear (W : Over T.left)
    (k : (Over.map T.hom).obj W ⟶ (GroupScheme.kernel (groupHom f)).X) :
    pairKernelPoint f ((relativeSpace A.X.hom).map (kernelCharacterParameter W))
        (kernelShear f (kernelCharacterParameter W) k)
        (kernelShear_homFamilySpaceMap f _ k).symm =
      (Over.map T.hom).map (pairParameterProj W) ≫ k := by
  let W' := (Over.map T.hom).obj W
  let ψ : (Over.map T.hom).obj
      (pairParameter ((relativeSpace A.X.hom).map (kernelCharacterParameter W))) ⟶
        relativeOver A W' :=
    Over.homMk (𝟙 _) (by
      simp only [Over.map_obj_hom, Over.mk_hom, Category.id_comp, ← Category.assoc,
        relativeSpace_map_fst]
      rfl)
  have hP : pairPoint ((relativeSpace A.X.hom).map (kernelCharacterParameter W))
      (kernelShear f (kernelCharacterParameter W) k)
      (pair_fst_eq f _ _ (kernelShear_homFamilySpaceMap f _ k).symm) =
        ψ ≫ ((relativeFst A W' ≫ k ≫ (GroupScheme.kernelι (groupHom f)).hom.hom) *
          relativeSnd A W') := by
    ext
    simp only [pairPoint, Over.homMk_left, Over.comp_left, ψ, Category.id_comp]
    exact shear_snd A _ _
  have hQ : pairPoint ((relativeSpace A.X.hom).map (kernelCharacterParameter W))
      ((relativeSpace A.X.hom).map (kernelCharacterParameter W)) rfl = ψ ≫ relativeSnd A W' := by
    ext
    simp only [pairPoint, Over.homMk_left, Over.comp_left, ψ, Category.id_comp]
    exact relativeSpace_map_snd A _
  have hF : ψ ≫ relativeFst A W' = (Over.map T.hom).map (pairParameterProj W) := by
    ext
    simp [ψ, pairParameterProj]
    rfl
  apply (cancel_mono (GroupScheme.kernelι (groupHom f)).hom.hom).mp
  rw [pairKernelPoint_ι, hP, hQ, MonObj.comp_mul, mul_inv_cancel_right, reassoc_of% hF,
    Category.assoc]

variable {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (h : UniversalGlobalFunctions A)

/-- A trivialization realizing the character values has that character. -/
lemma intrinsicKernelCharacterHom_eq_of_pairCharacterValue
    (hα : ∀ (U : Scheme.{u}) (a b : U ⟶ (relativeSpace A.X.hom).obj T)
      (hab : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T),
      structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T) a b hab α) =
        pairCharacterValue f χ U a b hab) :
    intrinsicKernelCharacterHom f α h = χ := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro W k
  apply (Gm.pointsEquiv T.left W).injective
  rw [intrinsicKernelCharacterHom_points]
  unfold kernelTranslationUnit kernelTranslationScalar kernelTranslationAut
  rw [hα]
  unfold pairCharacterValue
  rw [pairKernelPoint_kernelShear, characterValue_naturality]
  change relativeUnitDescend A h _ (relativeUnitsPullback A _ _) = _
  rw [relativeUnitDescend_pullback]
  unfold characterValue
  rw [MulEquiv.symm_apply_apply]

/-- Effective descent along the faithfully flat `f_T` gives surjectivity. -/
theorem trivialHomPullbackClassCharacter_surjective_of_effective
    (hE : UnitCocycleDescentEffectiveStatement.{u}) (hf : IsIsogeny f) (T : Over S) :
    Function.Surjective
      (trivialHomPullbackClassCharacter f (T := T) (universalGlobalFunctions A)) := by
  intro χ
  let χh := Cartier.characterHomEquiv (kernelCommGroupScheme f) T χ
  have := isFinite_homFamilySpaceMap hf T
  obtain ⟨L, α, hα⟩ := hE _ _ ((homFamilySpaceMap f).app T) inferInstance
    (flat_homFamilySpaceMap hf T) (surjective_homFamilySpaceMap hf T)
    (pairCharacterValue f χh)
    (fun _ _ q a b h h' ↦ pairCharacterValue_precomp f χh q a b h h')
    (fun _ a b d h h' h'' ↦ pairCharacterValue_trans f χh a b d h h' h'')
  refine ⟨trivialHomPullbackClassOf f L ⟨α⟩, ?_⟩
  rw [trivialHomPullbackClassCharacter_classOf, trivialHomPullbackCharacter_eq f _ L ⟨α⟩ α]
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).injective
  rw [characterHomEquiv_intrinsicKernelCharacter]
  exact intrinsicKernelCharacterHom_eq_of_pairCharacterValue f χh α _ hα

end Langlands.AbelianScheme
