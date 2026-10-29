import Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionStatement
import Langlands.AlgebraicGeometry.Picard.FiniteWeilBilinearity
import Langlands.AbelianScheme.KernelCharacterNaturality

/-! # Proof of divisibility compatibility of the actual finite Weil pairing -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

section Composition

variable {S : Scheme.{u}} {A B C : AbelianScheme S}

/-- Equal-composite automorphisms depend only on the two maps being compared. -/
lemma equalCompositeUnitAut_congr {U X Y : Scheme.{u}} (p : X ⟶ Y) {a a' b b' : U ⟶ X}
    (ha : a = a') (hb : b = b') (h : a ≫ p = b ≫ p) (h' : a' ≫ p = b' ≫ p)
    {M : Y.Modules} (α : (Scheme.Modules.pullback p).obj M ≅ structureModule X) :
    equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a' b' h' α := by
  subst ha hb
  rfl

/-- The homomorphism-family map of a composite is the composite of the family maps. -/
lemma homFamilySpaceMap_composite_square (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hfg : f ≫ g = h)
    (T : Over S) :
    (homFamilySpaceMap h).app T ≫ 𝟙 _ =
      (homFamilySpaceMap f).app T ≫ (homFamilySpaceMap g).app T := by
  subst hfg
  rw [Category.comp_id, homFamilySpaceMap_comp]

/-- Pulling back the global units of `T ×_S B` to `T ×_S A` commutes with descent to `T`. -/
lemma relativeUnitDescend_homFamilySpaceMap (f : A ⟶ B) (U : Over S)
    (c : Γ((relativeSpace B.X.hom).obj U, ⊤)ˣ) :
    relativeUnitDescend A (universalGlobalFunctions A) U
        (Units.map ((homFamilySpaceMap f).app U).appTop.hom.toMonoidHom c) =
      relativeUnitDescend B (universalGlobalFunctions B) U c := by
  apply relativeUnitsPullback_injective A (universalGlobalFunctions A) U
  rw [relativeUnitsPullback_descend]
  conv_lhs => rw [← relativeUnitsPullback_descend B (universalGlobalFunctions B) U c]
  apply Units.ext
  have he := congrArg Scheme.Hom.appTop (homFamilySpaceMap_fst f U)
  rw [Scheme.Hom.comp_appTop] at he
  exact congrArg (fun φ ↦ φ ((relativeUnitDescend B (universalGlobalFunctions B) U c :
    Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤))) he

/-- The section of a base-changed group scheme attached to a point is that point. -/
lemma baseChangePointsEquiv_sectionPointsEquiv_symm (G : CommGroupScheme S) (T : Over S)
    (x : T ⟶ G.X) :
    baseChangePointsEquiv T.hom G.toGrp (Over.mk (𝟙 T.left))
        ((Cartier.sectionPointsEquiv G T).symm x) =
      (Cartier.sectionBaseIso T).hom ≫ x := by
  rw [← Iso.inv_comp_eq]
  exact (Cartier.sectionPointsEquiv G T).apply_symm_apply x

variable (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (hfg : f ≫ g = h)

/-- A trivialization of the pullback along `g` induces one along a composite `h = f ≫ g`. -/
def compositeHomPullbackTrivialization {T : Over S}
    {M : ((relativeSpace C.X.hom).obj T).Modules}
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap g).app T)).obj M ≅
      structureModule ((relativeSpace B.X.hom).obj T)) :
    (Scheme.Modules.pullback ((homFamilySpaceMap h).app T)).obj
        ((Scheme.Modules.pullback (𝟙 _)).obj M) ≅
      structureModule ((relativeSpace A.X.hom).obj T) :=
  squarePullbackIso ((homFamilySpaceMap g).app T) ((homFamilySpaceMap h).app T)
      ((homFamilySpaceMap f).app T) (𝟙 _) (homFamilySpaceMap_composite_square f g h hfg T) M ≪≫
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).mapIso α ≪≫
      pullbackUnitIso ((homFamilySpaceMap f).app T)

variable {T : Over S} {M : ((relativeSpace C.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap g).app T)).obj M ≅
    structureModule ((relativeSpace B.X.hom).obj T))

/-- Translation by a point of `ker h` is the pullback of translation by its image in `ker g`. -/
lemma kernelTranslationAut_comp {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom h)).X)
    (k' : U ⟶ (GroupScheme.kernel (groupHom g)).X)
    (hk : k' ≫ (GroupScheme.kernelι (groupHom g)).hom.hom =
      k ≫ (GroupScheme.kernelι (groupHom h)).hom.hom ≫ (groupHom f).hom.hom) :
    kernelTranslationAut h (compositeHomPullbackTrivialization f g h hfg α) a k =
      structureAutPullback ((homFamilySpaceMap f).app U) (kernelTranslationAut g α a k') := by
  have h₁ : (relativeSpace A.X.hom).map a ≫ (homFamilySpaceMap f).app T =
      (homFamilySpaceMap f).app U ≫ (relativeSpace B.X.hom).map a :=
    (homFamilySpaceMap f).naturality a
  have h₂ : kernelShear h a k ≫ (homFamilySpaceMap f).app T =
      (homFamilySpaceMap f).app U ≫ kernelShear g a k' := by
    rw [kernelShear, shear_homFamilySpaceMap, kernelShear, hk, Category.assoc]
  have hab : ((relativeSpace A.X.hom).map a ≫ (homFamilySpaceMap f).app T) ≫
        (homFamilySpaceMap g).app T =
      (kernelShear h a k ≫ (homFamilySpaceMap f).app T) ≫ (homFamilySpaceMap g).app T := by
    rw [h₁, h₂, Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap]
  have hab' : ((homFamilySpaceMap f).app U ≫ (relativeSpace B.X.hom).map a) ≫
        (homFamilySpaceMap g).app T =
      ((homFamilySpaceMap f).app U ≫ kernelShear g a k') ≫ (homFamilySpaceMap g).app T := by
    rw [Category.assoc, Category.assoc, kernelShear_homFamilySpaceMap]
  unfold kernelTranslationAut compositeHomPullbackTrivialization
  rw [equalCompositeUnitAut_square _ _ _ _ _ α _ _ _ hab,
    equalCompositeUnitAut_congr _ h₁ h₂ hab hab',
    equalCompositeUnitAut_precomp ((homFamilySpaceMap g).app T)
      ((relativeSpace B.X.hom).map a) (kernelShear g a k') α ((homFamilySpaceMap f).app U)
      (kernelShear_homFamilySpaceMap g a k').symm hab']
  rfl

/-- The corresponding global scalars agree after pullback along the family map of `f`. -/
lemma kernelTranslationScalar_comp {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom h)).X)
    (k' : U ⟶ (GroupScheme.kernel (groupHom g)).X)
    (hk : k' ≫ (GroupScheme.kernelι (groupHom g)).hom.hom =
      k ≫ (GroupScheme.kernelι (groupHom h)).hom.hom ≫ (groupHom f).hom.hom) :
    kernelTranslationScalar h (compositeHomPullbackTrivialization f g h hfg α) a k =
      Units.map ((homFamilySpaceMap f).app U).appTop.hom.toMonoidHom
        (kernelTranslationScalar g α a k') := by
  rw [kernelTranslationScalar, kernelTranslationAut_comp f g h hfg α a k k' hk,
    structureAutScalar_pullback]
  rfl

/-- The descended units on the parameter scheme agree. -/
lemma kernelTranslationUnit_comp {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom h)).X)
    (k' : U ⟶ (GroupScheme.kernel (groupHom g)).X)
    (hk : k' ≫ (GroupScheme.kernelι (groupHom g)).hom.hom =
      k ≫ (GroupScheme.kernelι (groupHom h)).hom.hom ≫ (groupHom f).hom.hom) :
    kernelTranslationUnit h (compositeHomPullbackTrivialization f g h hfg α)
        (universalGlobalFunctions A) a k =
      kernelTranslationUnit g α (universalGlobalFunctions B) a k' := by
  rw [kernelTranslationUnit, kernelTranslationScalar_comp f g h hfg α a k k' hk,
    relativeUnitDescend_homFamilySpaceMap]
  rfl

/-- Evaluating the intrinsic character for `g` on the image of a point of `ker h` gives the
intrinsic character for `h = f ≫ g` at that point. -/
lemma intrinsicKernelCharacter_evaluation_comp
    (κ : (kernelCommGroupScheme h).X ⟶ (kernelCommGroupScheme g).X)
    (hκ : κ ≫ (GroupScheme.kernelι (groupHom g)).hom.hom =
      (GroupScheme.kernelι (groupHom h)).hom.hom ≫ (groupHom f).hom.hom)
    (x : T ⟶ (kernelCommGroupScheme h).X) :
    Cartier.characterEvaluation
        (intrinsicKernelCharacter g α (universalGlobalFunctions B)) (x ≫ κ) =
      Cartier.characterEvaluation
        (intrinsicKernelCharacter h (compositeHomPullbackTrivialization f g h hfg α)
          (universalGlobalFunctions A)) x := by
  apply (Gm.pointsEquiv S T).injective
  rw [← Cartier.characterEvaluation_section, ← Cartier.characterEvaluation_section,
    characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter,
    intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points,
    baseChangePointsEquiv_sectionPointsEquiv_symm,
    baseChangePointsEquiv_sectionPointsEquiv_symm]
  symm
  apply kernelTranslationUnit_comp f g h hfg α
  simp only [Category.assoc, hκ]

variable (hA : HasDualScheme A) (hB : HasDualScheme B) (hC : HasDualScheme C)
  (stability : PicardZeroPullbackStatement.{u})

include hfg in
/-- Composition compatibility of actual dual-kernel characters along `h = f ≫ g`. -/
lemma dualKernelCharacter_evaluation_comp
    (p p' : T ⟶ dualScheme C hC) (hpp : p = p')
    (hpg : p ≫ dualSchemeMap homPicardZeroPullback g hB hC =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB)
    (hph : p' ≫ dualSchemeMap homPicardZeroPullback h hA hC =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (κ : (kernelCommGroupScheme h).X ⟶ (kernelCommGroupScheme g).X)
    (hκ : κ ≫ (GroupScheme.kernelι (groupHom g)).hom.hom =
      (GroupScheme.kernelι (groupHom h)).hom.hom ≫ (groupHom f).hom.hom)
    (x : T ⟶ (kernelCommGroupScheme h).X) :
    Cartier.characterEvaluation (dualKernelCharacter hB stability g hC p hpg) (x ≫ κ) =
      Cartier.characterEvaluation (dualKernelCharacter hA stability h hC p' hph) x := by
  subst hpp
  rw [dualKernelCharacter_eq_intrinsic hB stability g hC p hpg
      (dualKernelPullbackModuleIso hB stability g hC p hpg),
    dualKernelCharacter_eq_of_iso hA stability h hC p hph
      ((Scheme.Modules.pullbackId _).app _).symm
      (compositeHomPullbackTrivialization f g h hfg
        (dualKernelPullbackModuleIso hB stability g hC p hpg))]
  exact intrinsicKernelCharacter_evaluation_comp f g h hfg _ κ hκ x

end Composition

section Transition

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "primal" n:arg => kernelCommGroupScheme (multiplication A (n : ℤ))
local notation "dualTorsion" n:arg => torsion (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)
local notation "ki" n:arg =>
  relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA (n : ℤ)
local notation "chi" => dualTorsionCharacter preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "value" => finiteWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "pairing" => finiteWeilPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

omit [QuasiSeparatedSpace S] in
/-- For `n ∣ m`, multiplication by `m / n` followed by multiplication by `n` is
multiplication by `m`. -/
lemma multiplication_div_comp (A : AbelianScheme S) {n m : ℕ} (h : n ∣ m) :
    multiplication A ((m / n : ℕ) : ℤ) ≫ multiplication A (n : ℤ) =
      multiplication A (m : ℤ) := by
  unfold multiplication
  rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul]
  congr 1
  exact_mod_cast Nat.div_mul_cancel h

omit [QuasiSeparatedSpace S] in
/-- Character evaluation turns natural multiples of a character into powers. -/
lemma characterEvaluation_nsmul {G : CommGroupScheme S} {T : Over S}
    (χ : (Cartier.characters G).obj (op T)) (x : T ⟶ G.X) (r : ℕ) :
    Cartier.characterEvaluation (r • χ) x = Cartier.characterEvaluation χ x ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [succ_nsmul, Cartier.characterEvaluation_add, ih, pow_succ]

/-- Powers of an actual dual-torsion point give multiples of its intrinsic character. -/
lemma dualTorsionCharacter_pow (n : ℕ) {T : Over S} (y : T ⟶ (dualTorsion n).X) (r : ℕ) :
    chi n (y ^ r) = r • chi n y :=
  map_nsmul (dualTorsionCharacterAddHom preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n T) r (Additive.ofMul y)

/-- The beta character of the transitioned dual point, evaluated on the transitioned primal
point, is the `m / n`-th power of the original evaluation. -/
lemma dualTorsionCharacter_transition {n m : ℕ} (h : n ∣ m) {T : Over S}
    (x : T ⟶ (primal m).X) (y : T ⟶ (dualTorsion m).X) :
    Cartier.characterEvaluation
        (chi n (y ≫ Tate.kernelTransition (Langlands.CommGroupScheme.toGrp GA) h))
        (x ≫ Tate.kernelTransition A.toGrp h) =
      Cartier.characterEvaluation (chi m y) x ^ (m / n) := by
  rw [← characterEvaluation_nsmul, ← dualTorsionCharacter_pow]
  have hι (k : ℕ) := congrArg (fun φ ↦ φ.hom.hom)
    (relativeDualMultiplicationKernelIso_inv_ι preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA (k : ℤ))
  simp only [Grp.comp_hom_hom] at hι
  have hκ : Tate.kernelTransition (Langlands.CommGroupScheme.toGrp GA) h ≫
        (torsionι (Langlands.CommGroupScheme.toGrp GA) (n : ℤ)).hom.hom =
      (torsionι (Langlands.CommGroupScheme.toGrp GA) (m : ℤ)).hom.hom ≫
        (GroupScheme.multiplication (Langlands.CommGroupScheme.toGrp GA)
          ((m / n : ℕ) : ℤ)).hom.hom :=
    Tate.kernelTransition_ι (Langlands.CommGroupScheme.toGrp GA) h
  unfold dualTorsionCharacter dualKernelPointCharacter
  refine dualKernelCharacter_evaluation_comp
    (multiplication A ((m / n : ℕ) : ℤ)) (multiplication A (n : ℤ)) (multiplication A (m : ℤ))
    (multiplication_div_comp A h) hA hA hA stability _ _ ?_ _ _ _ ?_ x
  · simp only [Category.assoc]
    rw [hι, hι, hκ, ← Category.assoc, GroupScheme.points_multiplication, zpow_natCast]
    exact (MonObj.pow_comp (N := (Langlands.CommGroupScheme.toGrp GA).X) y (m / n)
      (torsionι (Langlands.CommGroupScheme.toGrp GA) (m : ℤ)).hom.hom).symm
  · exact Tate.kernelTransition_ι A.toGrp h

/-- Pointwise form of the divisibility compatibility. -/
lemma finiteWeilValue_transition {n m : ℕ} (h : n ∣ m) {T : Over S}
    (x : T ⟶ (primal m).X) (y : T ⟶ (dualTorsion m).X) :
    value n (x ≫ Tate.kernelTransition A.toGrp h)
        (y ≫ Tate.kernelTransition (Langlands.CommGroupScheme.toGrp GA) h) =
      value m x y ≫ (Langlands.CommGroupScheme.groupHom (mu.transition S h)).hom.hom := by
  refine (finiteWeilValue_unique preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA n _ _ _ ?_).symm
  have ht := congrArg (fun φ ↦ (Langlands.CommGroupScheme.groupHom φ).hom.hom)
    (mu.transition_incl S h)
  simp only [Langlands.CommGroupScheme.groupHom] at ht
  change (Langlands.CommGroupScheme.groupHom (mu.transition S h)).hom.hom ≫
      (mu.incl S n).toMul.hom.hom =
    (mu.incl S m).toMul.hom.hom ≫
      (GroupScheme.multiplication (Gm S).toGrp ((m / n : ℕ) : ℤ)).hom.hom at ht
  rw [Category.assoc, ht, ← Category.assoc, finiteWeilValue_incl,
    GroupScheme.points_multiplication, zpow_natCast,
    dualTorsionCharacter_transition]

end Transition

/-- The actual finite Weil pairings commute with the actual divisibility transitions. -/
theorem relativeFiniteWeilTransition : RelativeFiniteWeilTransitionStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    S _ A hA MA evaluationA n m _ _ h
  dsimp only
  have key := finiteWeilValue_transition preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA h prod.fst prod.snd
  rw [← finiteWeilPairing_points, ← finiteWeilPairing_points, prod.lift_fst_snd,
    Category.id_comp] at key
  rw [← key, ← prod.lift_map, prod.lift_fst_snd, Category.id_comp]

end Langlands.AbelianScheme
