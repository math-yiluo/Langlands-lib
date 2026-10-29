import Langlands.AlgebraicGeometry.Picard.FiniteWeilFunctorialityStatement
import Langlands.AbelianScheme.KernelCharacterNaturality
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHomBilinearity

/-! # Dual-homomorphism functoriality of the actual finite Weil pairing -/

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

section Square

variable {S : Scheme.{u}} {A A₂ B B₂ : AbelianScheme S}
  (g : A ⟶ A₂) (h : B ⟶ B₂) (f : A ⟶ B) (f₂ : A₂ ⟶ B₂) (w : g ≫ f₂ = f ≫ h)

include w in
/-- The commutative square of actual family maps over every test scheme. -/
lemma homFamilySpaceMap_square (T : Over S) :
    (homFamilySpaceMap g).app T ≫ (homFamilySpaceMap f₂).app T =
      (homFamilySpaceMap f).app T ≫ (homFamilySpaceMap h).app T := by
  rw [← homFamilySpaceMap_comp, ← homFamilySpaceMap_comp, w]

/-- Base units pulled back to `B_U` and then along `f_U` are base units pulled back to `A_U`. -/
lemma relativeUnitsPullback_homFamilySpaceMap (U : Over S) (c : Γ(U.left, ⊤)ˣ) :
    Units.map ((homFamilySpaceMap f).app U).appTop.hom.toMonoidHom
        (relativeUnitsPullback B U c) =
      relativeUnitsPullback A U c := by
  have he := congrArg Scheme.Hom.appTop (homFamilySpaceMap_fst f U)
  rw [Scheme.Hom.comp_appTop] at he
  apply Units.ext
  exact congrArg (fun m ↦ m (c : Γ(U.left, ⊤))) he

variable {T : Over S} {N : ((relativeSpace B₂.X.hom).obj T).Modules}
  (β : (Scheme.Modules.pullback ((homFamilySpaceMap h).app T)).obj N ≅
    structureModule ((relativeSpace B.X.hom).obj T))

/-- Transport a trivialization of `h^* N` to one of `g^* f₂^* N` around the square. -/
def squareKernelTrivialization :
    (Scheme.Modules.pullback ((homFamilySpaceMap g).app T)).obj
        ((Scheme.Modules.pullback ((homFamilySpaceMap f₂).app T)).obj N) ≅
      structureModule ((relativeSpace A.X.hom).obj T) :=
  squarePullbackIso ((homFamilySpaceMap h).app T) ((homFamilySpaceMap g).app T)
      ((homFamilySpaceMap f).app T) ((homFamilySpaceMap f₂).app T)
      (homFamilySpaceMap_square g h f f₂ w T) N ≪≫
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).mapIso β ≪≫
      pullbackUnitIso ((homFamilySpaceMap f).app T)

variable (φ : (GroupScheme.kernel (groupHom g)).X ⟶ (GroupScheme.kernel (groupHom h)).X)
  (hφ : φ ≫ (GroupScheme.kernelι (groupHom h)).hom.hom =
    (GroupScheme.kernelι (groupHom g)).hom.hom ≫ (groupHom f).hom.hom)

include hφ in
/-- Kernel translation on the source pushes forward to kernel translation on the target. -/
lemma kernelShear_square {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom g)).X) :
    kernelShear g a k ≫ (homFamilySpaceMap f).app T =
      (homFamilySpaceMap f).app U ≫ kernelShear h a (k ≫ φ) := by
  rw [kernelShear, shear_homFamilySpaceMap, kernelShear, Category.assoc k φ, hφ,
    Category.assoc]

include hφ in
/-- The transported kernel action is the pullback of the target kernel action. -/
lemma kernelTranslationAut_square {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom g)).X) :
    kernelTranslationAut g (squareKernelTrivialization g h f f₂ w β) a k =
      structureAutPullback ((homFamilySpaceMap f).app U)
        (kernelTranslationAut h β a (k ≫ φ)) := by
  have ha : (relativeSpace A.X.hom).map a ≫ (homFamilySpaceMap f).app T =
      (homFamilySpaceMap f).app U ≫ (relativeSpace B.X.hom).map a :=
    (homFamilySpaceMap f).naturality a
  have hk := kernelShear_square g h f φ hφ a k
  have hab : ((relativeSpace A.X.hom).map a ≫ (homFamilySpaceMap f).app T) ≫
        (homFamilySpaceMap h).app T =
      (kernelShear g a k ≫ (homFamilySpaceMap f).app T) ≫ (homFamilySpaceMap h).app T := by
    rw [ha, hk, Category.assoc, Category.assoc,
      kernelShear_homFamilySpaceMap h a (k ≫ φ)]
  have hsq := equalCompositeUnitAut_square ((homFamilySpaceMap h).app T)
    ((homFamilySpaceMap g).app T) ((homFamilySpaceMap f).app T)
    ((homFamilySpaceMap f₂).app T) (homFamilySpaceMap_square g h f f₂ w T) β
    ((relativeSpace A.X.hom).map a) (kernelShear g a k)
    (kernelShear_homFamilySpaceMap g a k).symm hab
  have hpre := equalCompositeUnitAut_precomp ((homFamilySpaceMap h).app T)
    ((relativeSpace B.X.hom).map a) (kernelShear h a (k ≫ φ)) β
    ((homFamilySpaceMap f).app U) (kernelShear_homFamilySpaceMap h a (k ≫ φ)).symm
    (by rw [← ha, ← hk]; exact hab)
  unfold kernelTranslationAut structureAutPullback squareKernelTrivialization
  rw [hsq]
  rw [← hpre]
  congr 1

include hφ in
/-- The transported action scalar is the pullback of the target action scalar. -/
lemma kernelTranslationScalar_square {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom g)).X) :
    kernelTranslationScalar g (squareKernelTrivialization g h f f₂ w β) a k =
      Units.map ((homFamilySpaceMap f).app U).appTop.hom.toMonoidHom
        (kernelTranslationScalar h β a (k ≫ φ)) := by
  rw [kernelTranslationScalar, kernelTranslationAut_square g h f f₂ w β φ hφ,
    structureAutScalar_pullback, kernelTranslationScalar]

include hφ in
/-- The descended source unit is the descended target unit at the image point. -/
lemma kernelTranslationUnit_square (hA : UniversalGlobalFunctions A)
    (hB : UniversalGlobalFunctions B) {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom g)).X) :
    kernelTranslationUnit g (squareKernelTrivialization g h f f₂ w β) hA a k =
      kernelTranslationUnit h β hB a (k ≫ φ) := by
  apply relativeUnitsPullback_injective A hA U
  rw [relativeUnitsPullback_kernelTranslationUnit,
    kernelTranslationScalar_square g h f f₂ w β φ hφ,
    ← relativeUnitsPullback_kernelTranslationUnit h β hB,
    relativeUnitsPullback_homFamilySpaceMap]

variable (Φ : kernelCommGroupScheme g ⟶ kernelCommGroupScheme h)
  (hΦ : Φ.toMul.hom.hom ≫ (GroupScheme.kernelι (groupHom h)).hom.hom =
    (GroupScheme.kernelι (groupHom g)).hom.hom ≫ (groupHom f).hom.hom)

include hΦ in
/-- The source character homomorphism is the target one precomposed with the kernel map. -/
lemma intrinsicKernelCharacterHom_square (hA : UniversalGlobalFunctions A)
    (hB : UniversalGlobalFunctions B) :
    intrinsicKernelCharacterHom g (squareKernelTrivialization g h f f₂ w β) hA =
      (CommGroupScheme.baseChange T.hom).map Φ ≫ intrinsicKernelCharacterHom h β hB := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro V k
  apply (Gm.pointsEquiv T.left V).injective
  change _ = Gm.pointsEquiv T.left V
    ((k ≫ ((CommGroupScheme.baseChange T.hom).map Φ).toMul.hom.hom) ≫
      (intrinsicKernelCharacterHom h β hB).toMul.hom.hom)
  rw [intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points]
  change _ = kernelTranslationUnit h β hB (kernelCharacterParameter V)
    (baseChangePointsEquiv T.hom (kernelCommGroupScheme h).toGrp V
      (k ≫ ((GroupScheme.baseChange T.hom).map Φ.toMul).hom.hom))
  rw [baseChangePointsEquiv_comp]
  exact kernelTranslationUnit_square g h f f₂ w β Φ.toMul.hom.hom hΦ hA hB _ _

include hΦ in
/-- The source intrinsic character is the image of the target one under the kernel map. -/
lemma intrinsicKernelCharacter_square (hA : UniversalGlobalFunctions A)
    (hB : UniversalGlobalFunctions B) :
    intrinsicKernelCharacter g (squareKernelTrivialization g h f f₂ w β) hA =
      (Cartier.charactersMap Φ).app (op T) (intrinsicKernelCharacter h β hB) := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme g) T).injective
  rw [characterHomEquiv_intrinsicKernelCharacter, Cartier.characterHomEquiv_precompose,
    characterHomEquiv_intrinsicKernelCharacter]
  exact intrinsicKernelCharacterHom_square g h f f₂ w β Φ hΦ hA hB

end Square

section Dual

variable {S : Scheme.{u}} {A A₂ B B₂ : AbelianScheme S}
  (stability : PicardZeroPullbackStatement.{u})
  (hA : HasDualScheme A) (hA₂ : HasDualScheme A₂) (hB : HasDualScheme B)
  (hB₂ : HasDualScheme B₂)

/-- The dual-kernel character depends only on the dual point, not on the proof that it lies
in the kernel. -/
lemma dualKernelCharacter_congr (g : A ⟶ A₂) {T : Over S} {p q : T ⟶ dualScheme A₂ hA₂}
    (e : p = q)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback g hA hA₂ =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    dualKernelCharacter hA stability g hA₂ p hp =
      dualKernelCharacter hA stability g hA₂ q (e ▸ hp) := by
  subst e
  rfl

include stability in
/-- The Poincaré representative of a dual-map image is the homomorphism pullback of the
representative of the original point. -/
lemma dualPointFamily_dualSchemeMap_nonempty (f₂ : A₂ ⟶ B₂) {T : Over S}
    (p : T ⟶ dualScheme B₂ hB₂) :
    Nonempty (dualPointFamily A₂ hA₂ (p ≫ dualSchemeMap homPicardZeroPullback f₂ hA₂ hB₂) ≅
      (homFamilyPullback f₂ T).obj (dualPointFamily B₂ hB₂ p)) := by
  have hc := congrArg Subtype.val (dualPointClass_dualSchemeMap
    (homPreservation := homPicardZeroPullback) stability f₂ hA₂ hB₂ p)
  change RigidifiedLineBundle.classOf A₂.X.hom (unitSection A₂) (unitSection_comp A₂)
      (dualPointFamily A₂ hA₂ (p ≫ dualSchemeMap homPicardZeroPullback f₂ hA₂ hB₂)) =
    RigidifiedLineBundle.classOf A₂.X.hom (unitSection A₂) (unitSection_comp A₂)
      ((homFamilyPullback f₂ T).obj (dualPointFamily B₂ hB₂ p)) at hc
  exact Quotient.exact hc

variable (g : A ⟶ A₂) (h : B ⟶ B₂) (f : A ⟶ B) (f₂ : A₂ ⟶ B₂) (w : g ≫ f₂ = f ≫ h)
  (Φ : kernelCommGroupScheme g ⟶ kernelCommGroupScheme h)
  (hΦ : Φ.toMul.hom.hom ≫ (GroupScheme.kernelι (groupHom h)).hom.hom =
    (GroupScheme.kernelι (groupHom g)).hom.hom ≫ (groupHom f).hom.hom)

include w hΦ in
/-- The source dual-kernel character at a dual-map image is the image of the target
dual-kernel character under the kernel map. -/
lemma dualKernelCharacter_square {T : Over S} (p : T ⟶ dualScheme B₂ hB₂)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback h hB hB₂ =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin B hB)
    (hp' : (p ≫ dualSchemeMap homPicardZeroPullback f₂ hA₂ hB₂) ≫
        dualSchemeMap homPicardZeroPullback g hA hA₂ =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA) :
    dualKernelCharacter hA stability g hA₂
        (p ≫ dualSchemeMap homPicardZeroPullback f₂ hA₂ hB₂) hp' =
      (Cartier.charactersMap Φ).app (op T) (dualKernelCharacter hB stability h hB₂ p hp) := by
  obtain ⟨e⟩ := dualPointFamily_dualSchemeMap_nonempty stability hA₂ hB₂ f₂ p
  rw [dualKernelCharacter_eq_of_iso hA stability g hA₂ _ hp'
      ((RigidifiedLineBundle.forget _ ⋙ LineBundle.forget _).mapIso e)
      (squareKernelTrivialization g h f f₂ w
        (dualKernelPullbackModuleIso hB stability h hB₂ p hp)),
    dualKernelCharacter_eq_intrinsic hB stability h hB₂ p hp
      (dualKernelPullbackModuleIso hB stability h hB₂ p hp)]
  exact intrinsicKernelCharacter_square g h f f₂ w _ Φ hΦ _ _

end Dual

section Application

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (f : A ⟶ B)

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GB" => dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB
  stability composition unitCoherence associativity comparison symmetry
local notation "df" => dualCommGroupSchemeMapFromEvaluation preservation composition
  unitCoherence associativity comparison symmetry stability hA hB MA evaluationA MB
  evaluationB f

omit [QuasiSeparatedSpace S] in
/-- Integer multiplication commutes with every homomorphism of abelian schemes. -/
lemma multiplication_comp_hom (n : ℤ) :
    multiplication A n ≫ f = f ≫ multiplication B n :=
  Additive.toMul.injective (GroupScheme.multiplication_naturality (groupHom f) n)

/-- The actual map of `n`-torsion kernels induced by `f`, as a commutative group-scheme map. -/
def multiplicationKernelMap (n : ℕ) :
    kernelCommGroupScheme (multiplication A (n : ℤ)) ⟶
      kernelCommGroupScheme (multiplication B (n : ℤ)) :=
  Additive.ofMul (homOfPoints
    (fun T ↦
      { toFun := fun x ↦ x ≫ Tate.kernelLevelMap (groupHom f) n
        map_one' := Tate.kernelLevelMap_comp_one (groupHom f) n T
        map_mul' := fun x y ↦ Tate.kernelLevelMap_comp_mul (groupHom f) n x y })
    (fun a x ↦ Category.assoc a x _))

omit [QuasiSeparatedSpace S] in
/-- On points, the kernel map is the published torsion-kernel map. -/
lemma comp_multiplicationKernelMap (n : ℕ) {T : Over S}
    (x : T ⟶ (kernelCommGroupScheme (multiplication A (n : ℤ))).X) :
    x ≫ (multiplicationKernelMap f n).toMul.hom.hom =
      x ≫ Tate.kernelLevelMap (groupHom f) n :=
  comp_homOfPoints _ (fun a x ↦ Category.assoc a x _) T x

omit [QuasiSeparatedSpace S] in
/-- The kernel map is compatible with the kernel inclusions and `f`. -/
lemma multiplicationKernelMap_ι (n : ℕ) :
    (multiplicationKernelMap f n).toMul.hom.hom ≫
        (GroupScheme.kernelι (groupHom (multiplication B (n : ℤ)))).hom.hom =
      (GroupScheme.kernelι (groupHom (multiplication A (n : ℤ)))).hom.hom ≫
        (groupHom f).hom.hom := by
  have h := comp_multiplicationKernelMap f n (𝟙 _)
  rw [Category.id_comp, Category.id_comp] at h
  rw [h]
  exact Tate.kernelLevelMap_ι (groupHom f) n

/-- The dual-torsion point `fᵛ(y)` has the image of the dual-torsion character of `y` under
the kernel map as its character. -/
lemma dualTorsionCharacter_dualMap (n : ℕ) {T : Over S}
    (y : T ⟶ (GroupScheme.torsion (GB).toGrp (n : ℤ)).X) :
    dualTorsionCharacter preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n
        (y ≫ Tate.kernelLevelMap (Langlands.CommGroupScheme.groupHom df) n) =
      (Cartier.charactersMap (multiplicationKernelMap f n)).app (op T)
        (dualTorsionCharacter preservation composition unitCoherence associativity comparison
          symmetry stability hB MB evaluationB n y) := by
  have hiA := congrArg (fun φ ↦ φ.hom.hom)
    (relativeDualMultiplicationKernelIso_inv_ι preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA (n : ℤ))
  have hiB := congrArg (fun φ ↦ φ.hom.hom)
    (relativeDualMultiplicationKernelIso_inv_ι preservation composition unitCoherence
      associativity comparison symmetry stability hB MB evaluationB (n : ℤ))
  dsimp only at hiA hiB
  have hk := Tate.kernelLevelMap_ι (Langlands.CommGroupScheme.groupHom df) n
  unfold dualTorsionCharacter dualKernelPointCharacter
  refine (dualKernelCharacter_congr stability hA hA _ ?_ _).trans
    (dualKernelCharacter_square stability hA hA hB hB (multiplication A (n : ℤ))
      (multiplication B (n : ℤ)) f f (multiplication_comp_hom f (n : ℤ))
      (multiplicationKernelMap f n) (multiplicationKernelMap_ι f n) _ _ _)
  rw [Grp.comp_hom_hom] at hiA hiB
  simp only [Category.assoc]
  rw [hiA, reassoc_of% hiB]
  change y ≫ Tate.kernelLevelMap (Langlands.CommGroupScheme.groupHom df) n ≫
      (GroupScheme.kernelι (GroupScheme.multiplication (GA).toGrp (n : ℤ))).hom.hom =
    y ≫ (GroupScheme.kernelι (GroupScheme.multiplication (GB).toGrp (n : ℤ))).hom.hom ≫
      (Langlands.CommGroupScheme.groupHom df).hom.hom
  rw [hk]

/-- The pairing of `B` after the primal torsion map of `f` is the pairing of `A` after the
dual torsion map of `fᵛ`. -/
lemma finiteWeilPairing_dualMap (n : ℕ) :
    prod.map (Tate.kernelLevelMap (groupHom f) n) (𝟙 _) ≫
        finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hB MB evaluationB n =
      prod.map (𝟙 _) (Tate.kernelLevelMap (Langlands.CommGroupScheme.groupHom df) n) ≫
        finiteWeilPairing preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA n := by
  have key : ∀ (T : Over S)
      (x : T ⟶ (kernelCommGroupScheme (multiplication A (n : ℤ))).X)
      (y : T ⟶ (GroupScheme.torsion (GB).toGrp (n : ℤ)).X),
      prod.lift x y ≫ prod.map (Tate.kernelLevelMap (groupHom f) n) (𝟙 _) ≫
          finiteWeilPairing preservation composition unitCoherence associativity comparison
            symmetry stability hB MB evaluationB n =
        prod.lift x y ≫ prod.map (𝟙 _)
            (Tate.kernelLevelMap (Langlands.CommGroupScheme.groupHom df) n) ≫
          finiteWeilPairing preservation composition unitCoherence associativity comparison
            symmetry stability hA MA evaluationA n := by
    intro T x y
    simp only [prod.lift_map_assoc, Category.comp_id]
    rw [finiteWeilPairing_points, finiteWeilPairing_points]
    unfold finiteWeilValue
    rw [dualTorsionCharacter_dualMap, Cartier.muEvaluation_precompose,
      comp_multiplicationKernelMap]
  simpa only [prod.lift_fst_snd, Category.id_comp] using key _ prod.fst prod.snd

/-- Dual-homomorphism functoriality of the actual finite Weil pairing. -/
theorem relativeFiniteWeilFunctoriality : RelativeFiniteWeilFunctorialityStatement.{u} := by
  intro preservation composition unitCoherence associativity comparison symmetry stability
    S _ A B hA hB MA evaluationA MB evaluationB f n _
  exact finiteWeilPairing_dualMap preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f n

end Application

end Langlands.AbelianScheme
