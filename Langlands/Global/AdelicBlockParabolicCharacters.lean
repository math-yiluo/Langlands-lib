import Langlands.Global.AdelicBlockEisensteinGeometry
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-! # Block determinant characters of the actual scheme block parabolic

The determinant of each diagonal block is a rational character of the block parabolic subgroup
scheme of `GL_N`; over a number field its normalized adelic norm is the determinant norm of the
corresponding block of the adelic matrix. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ} (B : BlockShape N) (R : CommRingCat.{u})

/-- Block upper triangular coordinates on every test scheme of the block parabolic. -/
def blockParabolicTestPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) ≃*
      B.parabolic Γ(T.left, ⊤) :=
  (Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy
    (isCutOutBy_blockParabolic (n := Fin N) (R := R) (blockShapeWeight B))) T).trans
    (MulEquiv.subgroupCongr (blockParabolicSubgroup_blockShapeWeight B Γ(T.left, ⊤)))

theorem blockParabolicTestPointsEquiv_val (T : Over (Spec R))
    (x : T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) :
    (blockParabolicTestPointsEquiv B R T x).val =
      pointsEquiv (Fin N) R T (x ≫ (blockParabolicHom (Fin N) R (blockShapeWeight B)).hom.hom) :=
  (pointsEquiv_cutHom _ x).symm

theorem blockParabolicTestPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) :
    (blockParabolicTestPointsEquiv B R T' (a ≫ x)).val =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (blockParabolicTestPointsEquiv B R T x).val := by
  rw [blockParabolicTestPointsEquiv_val, blockParabolicTestPointsEquiv_val, Category.assoc,
    pointsEquiv_naturality]

/-- The `i`-th diagonal block of a point of the block parabolic. -/
def parabolicBlockPoints (i : Fin B.length) (T : Over (Spec R)) :
    (T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) →*
      (T ⟶ (groupScheme (Fin (B.size i)) R).X) :=
  (pointsEquiv (Fin (B.size i)) R T).symm.toMonoidHom.comp
    ((Pi.evalMonoidHom (fun j => Langlands.GeneralLinear (B.size j) Γ(T.left, ⊤)) i).comp
      ((B.leviProjection Γ(T.left, ⊤)).comp (blockParabolicTestPointsEquiv B R T).toMonoidHom))

theorem parabolicBlockPoints_naturality (i : Fin B.length) {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) :
    parabolicBlockPoints B R i T' (a ≫ x) = a ≫ parabolicBlockPoints B R i T x := by
  apply (pointsEquiv (Fin (B.size i)) R T').injective
  rw [pointsEquiv_naturality]
  simp only [parabolicBlockPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, Pi.evalMonoidHom_apply]
  apply Units.ext
  ext b c
  rw [B.leviProjection_apply, blockParabolicTestPointsEquiv_naturality]
  rfl

/-- The scheme projection of the block parabolic to one invertible diagonal block. -/
def parabolicBlockHom (i : Fin B.length) :
    blockParabolicScheme (Fin N) R (blockShapeWeight B) ⟶ groupScheme (Fin (B.size i)) R :=
  homOfPoints (parabolicBlockPoints B R i) (parabolicBlockPoints_naturality B R i)

theorem pointsEquiv_parabolicBlockHom (i : Fin B.length) (T : Over (Spec R))
    (x : T ⟶ (blockParabolicScheme (Fin N) R (blockShapeWeight B)).X) :
    pointsEquiv (Fin (B.size i)) R T (x ≫ (parabolicBlockHom B R i).hom.hom) =
      B.leviProjection Γ(T.left, ⊤) (blockParabolicTestPointsEquiv B R T x) i := by
  rw [parabolicBlockHom, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

/-- The `i`-th block determinant, as a rational character of the block parabolic. -/
def parabolicBlockCharacter (i : Fin B.length) :
    rationalCharacters (blockParabolicScheme (Fin N) R (blockShapeWeight B)) :=
  characterRestrict (parabolicBlockHom B R i) (determinantCharacter (Fin (B.size i)) R)

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.Global.AdelicBlockEisensteinGeometry

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockDeterminantCharacter
open NumberField
open scoped NNReal

variable (F : Type u) [Field F] {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt

/-- On affine points, the block projection of the scheme parabolic is the diagonal block of the
corresponding block upper triangular matrix. -/
theorem affinePointsEquiv_parabolicBlockHom (i : Fin B.length) (S : CommAlgCat.{u} 𝕜)
    (x : (P).affinePoints S) :
    affinePointsEquiv (Fin (B.size i)) 𝕜 S (x ≫ (parabolicBlockHom B 𝕜 i).hom.hom) =
      B.leviProjection S (blockParabolicPointsEquiv F B S x) i := by
  have hinj : Function.Injective (Corepresented.affineSectionsIso S).inv.hom.toRingHom :=
    (Corepresented.affineSectionsAlgEquiv S).symm.injective
  apply Units.ext
  ext a c
  apply hinj
  have h1 := congrArg (fun g : GL (Fin (B.size i)) Γ(((algSpec 𝕜).obj (op S)).left, ⊤) =>
    g.1 a c)
    (pointsEquiv_eq_affinePointsEquiv (n := Fin (B.size i)) (R := 𝕜) S
      (x ≫ (parabolicBlockHom B 𝕜 i).hom.hom))
  have h2 := congrArg (fun g : GL (Fin n) Γ(((algSpec 𝕜).obj (op S)).left, ⊤) =>
    g.1 (B.index i a) (B.index i c))
    (pointsEquiv_eq_affinePointsEquiv (n := Fin n) (R := 𝕜) S (x ≫ (p).hom.hom))
  simp only at h1 h2
  rw [pointsEquiv_parabolicBlockHom, B.leviProjection_apply,
    blockParabolicTestPointsEquiv_val] at h1
  rw [B.leviProjection_apply, blockParabolicPointsEquiv_val]
  exact h1.symm.trans h2

omit [Field F] in
variable {F} in
private theorem characterUnits_determinantCharacter [Field F] (b : ℕ) (S : CommAlgCat.{u} 𝕜)
    (x : (groupScheme (Fin b) 𝕜).affinePoints S) :
    characterUnits F (groupScheme (Fin b) 𝕜) (determinantCharacter (Fin b) 𝕜).toMul S x =
      Matrix.GeneralLinearGroup.det (affinePointsEquiv (Fin b) 𝕜 S x) := by
  let e := affinePointsEquiv (Fin b) 𝕜 S
  have hx := characterOnAffineMatrices_apply (determinantCharacter (Fin b) 𝕜).toMul S (e x)
  rw [MulEquiv.symm_apply_apply] at hx
  have h : characterOnAffineMatrices (determinantCharacter (Fin b) 𝕜).toMul S (e x) =
      Matrix.GeneralLinearGroup.det (e x) :=
    characterOnAffineMatrices_determinantCharacter (n := Fin b) S (e x)
  exact hx.symm.trans h

variable [NumberField F]

theorem characterNorm_determinantCharacter (b : ℕ)
    (g : AdelicGroupPoints F (groupScheme (Fin b) 𝕜)) :
    characterNorm F (groupScheme (Fin b) 𝕜) (determinantCharacter (Fin b) 𝕜).toMul g =
      determinantNorm F b (adelicHomeomorph F b g) :=
  congrArg (IdeleAbsoluteValue.full F)
    (characterUnits_determinantCharacter b (CommAlgCat.of F (AdeleRing (𝓞 F) F)) g)

/-- The logarithmic functional of an adelic point of the block parabolic at the `i`-th block
determinant character is the logarithm of the normalized norm of the determinant of its
`i`-th diagonal block. -/
theorem characterLog_parabolicBlockCharacter (i : Fin B.length) (q : AdelicGroupPoints F P) :
    characterLog F P q (parabolicBlockCharacter B 𝕜 i) =
      Real.log ((blockDeterminantNorm F B i (B.leviProjection (AdeleRing (𝓞 F) F)
        (blockParabolicPointsEquiv F B (CommAlgCat.of F (AdeleRing (𝓞 F) F)) q)) : ℝ≥0) : ℝ) := by
  have h := congrArg (fun ℓ : RealCharacterDual F (groupScheme (Fin (B.size i)) 𝕜) =>
      ℓ (determinantCharacter (Fin (B.size i)) 𝕜))
    (characterLog_map F _ _ (parabolicBlockHom B 𝕜 i) q)
  change _ = characterLog F P q (characterRestrict (parabolicBlockHom B 𝕜 i) _) at h
  rw [parabolicBlockCharacter, ← h, characterLog_apply, characterNorm_determinantCharacter]
  exact congrArg (fun g => Real.log ((determinantNorm F (B.size i) g : ℝ≥0) : ℝ))
    (affinePointsEquiv_parabolicBlockHom F B i _ q)

end Langlands.Global.AdelicBlockEisensteinGeometry
