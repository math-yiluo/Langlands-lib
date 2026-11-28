import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.Global.AdelicGaloisTwistMap
import Langlands.Global.NumberFieldAdeleTensorComparison

/-!
# Localization of the adelic comparison for `Res_{L/K} GL_n`

See `GeneralLinearWeilAdelicLocalizationStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.TraceFormula.AdelicGroupAutomorphism

local instance generalLinearWeilLocalizationIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance generalLinearWeilLocalizationSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The Weil restriction `Res_{L/K} GL_n`, for the bound variables `K`, `L` and `n`. -/
local notation "Wₙ" => weilGroup K L GLₙ

set_option maxRecDepth 4000 in
/-- For every adelic point `g` of `W = Res_{L/K} GL_n` and every place `i` of `K`, the adelic
comparison `Φ` from `GeneralLinearWeilAdelicTwistStatement` agrees at `i` with `localPointsEquiv`.
Applying the ring map `r : 𝔸_L → K_i ⊗_K L` to the entries of `Φ g` gives the same invertible
matrix as applying `localPointsEquiv K L n i` to `atPlace K Wₙ i g`. The map `r` inverts the
adelic tensor isomorphism, projects the adelic factor to `K_i`, and exchanges the factors. -/
def GeneralLinearWeilAdelicLocalizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (g : AdelicGroupPoints K Wₙ)
    (i : Place K),
    let r : Adeles L →+* LocalBaseChangeAlgebra K L i :=
      (localSwap K L i).toRingHom.comp
        ((Algebra.TensorProduct.lTensor (S := L) L (adeleProjection K i)).toRingHom.comp
          (numberFieldAdeleTensorEquiv K L).symm.toRingHom)
    Matrix.GeneralLinearGroup.map r
        (GeneralLinearGroupPoints.adelicHomeomorph L n
          (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
            (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
            (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
            (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))) =
      localPointsEquiv K L n i (atPlace K Wₙ i g)

end Langlands.TraceFormula
