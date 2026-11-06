import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Plancherel.ParabolicPointIntertwiningRegion
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# All-proper-rational-parabolic cuspidality on the actual inducing Levi

The character-one Jacquet quotient vanishes along the geometric radical of every
proper rational parabolic. The literal Levi action is pulled back along its
canonical rational-point homeomorphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

/-- The Jacquet-vanishing condition for every proper rational parabolic of the
actual group scheme, using its represented geometric unipotent radical. -/
def ProperRationalJacquetVanishing
    (σ : Representation ℂ (rationalPoints H) E) : Prop :=
  ∀ (Q U : GroupScheme (Spec (CommRingCat.of F))) (q : Q ⟶ H) (n : U ⟶ Q),
    IsParabolicSubgroup q →
    SubgroupFunctor.range q ≠ ⊤ →
    LeviSubgroup.IsGeometricUnipotentRadical n →
    Subsingleton (Jacquet.Localization.Coinvariants σ
      ((SubgroupFunctor.range (n ≫ q)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) 1)

namespace RationalNormalized

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance cuspidalityAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance cuspidalityAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance cuspidalityLeviPointTopology : TopologicalSpace (rationalPoints M) :=
  rationalPointTopology F M.X

/-- The actual representation of the Levi scheme's rational points obtained
from the representation of its literal subgroup in the ambient point group. -/
abbrev leviSchemeRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    Representation ℂ (rationalPoints M) E :=
  σ.comp (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom

/-- Renard VI.2.1 supercuspidality for the literal inducing Levi: smoothness and
vanishing of all actual proper-rational-parabolic Jacquet quotients. -/
def IsSupercuspidal
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  IsSmooth σ ∧ ProperRationalJacquetVanishing (leviSchemeRepresentation r σ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Smoothness is preserved by the canonical actual-Levi pullback. -/
theorem isSmooth_leviSchemeRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) (hσ : IsSmooth σ) :
    IsSmooth (leviSchemeRepresentation r σ) :=
  isSmooth_comp (parabolicLeviPointHomeomorph r).toMulEquiv.toMonoidHom
    (parabolicLeviPointHomeomorph r).continuous hσ

end RationalNormalized

end Langlands.Plancherel
