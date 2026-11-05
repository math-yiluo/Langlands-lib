import Langlands.Global.FinitePlaceIwasawaTransport
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.BruhatTits.Iwasawa.PointProducts

/-! # Extracting the finite-place Iwasawa input from local compact and product data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.BruhatTits.SpecialCompact

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [TopologicalSpace F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Compact maximality and the source-left product give the exact consumer
predicate on the original rational-point topology. -/
theorem IsCompactOpenMaximal.isLocalIwasawaCompact
    {K : Subgroup (rationalPoints G)} (hK : IsCompactOpenMaximal F K)
    {P : GroupScheme (Spec (CommRingCat.of F))} (j : P ⟶ G)
    (hprod : Iwasawa.PointProductEqualities (rationalPoints.map j).range K) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    Global.CoordinateCompactPatching.IsLocalIwasawaCompact (rationalPoints.map j) K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  refine ⟨⟨hK.1, ?_⟩, ?_⟩
  · intro L hL hKL
    exact (hK.2.2.eq_of_le hL hKL).symm
  · exact hprod.1.symm

end Langlands.BruhatTits.SpecialCompact

namespace Langlands.Global.FinitePlaceGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- Connected reductivity holds on the actual finite-completion pullback,
by the unconditional field-extension theorem. -/
theorem baseChanged_isConnectedReductive (hG : IsConnectedReductive G)
    (v : FinitePlace F) :
    IsConnectedReductive (baseChangedGroup F G v) :=
  connectedReductiveFieldExtensionStatement F (FiniteCompletion F v) G hG

/-- Every actual parabolic inclusion remains parabolic on the actual
finite-completion pullback, including the improper parabolic. -/
theorem baseChange_isParabolicSubgroup (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) (v : FinitePlace F) :
    IsParabolicSubgroup
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).map p) :=
  parabolicFieldExtensionStatement F (FiniteCompletion F v) G hG P p hp

/-- Extract the finite-place consumer data from one supplied compact subgroup
with compact maximality and products for every actual algebraic parabolic.
This is a function of supplied subgroup data, not an existence assertion. -/
def baseChangeIwasawaCompactOfParabolicProducts (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G)
    (hp : IsParabolicSubgroup p) (v : FinitePlace F) :
    haveI : IsAffineHom (baseChangedGroup F G v).X.hom :=
      (baseChanged_isConnectedReductive F G hG v).isAffineHom
    {K : Subgroup (rationalPoints (baseChangedGroup F G v)) //
      SpecialCompact.IsCompactOpenMaximal (FiniteCompletion F v) K ∧
        Iwasawa.AlgebraicParabolicProducts K} →
    {K : Subgroup (FinitePlaceGroupPoints F G v) //
      CoordinateCompactPatching.IsLocalIwasawaCompact
        (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v))) K} := by
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : IsAffineHom (baseChangedGroup F G v).X.hom :=
    (baseChanged_isConnectedReductive F G hG v).isAffineHom
  letI : IsAffine (baseChangedGroup F G v).X.left :=
    isAffine_of_isAffineHom (baseChangedGroup F G v).X.hom
  letI : TopologicalSpace (rationalPoints (baseChangedGroup F G v)) :=
    rationalPointTopology (FiniteCompletion F v) (baseChangedGroup F G v).X
  intro K
  let p' := (GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v))).map p
  have hp' : IsParabolicSubgroup p' := baseChange_isParabolicSubgroup F G hG p hp v
  exact baseChangeIwasawaCompact F G p v
    ⟨K.1, K.2.1.isLocalIwasawaCompact p'
      (K.2.2 (baseChangedGroup F P v) p' hp')⟩

end Langlands.Global.FinitePlaceGroupPoints
