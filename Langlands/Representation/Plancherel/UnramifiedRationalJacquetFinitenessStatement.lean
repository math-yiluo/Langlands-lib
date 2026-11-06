import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Langlands.Representation.Plancherel.RationalParabolicCuspidality
import Langlands.Representation.Aubert.General.DynamicInductionExactness
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof
import Mathlib.RepresentationTheory.Irreducible

/-! Native-coefficient Jacquet finiteness for the full universal induced family. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance jacquetFinitenessAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance jacquetFinitenessPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance jacquetFinitenessFieldT2 : T2Space F := BruhatTits.localField_t2Space F

/-- The literal centralizer point subgroup of the output cocharacter. -/
abbrev outputLeviPoints (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Subgroup (rationalPoints G) :=
  (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

/-- The actual normalized Jacquet action of the full universal induction along
an arbitrary output cocharacter; the inducing and output parabolics may differ. -/
abbrev outputJacquetRepresentation
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :=
  UnramifiedNormalized.jacquetRepresentation (parabolicLeviRationalNormCharacters r)
    (inducedRepresentation r h hU σ)
    (BruhatTits.DynamicUnipotentContainment.unipotentPoints χ) (outputLeviPoints χ)
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
    (Aubert.General.dynamic_isSemidirectDecomposition χ
      (Over.mk (𝟙 (Spec (CommRingCat.of F))))).levi_le_normalizer

/-- Native fixed-module finiteness for every output dynamic parabolic and every
compact open subgroup of its literal Levi. This is a conclusion predicate. -/
def UniversalInducedJacquetFiniteness
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  ∀ (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (J : OpenSubgroup (outputLeviPoints χ)),
    IsCompact (J : Set (outputLeviPoints χ)) →
      Module.Finite (RegularAlgebra r)
        (fixedVectors (outputJacquetRepresentation r h hU σ χ) J.toSubgroup)

end Langlands.Plancherel.RationalNormalized

namespace Langlands.Plancherel

universe u uV

/-- Renard VI.9.2: every compact-open fixed module of every output normalized
Jacquet action of the actual universal induced supercuspidal family is finite
over its complete rational-norm algebra. This declaration states the input to
the uniform-compression argument; it does not prove coefficient admissibility. -/
def RationalSupercuspidalJacquetFamilyFiniteStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI := hG.smooth
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : T2Space F := BruhatTits.localField_t2Space F
    letI : T2Space (rationalPoints G) := rationalPoint_t2Space F G
    letI : LocallyCompactSpace (rationalPoints G) := rationalPoint_locallyCompactSpace F G
    letI : NonarchimedeanGroup (rationalPoints G) :=
      Aubert.General.RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a),
      haveI := r.isCompatible.levi.isConnectedReductive.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      ∀ (n : U ⟶ P) (_hRad : LeviSubgroup.IsGeometricUnipotentRadical n)
        (h : Aubert.General.IsSemidirectDecomposition (RationalNormalized.ParabolicPoints p)
          (parabolicLeviPointSubgroup p l) (RationalNormalized.UnipotentPoints (p := p) n))
        (hU : IsClosed (RationalNormalized.UnipotentPoints (p := p) n :
          Set (rationalPoints G)))
        (_hr : Continuous h.projection)
        (_hCompact : CompactSpace (Induction.LeftQuotient (RationalNormalized.ParabolicPoints p)))
        (E : Type uV) [AddCommGroup E] [Module ℂ E]
        (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E),
        IsSmooth σ → IsAdmissible σ → Representation.IsIrreducible σ →
          RationalNormalized.IsSupercuspidal r σ →
            RationalNormalized.UniversalInducedJacquetFiniteness r h hU σ

end Langlands.Plancherel
