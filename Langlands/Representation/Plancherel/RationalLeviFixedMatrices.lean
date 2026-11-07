import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedSpecialization
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Plancherel.ParabolicRadicalUnimodularity
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof
import Langlands.Representation.Smooth.IrreducibleRealization

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Compact

universe uG uV uW un

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {τ : Representation ℂ H W}
  (mHaar : Measure H) [mHaar.IsHaarMeasure] (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
  (K : OpenSubgroup H) (hK : IsCompact (K : Set H))
  (E : ρ.Equiv τ) {idx : Type un} [Fintype idx]
  (e : Module.Basis idx ℂ (fixedVectors ρ K.toSubgroup))

/-- Transporting a fixed-space basis through a representation equivalence
preserves every actual compressed matrix entry. -/
theorem fixedMatrix_mapBasis (g : H) (i j : idx) :
    UnitarizabilityContinuation.fixedMatrix mHaar hτ hK
      (e.map (fixedVectorsEquiv E K.toSubgroup)) τ g i j =
    UnitarizabilityContinuation.fixedMatrix mHaar hρ hK e ρ g i j := by
  have hp :
      Hecke.fixedProjection mHaar τ hτ K hK
        (τ g ((e.map (fixedVectorsEquiv E K.toSubgroup)) j)) =
      fixedVectorsEquiv E K.toSubgroup
        (Hecke.fixedProjection mHaar ρ hρ K hK (ρ g (e j))) := by
    rw [Module.Basis.map_apply]
    change Hecke.fixedProjection mHaar τ hτ K hK (τ g (E (e j))) = _
    have hg : τ g (E (e j)) = E (ρ g (e j)) :=
      (Representation.IntertwiningMap.isIntertwining ρ τ E.toIntertwiningMap g (e j)).symm
    rw [hg]
    exact (Hecke.fixedProjection_intertwiner mHaar ρ hρ K hK hτ
      E.toIntertwiningMap (ρ g (e j))).symm
  change (e.map (fixedVectorsEquiv E K.toSubgroup)).repr _ i = e.repr _ i
  rw [hp]
  change e.repr ((fixedVectorsEquiv E K.toSubgroup).symm
    ((fixedVectorsEquiv E K.toSubgroup) _)) i = _
  rw [LinearEquiv.symm_apply_apply]

end Langlands.Compact

namespace Langlands.Plancherel.RationalNormalized

universe u uV un

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance leviMatricesAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance leviMatricesPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  (hG : IsConnectedReductive G) (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))

/-- The full and Levi-normalized fibers agree through the actual normalization
comparison; radical unimodularity follows from the geometric radical. -/
def inducedLeviNormalizationEquiv
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    (complexInduced r h hU π χ).representation.Equiv
      (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).representation :=
  normalizedInductionLeviEquiv h hU
    (parabolicRadical_isUnimodular F G hG A M P U p l a n r hn hU)
    (π.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ))

/-- The actual two fibers have the same irreducibility predicate. -/
abbrev InducedLeviNormalizationIrreducibleIff
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) : Prop :=
  (complexInduced r h hU π χ).IsIrreducible ↔
    (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).IsIrreducible

include hG hn in
theorem inducedLeviNormalization_irreducible_iff
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    InducedLeviNormalizationIrreducibleIff r h hU π χ :=
  ⟨SmoothRep.isIrreducible_of_equiv (inducedLeviNormalizationEquiv r h hU hG hn π χ),
    SmoothRep.isIrreducible_of_equiv (inducedLeviNormalizationEquiv r h hU hG hn π χ).symm⟩

variable (K : OpenSubgroup (rationalPoints G))
  (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
  {idx : Type un}
  (e : Module.Basis idx ℂ
    (fixedVectors (complexInduced r h hU π χ).representation K.toSubgroup))

/-- Carry a full-normalized fiber basis to the actual positive Levi model. -/
def leviFixedBasis :
    Module.Basis idx ℂ
      (fixedVectors
        (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).representation
        K.toSubgroup) :=
  e.map (fixedVectorsEquiv (inducedLeviNormalizationEquiv r h hU hG hn π χ) K.toSubgroup)

variable [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  (mHaar : Measure (rationalPoints G)) [mHaar.IsHaarMeasure]
  (hK : IsCompact (K : Set (rationalPoints G))) [Fintype idx]

/-- The transported basis has exactly the same compressed matrices. -/
abbrev LeviFixedBasisMatrix (g : rationalPoints G) (i j : idx) : Prop :=
  UnitarizabilityContinuation.fixedMatrix mHaar
    (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).isSmooth hK
    (leviFixedBasis r h hU hG hn π K χ e)
    (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).representation
    g i j =
  UnitarizabilityContinuation.fixedMatrix mHaar
    (complexInduced r h hU π χ).isSmooth hK e
    (complexInduced r h hU π χ).representation g i j

theorem leviFixedBasis_matrix (g : rationalPoints G) (i j : idx) :
    LeviFixedBasisMatrix r h hU hG hn π K χ e mHaar hK g i j :=
  Compact.fixedMatrix_mapBasis mHaar (complexInduced r h hU π χ).isSmooth
    (UnramifiedLeviInduction h hU (parabolicLeviRationalNormCharacters r) χ π).isSmooth
    K hK (inducedLeviNormalizationEquiv r h hU hG hn π χ) e g i j

end Langlands.Plancherel.RationalNormalized
