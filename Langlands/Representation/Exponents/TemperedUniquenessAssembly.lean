import Langlands.Representation.Exponents.TemperedInductionEmbeddingPieceMap
import Langlands.Representation.Exponents.ActualUnitaryPieceInducingTempered

/-! # Conditional uniqueness from common embeddings and an actual unitary filtration -/

noncomputable section

universe u v w x

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (hG : IsConnectedReductive G)

local instance uniquenessAssemblyAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
  (hl : IsRationalLeviSubgroup l) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
  (hlQ : IsRationalLeviSubgroup lQ) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {AL : CommGroupScheme (Spec (CommRingCat.of k))} {aL : AL.toGrp ⟶ L}
  (haL : IsSplitComponent aL)
  (π : SmoothRep.{0, u, x} ℂ (rationalPoints G))
  (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
  (τ : letI := leviPointTopology lQ hlQ; SmoothRep.{0, u, w} ℂ (rationalPoints L))
  (hπ : π.IsIrreducible)
  (hσ : letI := leviPointTopology l hl; σ.IsIrreducible)
  (hτ : letI := leviPointTopology lQ hlQ; τ.IsIrreducible)
  (hσtemp : letI := leviPointTopology l hl
    haveI := hl.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsNormalizedExponentTempered hl.isConnectedReductive σ)
  (hτtemp : letI := leviPointTopology lQ hlQ
    haveI := hlQ.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsNormalizedExponentTempered hlQ.isConnectedReductive τ)
  (hsemisimple : letI := leviPointTopology l hl
    Representation.IsSemisimpleRepresentation
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
  (hItemp : letI := leviPointTopology l hl
    IsNormalizedExponentTempered hG
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ))
  (i₁ : letI := leviPointTopology l hl
    π.representation.IntertwiningMap
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
  (hi₁ : Function.Injective i₁)
  (i₂ : letI := leviPointTopology lQ hlQ
    π.representation.IntertwiningMap
      ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj τ).representation)
  (hi₂ : Function.Injective i₂)
  [MeasurableSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  [hBorelM : letI := leviPointTopology l hl
    BorelSpace (rationalPoints M ⧸ Subgroup.center (rationalPoints M))]
  (haarM : MeasureTheory.Measure (rationalPoints M ⧸ Subgroup.center (rationalPoints M)))
  [hhaarM : letI := leviPointTopology l hl; haarM.IsHaarMeasure]
  (hσsquare : letI := leviPointTopology l hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    IsSquareIntegrableModCenter σ.representation haarM)
  (hcriterionσ : TemperedSquareIntegrableUnitaryPartStatement.{u, v})
  [MeasurableSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  [hBorelL : letI := leviPointTopology lQ hlQ
    BorelSpace (rationalPoints L ⧸ Subgroup.center (rationalPoints L))]
  (haarL : MeasureTheory.Measure (rationalPoints L ⧸ Subgroup.center (rationalPoints L)))
  [hhaarL : letI := leviPointTopology lQ hlQ; haarL.IsHaarMeasure]
  (hτsquare : letI := leviPointTopology lQ hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsSquareIntegrableModCenter τ.representation haarL)
  (hcriterionτ : TemperedSquareIntegrableUnitaryPartStatement.{u, w})
  {m : ℕ} {z : Fin m → rationalPoints G}
  (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ (z i))
  {A' : Fin m → CommGroupScheme (Spec (CommRingCat.of k))}
  {a' : ∀ i, (A' i).toGrp ⟶ (D i).M'} (ha' : ∀ i, IsSplitComponent (a' i))
  {B' : Fin m → CommGroupScheme (Spec (CommRingCat.of k))}
  {b' : ∀ i, (B' i).toGrp ⟶ (D i).L'} (hb' : ∀ i, IsSplitComponent (b' i))
  (hpieces : letI := leviPointTopology l hl
    ∀ i, Representation.IsSemisimpleRepresentation ((D i).unitaryPieceRep (ha' i) σ).ρ)
  (s : letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    ObjectRepFiltration
      (SmoothRep.toRep.obj (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ))) m)
  (e : Equiv.Perm (Fin m))
  (hs : letI := leviPointTopology l hl
    ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
      ((D (e j)).unitaryPieceRep (ha' (e j)) σ).ρ))

include hBorelM hhaarM hBorelL hhaarL in
set_option maxHeartbeats 800000 in
/-- Common embeddings and the supplied actual filtration select an intersection
and recover conjugacy of the original Levi actions. All analytic inputs remain
explicit, including semisimplicity of the literal pieces. -/
def conjugacyOfInductionEmbeddingsAndUnitaryFiltration :
    Σ i, GeometricLemmaIntersectionDatum.FullPieceConjugacy
      (p := p) (l := l) (q := q) (lQ := lQ)
      (hl := hl) (hlQ := hlQ) (z := z i) σ τ := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  obtain ⟨i, F⟩ := nonzeroUnitaryPieceMapOfInductionEmbeddings
    hG p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ haL
    π σ τ hπ hsemisimple hItemp hτtemp i₁ hi₁ i₂ hi₂ D ha' s e hs
  refine ⟨i, ?_⟩
  exact (D i).unitaryPieceConjugacyOfSquareIntegrableNonzeroMapFromOriginalTemperedness
    (ha' := ha' i) (σ := σ) (τ := τ) (F := F)
    (hσtemp := hσtemp) (hτtemp := hτtemp)
    (haarM := haarM) (hσsquare := hσsquare) (hcriterionσ := hcriterionσ)
    (haarL := haarL) (hτsquare := hτsquare) (hcriterionτ := hcriterionτ)
    (hb' := hb' i) (hsemisimple := hpieces i) hσ hτ

end Langlands.Aubert.General.RepresentedParabolic
