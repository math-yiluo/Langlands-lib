import Langlands.Representation.Exponents.ActualUnitaryGeometricNonvanishing
import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityProof
import Langlands.Representation.Exponents.TemperedUniquenessIntertwiners

/-! # From common induction embeddings to an actual nonzero unitary piece map -/

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

local instance inductionEmbeddingPieceMapAmbientTopology :
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
  (hsemisimple : letI := leviPointTopology l hl
    Representation.IsSemisimpleRepresentation
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
  (hItemp : letI := leviPointTopology l hl
    IsNormalizedExponentTempered hG
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ))
  (hτtemp : letI := leviPointTopology lQ hlQ
    haveI := hlQ.isConnectedReductive.isAffineHom
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    IsNormalizedExponentTempered hlQ.isConnectedReductive τ)
  (i₁ : letI := leviPointTopology l hl
    π.representation.IntertwiningMap
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation)
  (hi₁ : Function.Injective i₁)
  (i₂ : letI := leviPointTopology lQ hlQ
    π.representation.IntertwiningMap
      ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj τ).representation)
  (hi₂ : Function.Injective i₂)

set_option maxHeartbeats 800000 in
/-- Extend the second embedding across the first and apply actual tempered
reciprocity to obtain a nonzero map out of the unitary Jacquet module of the
first induction. The three original carrier universes are independent. -/
def nonzeroUnitaryJacquetMapOfInductionEmbeddings :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    {F : (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ)).representation.IntertwiningMap
      τ.representation // F ≠ 0} := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := hlQ.isConnectedReductive.isAffineHom
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  have : π.representation.IsIrreducible := hπ
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
  have hi₂zero : i₂ ≠ 0 := by
    intro hz
    obtain ⟨y, hy⟩ := exists_ne (0 : π)
    apply hy
    apply hi₂
    rw [hz]
    rfl
  let F := Langlands.nonzeroSemisimpleIntertwiningExtension hsemisimple i₁ hi₁ i₂ hi₂zero
  apply Classical.choice
  obtain ⟨e, _⟩ := temperedInductionUnitaryReciprocity
    k G hG Q L U AL q lQ rQ aL hq hlQ hrQ hmulQ haL
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ) τ hItemp hτtemp
  refine ⟨⟨e F.val, ?_⟩⟩
  intro hz
  apply F.property.1
  apply e.injective
  simpa only [map_zero] using hz

set_option maxHeartbeats 800000 in
/-- Extract an actual intersection-specific nonzero map from a supplied
filtration of the unitary Jacquet module of the first induction. -/
def nonzeroUnitaryPieceMapOfInductionEmbeddings
    {m : ℕ} {z : Fin m → rationalPoints G}
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    {A' : Fin m → CommGroupScheme (Spec (CommRingCat.of k))}
    {a' : ∀ i, (A' i).toGrp ⟶ (D i).M'} (ha' : ∀ i, IsSplitComponent (a' i))
    (s : letI := leviPointTopology l hl
      letI := leviPointTopology lQ hlQ
      ObjectRepFiltration
        (SmoothRep.toRep.obj (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
          ((leviInductionFunctor p l r hp hr hl hmul).obj σ))) m)
    (e : Equiv.Perm (Fin m))
    (hs : letI := leviPointTopology l hl
      ∀ j, Nonempty ((s.gradedRepresentation j).ρ.Equiv
        ((D (e j)).unitaryPieceRep (ha' (e j)) σ).ρ)) :
    Σ i, (D i).NonzeroUnitaryPieceMap (ha' i) σ τ := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  let F := nonzeroUnitaryJacquetMapOfInductionEmbeddings hG p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ haL π σ τ hπ hsemisimple hItemp hτtemp i₁ hi₁ i₂ hi₂
  exact nonzeroUnitaryPieceMapOfFiltration D ha' σ τ s e hs F.val F.property

end Langlands.Aubert.General.RepresentedParabolic
