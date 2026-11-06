import Langlands.Representation.Exponents.LeviSelectedWeights
import Langlands.Representation.Filtration.SelectedGluing
import Langlands.Representation.Filtration.ObjectTransport
import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement

/-! Supplied filtrations on the actual unitary Levi Jacquet module. -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryFiltrationAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  {n : ℕ}

/-- Intersect a supplied actual Levi Jacquet filtration with its zero-real-part
selection, then transport it to the published unitary Jacquet module. -/
def leviUnitaryJacquetFiltration :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ObjectRepFiltration
      (SmoothRep.toRep.obj ((leviJacquetFunctor p l r hp hr hl hmul).obj π)) n →
      ObjectRepFiltration
        (SmoothRep.toRep.obj (leviUnitaryJacquetModule p l r hp hl hr hmul ha π)) n := by
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  intro s
  exact LengthTwo.transport (selectedLeviJacquetEquivUnitary p l r hp hl hr hmul ha π)
    (s.selectedFiltration (rationalPoints.map a)
      ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0))

/-- A unitary vector lies in the transported step exactly when its ambient
vector lies in the original step. -/
theorem mem_leviUnitaryJacquetFiltration_subrepresentation :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (s : ObjectRepFiltration
        (SmoothRep.toRep.obj ((leviJacquetFunctor p l r hp hr hl hmul).obj π)) n)
      (i : Fin (n + 1)) (x : leviUnitaryJacquetModule p l r hp hl hr hmul ha π),
      x ∈ (leviUnitaryJacquetFiltration p l r hp hl hr hmul ha π s).subrepresentation i ↔
        x.val ∈ s.subrepresentation i := fun _ _ _ => Iff.rfl

/-- Each grade of the transported unitary filtration is the selected part of
the original grade, provided that the original ambient Jacquet module is admissible. -/
def leviUnitaryJacquetFiltrationGradedEquiv :
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ (s : ObjectRepFiltration
        (SmoothRep.toRep.obj ((leviJacquetFunctor p l r hp hr hl hmul).obj π)) n)
      (_ : IsAdmissible ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation)
      (i : Fin n),
      ((leviUnitaryJacquetFiltration p l r hp hl hr hmul ha π s).gradedRepresentation i).ρ.Equiv
        (selectedWeightPart (s.gradedRepresentation i).ρ (rationalPoints.map a)
          ha.isCentralSplitTorus.isCentral.map_mem_center
          (fun χ => Plancherel.SplitTorus.normalizedRealPart
            ha.isCentralSplitTorus.1.1 χ = 0)).toRepresentation := by
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  intro s hπ i
  exact (ObjectRepFiltration.equivTransportGradedEquiv
    (s.selectedFiltration (rationalPoints.map a)
      ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0))
    (selectedLeviJacquetEquivUnitary p l r hp hl hr hmul ha π) i).symm.trans
    (s.selectedGradedEquivOfAdmissible (rationalPoints.map a)
      ha.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0) hπ i)

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M N Q L U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryGluingAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  {AL : CommGroupScheme (Spec (CommRingCat.of k))} {aL : AL.toGrp ⟶ L}
  (haL : IsSplitComponent aL) {n : ℕ}

/-- A supplied gluing of the Jacquet-induction functor, at an admissible value,
gives an actual unitary Jacquet filtration with the selected supplied pieces.
The same permutation retains all pieces, including zero pieces. -/
theorem exists_leviUnitaryJacquetInductionFiltration_of_isGluedFrom :
    letI := leviPointTopology l hl
    letI := leviPointTopology lQ hlQ
    haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
    haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
    ∀ (pieces : Fin n →
        SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{max u v} ℂ (rationalPoints L))
      (_ : IsGluedFrom
        (leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ) pieces)
      (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (_ : IsAdmissible
        ((leviJacquetInductionFunctor p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ).obj ρ).ρ),
      ∃ (s : ObjectRepFiltration
          (SmoothRep.toRep.obj
            (leviUnitaryJacquetModule q lQ rQ hq hlQ hrQ hmulQ haL
              ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) n)
        (e : Equiv.Perm (Fin n)),
        ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (selectedWeightPart ((pieces (e i)).obj ρ).ρ (rationalPoints.map aL)
            haL.isCentralSplitTorus.isCentral.map_mem_center
            (fun χ => Plancherel.SplitTorus.normalizedRealPart
              haL.isCentralSplitTorus.1.1 χ = 0)).toRepresentation) := by
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  intro pieces h ρ hρ
  obtain ⟨s, e, hs⟩ := h.exists_objectFiltration ρ
  let π := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  refine ⟨leviUnitaryJacquetFiltration q lQ rQ hq hlQ hrQ hmulQ haL π s, e, fun i => ?_⟩
  obtain ⟨f⟩ := hs i
  exact ⟨(leviUnitaryJacquetFiltrationGradedEquiv q lQ rQ hq hlQ hrQ hmulQ haL π s hρ i).trans
    (selectedWeightEquiv (rationalPoints.map aL)
      haL.isCentralSplitTorus.isCentral.map_mem_center
      (fun χ => Plancherel.SplitTorus.normalizedRealPart haL.isCentralSplitTorus.1.1 χ = 0) f)⟩

end Langlands.Aubert.General.RepresentedParabolic
