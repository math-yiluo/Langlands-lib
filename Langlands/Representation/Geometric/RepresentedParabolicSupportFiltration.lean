import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.Representation.Geometric.SmoothSupportFiltration
import Langlands.Representation.Filtration.Transport
import Langlands.Representation.Aubert.General.CorrectedFiltration

/-! # Support images for the represented-parabolic geometric lemma -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supportAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- Inflation and the positive half modulus, with input on the actual Levi points. -/
def leviInducingFunctor :
    letI := leviPointTopology l hl
    SmoothRep.{0, u, v} ℂ (rationalPoints M) ⥤ Rep.{v} ℂ (pointImage p) :=
  letI := leviPointTopology l hl
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hc := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm ⋙ inflationFunctor h ⋙
    (inductionCharacter (pointImage (r ≫ p)) (pointImage p) hc h.le_normalizer).twistFunctor

/-- The actual normalized induction, restricted to `Q(F)`, with its support filtration. -/
def leviInductionSupportFiltration {m : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) :
    letI := leviPointTopology l hl
    RepFunctorFiltration
      (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
        Rep.resFunctor (pointImage q).subtype) m := by
  letI := leviPointTopology l hl
  exact s.rawSmoothSupportFiltration.precomp (leviInducingFunctor p l r hp hr hl hmul)

/-- Map a natural `Q(F)`-stable subspace into the actual normalized Jacquet quotient,
then transport its action from the Levi image to `L(F)` itself. -/
def leviJacquetImageSubfunctor
    (S : letI := leviPointTopology l hl
      RepSubfunctor
        (leviInductionFunctor.{u, v} p l r hp hr hl hmul ⋙ SmoothRep.toRep ⋙
          Rep.resFunctor (pointImage q).subtype)) :
    letI := leviPointTopology l hl
    RepSubfunctor
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ) := by
  letI := leviPointTopology l hl
  letI := leviPointTopology lQ hlQ
  let h := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
  let hc := isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup
  let I := leviInductionFunctor.{u, v} p l r hp hr hl hmul
  let J := fun A =>
    CorrectedFiltration.jacquetImage h hc (I.obj A) (S.obj A).toSubmodule
      (fun x hx _ hv => (S.obj A).apply_mem_toSubmodule ⟨x, hx⟩ hv)
  exact {
    obj A := {
      toSubmodule := (J A).toSubmodule
      apply_mem_toSubmodule m := (J A).apply_mem_toSubmodule (leviPointsEquiv q lQ hq hlQ m) }
    map_mem := by
      intro A B f x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨SmoothRep.hom (I.map f) y, S.map_mem f hy, rfl⟩ }

set_option maxHeartbeats 800000 in
/-- The canonical support-image filtration on the exact functor of the represented
geometric lemma. No graded-piece comparison is assumed or asserted here. -/
def leviJacquetSupportFiltration {m : ℕ}
    (s : Geometric.OrderedDoubleCosets (pointImage p) (pointImage q) m) :
    letI := leviPointTopology l hl
    RepFunctorFiltration
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
        q lQ rQ hq hrQ hlQ hmulQ) m := by
  letI := leviPointTopology l hl
  let t := leviInductionSupportFiltration.{u, v} p l r hp hr hl hmul q s
  refine {
    step j := leviJacquetImageSubfunctor p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (t.step j)
    monotone A := ?_
    zero A := ?_
    top A := ?_ }
  · intro i j hij x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, t.monotone A hij hy, rfl⟩
  · apply Subrepresentation.toSubmodule_injective
    change Submodule.map _ ((t.step 0).obj A).toSubmodule = ⊥
    rw [t.zero A]
    exact Submodule.map_bot _
  · apply le_antisymm le_top
    intro x _
    obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective
      ((leviInductionFunctor p l r hp hr hl hmul).obj A).representation
        (pointImage (rQ ≫ q)) 1 x
    exact ⟨y, t.top A ▸ Submodule.mem_top, rfl⟩

end Langlands.Aubert.General.RepresentedParabolic
