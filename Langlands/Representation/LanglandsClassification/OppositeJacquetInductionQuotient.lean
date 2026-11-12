import Langlands.Representation.LanglandsClassification.RegularOppositeLanglandsHead
import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityReduction

/-! # Induction quotients from nonzero opposite Jacquet maps

A supplied second adjunction converts a nonzero map into an opposite
Jacquet module into a nonzero induction map. Irreducibility of the target
makes the latter surjective. Carrier universes remain independent.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M N Q U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance jacquetQuotientAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- A supplied second adjunction converts a nonzero opposite Jacquet map
into a surjection from actual induction onto an irreducible target, even
when the target's carrier universe does not contain the field universe. -/
theorem exists_surjective_leviInduction_of_nonzero_jacquetMap
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible)
    (j : letI := leviPointTopology l hl
      σ.representation.IntertwiningMap
        ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π).representation)
    (hj : j ≠ 0) :
    letI := leviPointTopology l hl
    ∃ t : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
      π.representation, Function.Surjective t := by
  let := leviPointTopology l hl
  let σ' := SmoothRep.universeLift.{u} σ
  let π' := SmoothRep.universeLift.{u} π
  let eσ := SmoothRep.universeLiftEquiv.{u} σ
  let eπ := SmoothRep.universeLiftEquiv.{u} π
  let eJ := leviJacquetEquivOfEquiv q lQ rQ hq hlQ hrQ hmulQ π π' eπ
  let J := intertwiningMapCongr eσ eJ
  have hJzero : J 0 = 0 := by
    ext x
    change eJ (0 : (leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π) = 0
    exact map_zero eJ
  have hj' : J j ≠ 0 := by
    intro hz
    exact hj (J.injective (hz.trans hJzero.symm))
  let : (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).Additive :=
    { map_add := by
        intro A B f g
        apply ObjectProperty.hom_ext
        ext x
        rfl }
  let F := adj.homAddEquiv σ' π'
  let t' := F.symm (SmoothRep.ofHom (J j))
  have ht' : t' ≠ 0 := by
    intro hz
    apply hj'
    have h : SmoothRep.ofHom (J j) = 0 := by
      calc
        SmoothRep.ofHom (J j) = F t' := (F.apply_symm_apply _).symm
        _ = 0 := by rw [hz, map_zero]
    exact congrArg SmoothRep.hom h
  let eI := leviInductionEquivOfEquiv p l r hp hl hr hmul σ σ' eσ
  let t := (intertwiningMapCongr eI eπ).symm (SmoothRep.hom t')
  have ht : t ≠ 0 := by
    intro hz
    apply ht'
    apply ObjectProperty.hom_ext
    have hzero : intertwiningMapCongr eI eπ 0 = 0 := by
      ext x
      change eπ (0 : π) = 0
      exact map_zero eπ
    have h : SmoothRep.hom t' = 0 := by
      calc
        SmoothRep.hom t' = intertwiningMapCongr eI eπ t :=
          ((intertwiningMapCongr eI eπ).apply_symm_apply _).symm
        _ = 0 := by rw [hz]; exact hzero
    ext x
    exact congrArg (fun f => f x) h
  let := hπ
  exact ⟨t, (Representation.IsIrreducible.surjective_or_eq_zero t).resolve_right ht⟩

/-- Choose an actual surjective intertwiner onto the original irreducible
target from the supplied second adjunction and nonzero Jacquet map. -/
def leviInductionQuotientOfJacquetMap
    (adj : letI := leviPointTopology l hl
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul ⊣
        leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : π.IsIrreducible)
    (j : letI := leviPointTopology l hl
      σ.representation.IntertwiningMap
        ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj π).representation)
    (hj : j ≠ 0) :
    letI := leviPointTopology l hl
    {t : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
      π.representation // Function.Surjective t} :=
  ⟨(exists_surjective_leviInduction_of_nonzero_jacquetMap
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ adj σ π hπ j hj).choose,
    (exists_surjective_leviInduction_of_nonzero_jacquetMap
      p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ adj σ π hπ j hj).choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic
