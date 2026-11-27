import Langlands.AllFieldBZ.Representation.Classification.NonadjacentAssembly
import Langlands.AllFieldBZ.Representation.Classification.TwoSupercuspidalProductDualTwist
import Langlands.AllFieldBZ.Representation.Derivative.OrderedCuspidalProductTwistOne
import Langlands.Representation.Classification.NonadjacentSpecialization

/-!
# All-field port of `Langlands.Representation.Classification.NonadjacentSpecialization`

Specialization of the BZ77 Theorem 4.2 core (`NonadjacentAssembly`) to
two supercuspidal blocks.

A nonzero invariant form between irreducible `A` and `ν B~` forces `B ≅ ν A`; under
the nonadjacency hypotheses and integral twist freeness, no such form exists
between the derivative pieces of `ρ × ρ'` and of `ν (ρ × ρ')~`.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.Classification.NonadjacentAssembly

open Langlands.Classification

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Derivative Langlands.InvariantBilinear

universe uF u uV uW

section Classes

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

open Langlands.Classification.ProductDualTwist

/-- A nonzero invariant form between `A` and `ν B'~` forces `B' ≅ ν A`. -/
theorem twist_class_eq_of_length_ne_zero' {a : ℕ}
    (A B' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a))
    (hB : letI := T.topology
      length A.obj.representation (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').obj.representation
        (fun _ => (1 : ℂ)) ≠ 0) :
    letI := T.topology
    B'.isoClass = T.supercuspidalClassRealPowerTwist a 1 A.isoClass := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup a
  have hcof := Langlands.GeneralLinear.compactOpen_cofinal_allFieldBZ F T a
  have hsc := T.supercuspidalContragredientClosed Langlands.GeneralLinear.supercuspidalContragredient_allFieldBZ.{uF, uV} a
  have hnt : Nontrivial (forms A.obj.representation (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').obj.representation
      (fun _ => (1 : ℂ))) := by
    rw [← not_subsingleton_iff_nontrivial]
    exact fun h => hB (Module.length_eq_zero_iff.mpr h)
  obtain ⟨β, hβ⟩ := exists_ne (0 : forms A.obj.representation
    (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').obj.representation (fun _ => (1 : ℂ)))
  obtain ⟨E⟩ := Langlands.Classification.NonadjacentAssembly.nonempty_equiv_of_forms_ne_zero hcof A.property.2.1
    (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').obj.isSmooth A.property.1 (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').property.1 β hβ
  have hc : SupercuspidalClass.contragredient hcof hsc A.isoClass =
      (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').isoClass :=
    (SupercuspidalClass.contragredient_isoClass_eq_isoClass_iff hcof hsc A _).mpr ⟨E.symm⟩
  have hA : A.isoClass = T.supercuspidalClassRealPowerTwist a (-1) B'.isoClass := by
    rw [← SupercuspidalClass.contragredient_contragredient hcof hsc A.isoClass, hc]
    change SupercuspidalClass.contragredient hcof hsc
      (SupercuspidalClass.twist _ _ _ (SupercuspidalClass.contragredient hcof hsc B'.isoClass)) = _
    rw [SupercuspidalClass.contragredient_twist, SupercuspidalClass.contragredient_contragredient]
    exact SupercuspidalClass.twist_congr
      (realPowerCharacter_neg (T.determinantNorm a) 1).symm _ _ _ _ _
  rw [hA, T.supercuspidalClassRealPowerTwist_add, add_neg_cancel,
    T.supercuspidalClassRealPowerTwist_zero]

/-- A nonzero invariant form between `A` and `ν B'~`, after identifying both
ranks with `m`, forces `B' ≅ ν A` as rank-indexed supercuspidal classes. -/
theorem twist_class_eq_of_length_ne_zero {a b m : ℕ}
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a))
    (B' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := b))
    (h1 : a = m) (h2 : b = m)
    (hB : letI := T.topology
      length ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h1).obj A.obj).representation
        ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h2).obj (Langlands.AllFieldBZ.Classification.ProductDualTwist.dualTwist F T B').obj).representation
        (fun _ => (1 : ℂ)) ≠ 0) :
    letI := T.topology
    (⟨b, B'.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
      ⟨a, T.supercuspidalClassRealPowerTwist a 1 A.isoClass⟩ := by
  subst h1 h2
  exact congrArg (Sigma.mk _) (twist_class_eq_of_length_ne_zero' F T A B' hB)

/-- No positive-rank supercuspidal class is fixed by `ν`, as a rank-indexed class. -/
theorem sigma_ne_twist {a : ℕ} (ha : 0 < a)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    (⟨a, A.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨a, T.supercuspidalClassRealPowerTwist a 1 A.isoClass⟩ := by
  let _ := T.topology
  intro h
  have h' : A.isoClass = T.supercuspidalClassRealPowerTwist a 1 A.isoClass :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hfix : (LocalFieldPackage.TopologicalData.CuspidalDatum.mk a ha A.isoClass :
      T.CuspidalDatum.{uV, uF}).twist 1 =
        LocalFieldPackage.TopologicalData.CuspidalDatum.mk a ha A.isoClass := by
    change LocalFieldPackage.TopologicalData.CuspidalDatum.mk a ha
      (T.supercuspidalClassRealPowerTwist a 1 A.isoClass) = _
    rw [← h']
  exact Langlands.AllFieldBZ.Derivative.OrderedCuspidalProductTwistOne.twist_one_ne_self T _ hfix

end Classes

end Langlands.AllFieldBZ.Classification.NonadjacentAssembly
