import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyReductionStatement
import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitStatement
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerStatement
import Langlands.GroupScheme.Rational.SharpCentralizerConjugacyReduction

/-! # Reduction of unramified sharp torus conjugacy to its structural inputs -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The actual centralizer and conjugacy interfaces assemble sharp conjugacy of
maximally split maximal tori over any field where the ambient group is quasi-split.
The three structural statements are retained as premises of this reduction. -/
theorem exists_cover_conjugacy_of_quasi_split_maximal_tori
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hprod : SimplyConnectedCentralizerProductStatement.{u})
    (hcent : QuasiSplitMaximalTorusCentralizerStatement.{u})
    {k : Type u} [Field k]
    {H D C : GroupScheme (Spec (CommRingCat.of k))}
    (d : D ⟶ H) (π : C ⟶ D)
    (hcover : IsSimplyConnectedDerivedCover d π) (hquasi : IsQuasiSplit H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ H) (i' : T'.toGrp ⟶ H)
    (hi : IsMaximallySplitMaximalTorus i)
    (hi' : IsMaximallySplitMaximalTorus i') :
    ∃ g ∈ simplyConnectedImage d π, ∃ e : T.toGrp ≅ T'.toGrp,
      i ≫ (H.innerIso g).hom = e.hom ≫ i' := by
  obtain ⟨hi, A, a, f, ha, hf⟩ := hi
  obtain ⟨hi', A', a', f', ha', hf'⟩ := hi'
  exact exists_cover_conjugacy_of_maximal_split_centralizers hconj hprod
    a a' i i' d π hcover ha ha'
    (hcent k H hquasi T A i a f hi ha hf)
    (hcent k H hquasi T' A' i' a' f' hi' ha' hf')

/-- Conditional assembly of the exact unramified target. Each geometric or
structural input remains an explicit premise; this does not prove the target
without these inputs. -/
theorem unramifiedSharpTorusConjugacy_of_structure
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hprod : SimplyConnectedCentralizerProductStatement.{u})
    (hcent : QuasiSplitMaximalTorusCentralizerStatement.{u})
    (hquasi : UnramifiedQuasiSplitStatement.{u}) :
    UnramifiedSharpTorusConjugacyStatement.{u} := by
  intro F _ _ _ _ H D C d π hcover T T' i i' hi hi'
  exact exists_cover_conjugacy_of_quasi_split_maximal_tori hconj hprod hcent
    d π hcover (hquasi F H hcover.isConnectedReductive) i i' hi hi'

/-- Exact proof of the published four-input reduction proposition. -/
theorem unramifiedSharpTorusConjugacyReduction :
    UnramifiedSharpTorusConjugacyReductionStatement.{u} :=
  unramifiedSharpTorusConjugacy_of_structure

end Langlands.Geometry.Building
