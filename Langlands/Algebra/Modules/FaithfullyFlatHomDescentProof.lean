import Langlands.Algebra.Modules.FaithfullyFlatHomDescentStatements
import Mathlib.Algebra.Category.ModuleCat.Descent

/-! # Proof of faithfully flat descent for compatible module morphisms -/

universe u

open CategoryTheory ModuleCat

namespace Langlands.Algebra.Modules

/-- Mathlib's faithfully flat comonadicity uses the extension/restriction
adjunction, so its comparison functor is an equivalence. -/
private lemma comparison_isEquivalence {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.FaithfullyFlat) :
    (Comonad.comparison (extendRestrictScalarsAdj.{u} f)).IsEquivalence :=
  (comonadicExtendScalars hf).eqv

/-- Fullness and faithfulness of the comparison functor descend compatible
module morphisms uniquely. -/
theorem faithfullyFlatModuleHomDescent :
    FaithfullyFlatModuleHomDescentStatement.{u} := by
  intro A B _ _ f hf M N g hg
  let K := Comonad.comparison (extendRestrictScalarsAdj.{u} f)
  let : K.IsEquivalence := comparison_isEquivalence hf
  let g' : K.obj M ⟶ K.obj N := ⟨g, hg.symm⟩
  refine ⟨K.preimage g', ?_, ?_⟩
  · exact congrArg Comonad.Coalgebra.Hom.f (K.map_preimage g')
  · intro h hh
    apply K.map_injective
    apply Comonad.Coalgebra.Hom.ext
    exact hh.trans (congrArg Comonad.Coalgebra.Hom.f (K.map_preimage g')).symm

/-- Full faithfulness also descends compatible module isomorphisms uniquely. -/
theorem faithfullyFlatModuleIsoDescent :
    FaithfullyFlatModuleIsoDescentStatement.{u} := by
  intro A B _ _ f hf M N e he
  let K := Comonad.comparison (extendRestrictScalarsAdj.{u} f)
  let : K.IsEquivalence := comparison_isEquivalence hf
  let e' : K.obj M ≅ K.obj N := Comonad.Coalgebra.isoMk e he.symm
  refine ⟨K.preimageIso e', ?_, ?_⟩
  · apply Iso.ext
    exact congrArg Comonad.Coalgebra.Hom.f (K.map_preimage e'.hom)
  · intro e₀ he₀
    apply Iso.ext
    apply K.map_injective
    apply Comonad.Coalgebra.Hom.ext
    exact (congrArg Iso.hom he₀).trans
      (congrArg Comonad.Coalgebra.Hom.f (K.map_preimage e'.hom)).symm

/-- The combined module morphism and isomorphism descent statement. -/
theorem faithfullyFlatModuleHomIsoDescent :
    FaithfullyFlatModuleHomIsoDescentStatement.{u} :=
  ⟨faithfullyFlatModuleHomDescent, faithfullyFlatModuleIsoDescent⟩

end Langlands.Algebra.Modules
