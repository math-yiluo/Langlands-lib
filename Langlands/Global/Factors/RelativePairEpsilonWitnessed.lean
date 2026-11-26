import Langlands.Global.Factors.RelativePairEpsilonReduction
import Langlands.Correspondence.ArithmeticEpsilonBilinear
import Langlands.VirtualRepresentation.Global.WitnessedLocalMapConjugacy

/-!
# Weil-side virtual pair epsilon factors of exact expansions

The virtual arithmetic pair epsilon relation on unitary Weil classes is the graph of
the bilinear map `epsilonHom` of the basis certificates. That map is the bilinear
arithmetic epsilon map `pairEpsilonHom` on exact K0, evaluated at the canonical
realizations. Hence, if `x` and `y` expand the classes of continuous representations
`A` and `B`, every arithmetic certificate of the zero-monodromy pairs of `A` and `B`
is the virtual epsilon factor of `x` and `y`. For witnessed generators this gives the
Weil side of the generator-level epsilon comparison.
-/

noncomputable section

set_option autoImplicit false

universe uF uV uW uP uE

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (eC : LocalFactor.CommonClosure.ReciprocityFamily F)
  (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} F)
  (hε : LocalFactor.NonabelianSystem.IsSystem F eC ε)
  (ψ : Correspondence.NontrivialAdditiveCharacter F)

/-- The bilinear map of the chosen basis certificates is the bilinear arithmetic epsilon
map on exact K0 at the canonical realizations. -/
theorem epsilonHom_unitaryBasisPairEpsilon_eq :
    epsilonHom (unitaryBasisPairEpsilon.{uF, uV, uE} F eC ε hε ψ
        (hasUnitaryBasisPairEpsilonFactors F eC ε hε ψ)) =
      (Correspondence.pairEpsilonHom F eC ε hε ψ).compl₁₂ (unitaryRealize F)
        (unitaryRealize F) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [bilinear_eq_sum _ x y, bilinear_eq_sum _ x y]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  congr 1
  rw [epsilonHom_generator, LinearMap.compl₁₂_apply]
  obtain ⟨A, hA, hpA⟩ := exists_unitaryRealize_generator F a
  obtain ⟨B, hB, hpB⟩ := exists_unitaryRealize_generator F b
  rw [hA, hB]
  have hcert := Correspondence.isArithmeticPairEpsilonFactor_pairEpsilonHom F eC ε hε ψ A B
  have hg := (hasUnitaryBasisPairEpsilonFactors F eC ε hε ψ a b).choose_spec
  rw [← hpA, ← hpB] at hcert
  obtain ⟨h1, h2⟩ := Correspondence.IsArithmeticPairEpsilonFactor.unique F hg hcert
  refine Prod.ext ?_ ?_
  · change Additive.ofMul (unitaryBasisPairEpsilon F eC ε hε ψ _ a b).1 = _
    rw [unitaryBasisPairEpsilon, h1]
    rfl
  · exact h2

/-- If `x` and `y` expand the exact classes of continuous representations `A` and `B`,
every arithmetic pair epsilon certificate of their zero-monodromy pairs is the virtual
epsilon factor of `x` and `y`. -/
theorem isUnitaryPairEpsilonFactor_of_expansion (x y : UnitaryLattice.{uF, uV} F)
    (A B : {A : LocalWeilRepresentation.{uF, uV} F // A.IsContinuous})
    (hx : ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ A) (includeUnitary F x))
    (hy : ExactExpansion F (ExactGrothendieckGroup.ofRepresentation _ B) (includeUnitary F y))
    {c : ℂˣ} {m : ℤ}
    (h : Correspondence.IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom A.val))
      (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B.val))
      c m) :
    IsUnitaryPairEpsilonFactor F eC ε hε ψ x y (c, m) := by
  rw [isUnitaryPairEpsilonFactor_iff F eC ε hε ψ (hasUnitaryBasisPairEpsilonFactors F eC ε hε ψ),
    epsilonHom_unitaryBasisPairEpsilon_eq, LinearMap.compl₁₂_apply]
  have hx' : unitaryRealize F x = ExactGrothendieckGroup.ofRepresentation _ A := hx
  have hy' : unitaryRealize F y = ExactGrothendieckGroup.ofRepresentation _ B := hy
  rw [hx', hy']
  obtain ⟨h1, h2⟩ := Correspondence.IsArithmeticPairEpsilonFactor.unique F h
    (Correspondence.isArithmeticPairEpsilonFactor_pairEpsilonHom F eC ε hε ψ A B)
  exact Prod.ext h1 h2

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- The Weil side of the generator-level epsilon comparison: an arithmetic pair epsilon
certificate of the local components of two witnessed generators along the local map of
the first is the virtual epsilon factor of their Weil elements. -/
theorem witnessed_isUnitaryPairEpsilonFactor_weil
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
    (ε : LocalFactor.NonabelianSystem.Assignment.{uF, uE} (padicField v))
    (hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε)
    (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v))
    (d e : WitnessedGenerator.{uF, uW, uP} F E c v) {c₀ : ℂˣ} {m : ℤ}
    (h : Correspondence.IsArithmeticPairEpsilonFactor (padicField v) eC ε hε ψ
      (RelativeWeilGroup.localPairClass d.weil d.localMap)
      (RelativeWeilGroup.localPairClass e.weil d.localMap) c₀ m) :
    LocalWeil.IsUnitaryPairEpsilonFactor (padicField v) eC ε hε ψ
      d.weilElement e.weilElement (c₀, m) := by
  have he : LocalWeil.ExactExpansion (padicField v)
      (localExactClass F E c v e.weil e.associated.1 d.localMap)
      (LocalWeil.includeUnitary (padicField v) e.weilElement) := by
    rw [← WitnessedGenerator.localExactClass_localMap_eq F E c v d e e.weil e.associated.1]
    exact e.weil_expansion
  exact LocalWeil.isUnitaryPairEpsilonFactor_of_expansion (padicField v) eC ε hε ψ
    d.weilElement e.weilElement
    ⟨RelativeWeilGroup.localComponent d.weil d.localMap,
      RelativeWeilGroup.localComponent_isContinuous d.localMap d.associated.1⟩
    ⟨RelativeWeilGroup.localComponent e.weil d.localMap,
      RelativeWeilGroup.localComponent_isContinuous d.localMap e.associated.1⟩
    d.weil_expansion he h

end Langlands.Global.PoleComparison
