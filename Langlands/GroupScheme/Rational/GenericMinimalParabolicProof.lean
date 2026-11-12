import Langlands.GroupScheme.Rational.GenericMinimalParabolicReduction
import Langlands.GroupScheme.Rational.ParabolicFunctorCocharacter
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.GenericParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Generic cocharacters of maximal split tori define minimal rational parabolics: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Assemble the exact generic-minimality target from `ParabolicDynamicStatement`.
A cocharacter whose dynamic parabolic lies in `P_G(ν)` is conjugated into the torus by a
rational point of `P_G(ν)`; the root-sign comparison and root negation then force
equality. -/
theorem genericMinimalParabolic_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) :
    GenericMinimalParabolicStatement.{u} := by
  intro k _ G hG T i hi ν
  let := hG.isAffineHom
  change IsGenericCocharacter i ν →
    IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))
  intro hν
  apply (isMinimalParabolicFunctor_dynamic_iff_of_parabolicDynamic hPD hG _).mpr
  intro χ hle
  obtain ⟨g, hg, ρ, hχ⟩ := exists_parabolic_conj_into_torus hG hi ν
    (genericCentralizer k G hG T i hi ν hν) χ ((Dynamic.range_le_parabolic χ).trans hle)
  have hinv :
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).comap (G.innerIso g).hom =
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    SubgroupFunctor.comap_innerIso_hom_eq_of_mem _ hg
  have hχcomap := Dynamic.parabolic_eq_comap_of_iso χ (G.innerIso g)
  rw [hχ] at hχcomap
  have hρ : Dynamic.parabolic (ρ ≫ i) ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
    apply (SubgroupFunctor.comap_iso_le_comap_iso_iff (G.innerIso g)).mp
    rw [← hχcomap, hinv]
    exact hle
  have heq : Dynamic.parabolic (ρ ≫ i) = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
    generic_dynamicParabolic_eq_of_le relativeRootSignInclusions relativeRootNegation
      k G hG T i hi ν (Additive.ofMul ρ) hν hρ
  rw [heq, hinv] at hχcomap
  exact hχcomap

/-- **Generic cocharacters define minimal rational parabolics** (Borel–Tits 4.15(a)
and 4.16). For a connected reductive group over any field and an actual maximal split
torus, the dynamic parabolic of every generic cocharacter is represented by a geometric
parabolic subgroup and is minimal among rational parabolic subgroup functors, tested on
every scheme over the field. -/
theorem genericMinimalParabolic : GenericMinimalParabolicStatement.{u} :=
  genericMinimalParabolic_of_parabolicDynamic parabolicDynamic

end Langlands.GroupScheme
