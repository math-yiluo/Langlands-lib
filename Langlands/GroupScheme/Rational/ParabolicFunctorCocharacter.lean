import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.MinimalParabolic

/-! # Cocharacters presenting rational parabolic functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The closed affine dynamic representative is geometrically parabolic,
conditional on the published parabolic-dynamic structure statement. -/
theorem Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsParabolicSubgroup (Dynamic.Affine.parabolicHom χ) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (hPD k G hG _ _ (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)).2
    ⟨χ, (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2⟩

/-- Every dynamic parabolic has a geometrically parabolic all-test
representative, conditional on `ParabolicDynamicStatement`. -/
theorem isParabolicFunctor_dynamic_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsParabolicFunctor (Dynamic.parabolic χ) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.parabolicHom χ,
    Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic hPD hG χ,
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ).2⟩

/-- A rational parabolic functor is a dynamic parabolic of a cocharacter
over the ground field, conditional on `ParabolicDynamicStatement`. -/
theorem IsParabolicFunctor.exists_dynamicCocharacter
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {F : SubgroupFunctor G} (hF : IsParabolicFunctor F) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.parabolic χ = F := by
  obtain ⟨P, j, hj, rfl⟩ := hF
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hj.isClosedSubgroup).1 hj
  exact ⟨χ, hχ.symm⟩

/-- Choose a cocharacter over the ground field presenting a rational
parabolic functor. The structural statement remains an explicit input. -/
def IsParabolicFunctor.dynamicCocharacter
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {F : SubgroupFunctor G} (hF : IsParabolicFunctor F) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  Classical.choose (hF.exists_dynamicCocharacter hPD hG)

theorem IsParabolicFunctor.dynamicCocharacter_spec
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {F : SubgroupFunctor G} (hF : IsParabolicFunctor F) :
    Dynamic.parabolic (hF.dynamicCocharacter hPD hG) = F :=
  Classical.choose_spec (hF.exists_dynamicCocharacter hPD hG)

/-- Conditional on the structural statement, the geometric and dynamic
descriptions of rational parabolic functors agree on every test scheme. -/
theorem isParabolicFunctor_iff_exists_dynamicCocharacter
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (F : SubgroupFunctor G) :
    IsParabolicFunctor F ↔
      ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.parabolic χ = F := by
  constructor
  · exact fun hF => hF.exists_dynamicCocharacter hPD hG
  · rintro ⟨χ, rfl⟩
    exact isParabolicFunctor_dynamic_of_parabolicDynamic hPD hG χ

/-- With the structure statement as input, minimality may be tested against
all dynamic parabolics. The order is still the order on all-test functors. -/
theorem isMinimalParabolicFunctor_iff_dynamic_minimal_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {F : SubgroupFunctor G} (hF : IsParabolicFunctor F) :
    IsMinimalParabolicFunctor F ↔
      ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic χ ≤ F → Dynamic.parabolic χ = F := by
  constructor
  · intro hmin χ hle
    exact hmin.2 _ (isParabolicFunctor_dynamic_of_parabolicDynamic hPD hG χ) hle
  · intro hmin
    refine ⟨hF, ?_⟩
    intro F' hF' hle
    rw [← hF'.dynamicCocharacter_spec hPD hG] at hle ⊢
    exact hmin _ hle

/-- In particular a dynamic parabolic is minimal precisely when every
dynamic parabolic contained in it is equal to it, under the structure input. -/
theorem isMinimalParabolicFunctor_dynamic_iff_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsMinimalParabolicFunctor (Dynamic.parabolic χ) ↔
      ∀ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic χ' ≤ Dynamic.parabolic χ →
          Dynamic.parabolic χ' = Dynamic.parabolic χ :=
  isMinimalParabolicFunctor_iff_dynamic_minimal_of_parabolicDynamic hPD hG
    (isParabolicFunctor_dynamic_of_parabolicDynamic hPD hG χ)

end Langlands.GroupScheme
