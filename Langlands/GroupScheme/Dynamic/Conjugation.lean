import Langlands.GroupScheme.NormalizedSubgroup
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Scheme morphisms for the action of a dynamic parabolic on its unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G P U : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
  {iP : P ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hU : (unipotent χ).IsRepresentedBy iU)

include hP hU

/-- The representing inclusion of `U(χ)` is normalized by that of `P(χ)`. -/
theorem range_unipotent_isNormalizedBy_range_parabolic :
    (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range iP) := by
  rw [hU.2, hP.2]
  exact unipotent_isNormalizedBy_parabolic χ

/-- Conjugation by the represented dynamic parabolic on the represented dynamic
unipotent subgroup, as a morphism of schemes over `S`. -/
def parabolicConjugation : P.X ⊗ U.X ⟶ U.X :=
  SubgroupFunctor.normalizedConjugation iU iP
    (range_unipotent_isNormalizedBy_range_parabolic hP hU)

theorem parabolicConjugation_comp :
    parabolicConjugation hP hU ≫ iU.hom.hom =
      SubgroupFunctor.conjugationMap iU iP :=
  SubgroupFunctor.normalizedConjugation_comp _ _ _

theorem lift_comp_parabolicConjugation_comp {T : Over S}
    (p : T ⟶ P.X) (u : T ⟶ U.X) :
    (lift p u ≫ parabolicConjugation hP hU) ≫ iU.hom.hom =
      (p ≫ iP.hom.hom) * (u ≫ iU.hom.hom) * (p ≫ iP.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp _ _ _ p u

theorem parabolicConjugation_unique (a : P.X ⊗ U.X ⟶ U.X)
    (ha : a ≫ iU.hom.hom = SubgroupFunctor.conjugationMap iU iP) :
    a = parabolicConjugation hP hU := by
  let := hU.1
  exact SubgroupFunctor.normalizedConjugation_unique _ _ _ a ha

theorem parabolicConjugation_naturality {T T' : Over S} (f : T' ⟶ T)
    (p : T ⟶ P.X) (u : T ⟶ U.X) :
    f ≫ (lift p u ≫ parabolicConjugation hP hU) =
      lift (f ≫ p) (f ≫ u) ≫ parabolicConjugation hP hU :=
  SubgroupFunctor.normalizedConjugation_naturality _ _ _ f p u

/-- The conjugation action of `P(T)` on `U(T)` by group automorphisms, induced by
`parabolicConjugation`. -/
def parabolicConjAction (T : Over S) : (T ⟶ P.X) →* MulAut (T ⟶ U.X) := by
  letI := hU.1
  exact SubgroupFunctor.normalizedConjAction iU iP
    (range_unipotent_isNormalizedBy_range_parabolic hP hU) T

theorem parabolicConjAction_apply (T : Over S) (p : T ⟶ P.X) (u : T ⟶ U.X) :
    parabolicConjAction hP hU T p u = lift p u ≫ parabolicConjugation hP hU :=
  rfl

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : CommRingCat.{u}) (e : n → ℤ)

/-- The concrete closed block unipotent subgroup is normalized by the concrete closed
block parabolic subgroup, on every test scheme. -/
theorem range_blockUnipotent_isNormalizedBy_range_blockParabolic :
    (SubgroupFunctor.range (blockUnipotentHom n R e)).IsNormalizedBy
      (SubgroupFunctor.range (blockParabolicHom n R e)) := by
  rw [(isRepresentedBy_blockUnipotent n R e).2, (isRepresentedBy_blockParabolic n R e).2,
    ← unipotent_diagonalCocharacter, ← parabolic_diagonalCocharacter]
  exact Dynamic.unipotent_isNormalizedBy_parabolic (diagonalCocharacter n R e)

/-- The conjugation action of the block parabolic on the block unipotent subgroup,
as a morphism between the published quotient schemes. -/
def blockParabolicConjugation :
    (blockParabolicScheme n R e).X ⊗ (blockUnipotentScheme n R e).X ⟶
      (blockUnipotentScheme n R e).X :=
  SubgroupFunctor.normalizedConjugation (blockUnipotentHom n R e)
    (blockParabolicHom n R e) (range_blockUnipotent_isNormalizedBy_range_blockParabolic n R e)

theorem blockParabolicConjugation_comp :
    blockParabolicConjugation n R e ≫ (blockUnipotentHom n R e).hom.hom =
      SubgroupFunctor.conjugationMap (blockUnipotentHom n R e) (blockParabolicHom n R e) :=
  SubgroupFunctor.normalizedConjugation_comp _ _ _

theorem lift_comp_blockParabolicConjugation_comp {T : Over (Spec R)}
    (p : T ⟶ (blockParabolicScheme n R e).X)
    (u : T ⟶ (blockUnipotentScheme n R e).X) :
    (lift p u ≫ blockParabolicConjugation n R e) ≫ (blockUnipotentHom n R e).hom.hom =
      (p ≫ (blockParabolicHom n R e).hom.hom) * (u ≫ (blockUnipotentHom n R e).hom.hom) *
        (p ≫ (blockParabolicHom n R e).hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp _ _ _ p u

/-- On every test scheme the underlying matrix of the action is ordinary
matrix conjugation in `GL_n(Γ(T, 𝒪_T))`. -/
theorem pointsEquiv_blockParabolicConjugation {T : Over (Spec R)}
    (p : T ⟶ (blockParabolicScheme n R e).X)
    (u : T ⟶ (blockUnipotentScheme n R e).X) :
    pointsEquiv n R T
        ((lift p u ≫ blockParabolicConjugation n R e) ≫
          (blockUnipotentHom n R e).hom.hom) =
      pointsEquiv n R T (p ≫ (blockParabolicHom n R e).hom.hom) *
        pointsEquiv n R T (u ≫ (blockUnipotentHom n R e).hom.hom) *
          (pointsEquiv n R T (p ≫ (blockParabolicHom n R e).hom.hom))⁻¹ := by
  rw [lift_comp_blockParabolicConjugation_comp]
  simp only [map_mul, map_inv]

theorem blockParabolicConjugation_naturality {T T' : Over (Spec R)} (f : T' ⟶ T)
    (p : T ⟶ (blockParabolicScheme n R e).X)
    (u : T ⟶ (blockUnipotentScheme n R e).X) :
    f ≫ (lift p u ≫ blockParabolicConjugation n R e) =
      lift (f ≫ p) (f ≫ u) ≫ blockParabolicConjugation n R e :=
  SubgroupFunctor.normalizedConjugation_naturality _ _ _ f p u

/-- The concrete block action on `T`-points, induced by `blockParabolicConjugation`. -/
def blockParabolicConjAction (T : Over (Spec R)) :
    (T ⟶ (blockParabolicScheme n R e).X) →* MulAut (T ⟶ (blockUnipotentScheme n R e).X) := by
  letI := (isRepresentedBy_blockUnipotent n R e).1
  exact SubgroupFunctor.normalizedConjAction (blockUnipotentHom n R e)
    (blockParabolicHom n R e) (range_blockUnipotent_isNormalizedBy_range_blockParabolic n R e) T

theorem blockParabolicConjAction_apply (T : Over (Spec R))
    (p : T ⟶ (blockParabolicScheme n R e).X)
    (u : T ⟶ (blockUnipotentScheme n R e).X) :
    blockParabolicConjAction n R e T p u = lift p u ≫ blockParabolicConjugation n R e :=
  rfl

end Langlands.GroupScheme.GeneralLinear
