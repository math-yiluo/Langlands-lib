import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.IntegerCentralizer

/-! # Torus units fix the apartment through any source factorization -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- Under V6, the character-valuation kernel of any source mapping to the
apartment torus fixes every image of an apartment point. -/
def TorusUnitApartmentFixationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (A : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (D : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i),
    IntegerValuation.IsOmegaCompatible v D C →
    ∀ (e : A ⟶ T.toGrp) (a : rationalPoints A),
      a ∈ characterValuationKernel v A →
      ∀ x : D.Apartment, rationalPoints.map (e ≫ i) a • D.apartmentMap x =
        D.apartmentMap x

/-- Map a unit through the torus and its actual centralizer, then apply the
existing V6 centralizer fixation theorem. -/
theorem torusUnitApartmentFixation : TorusUnitApartmentFixationStatement.{u} := by
  intro k _ v A T G i _ _ D C hD e a ha x
  have hfix := hD.map_mem_reducedFixer
    (IntegerValuation.map_mem_characterValuationKernel v (e ≫ C.s) ha) x
  rw [D.mem_reducedFixer] at hfix
  have he : e ≫ C.s ≫ C.j = e ≫ i := by rw [C.comp_eq]
  have hp := congrArg (fun f => rationalPoints.map f a) he
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom] at hp
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc, hp] using hfix

/-- Scalar-extended units of a subgroup of the apartment torus fix its
apartment image. No splitness or Galois hypothesis is needed for this
elementary implication. -/
theorem isFixedByScalarTorusUnits_apartmentMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    {A : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (e : A ⟶ T.toGrp)
    [Mono ((GroupScheme.baseChange (baseMap k K)).map i).hom.hom.left]
    [IsAffineHom (baseChanged k K G).X.hom]
    (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (baseMap k K)).obj T)
      ((GroupScheme.baseChange (baseMap k K)).map i) (IntegerValuation.order v))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (baseMap k K)).obj T)
      ((GroupScheme.baseChange (baseMap k K)).map i))
    (hD : IntegerValuation.IsOmegaCompatible v D C) (x : D.Apartment) :
    IsFixedByScalarTorusUnits k K v (e ≫ i) (D.apartmentMap x) := by
  intro a ha
  rw [Functor.map_comp]
  exact torusUnitApartmentFixation K v (baseChanged k K A)
    ((CommGroupScheme.baseChange (baseMap k K)).obj T) (baseChanged k K G)
    ((GroupScheme.baseChange (baseMap k K)).map i) D C hD
    ((GroupScheme.baseChange (baseMap k K)).map e) a ha x

end Langlands.Geometry.Building
