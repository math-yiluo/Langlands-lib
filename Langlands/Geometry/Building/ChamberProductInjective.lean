import Langlands.Geometry.Building.ChamberIwahori
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-!
# Injectivity of the sharp and full chamber products

Opposite-cell injectivity and uniqueness of dynamic limits distinguish the
three factors. This argument applies to every cocharacter and every subset.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

section Restriction

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Restrict the opposite-unipotent/centralizer/unipotent product to any
negative and positive subgroups and any injectively mapped central factor. -/
theorem unipotentTripleProduct_injective
    (Uminus Uplus : Subgroup (rationalPoints G))
    {Z : Type u} (j : Z → rationalPoints G) (hj : Function.Injective j)
    (hminus : Uminus ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)).carrier (Over.mk (𝟙 _)))
    (hplus : Uplus ≤
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hcentral : ∀ z, j z ∈ centralizerPoints i) :
    Function.Injective (fun p : Uminus × Z × Uplus =>
      (p.1 : rationalPoints G) * j p.2.1 * (p.2.2 : rationalPoints G)) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := Dynamic.oppositeCocharacter χ
  let X : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  have hz (z : Z) : j z ∈ (Dynamic.centralizer χ).carrier X := by
    apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ν) X
    change j z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _))
    rw [torusCentralizer_carrier_base]
    exact hcentral z
  have hm (v : Uminus) : (v : rationalPoints G) ∈ (Dynamic.unipotent χminus).carrier X := by
    have h := hminus v.property
    rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at h
    exact h
  let f : Uminus × Z × Uplus →
      (Dynamic.unipotent χminus).carrier X × (Dynamic.parabolic χ).carrier X :=
    fun p => (⟨p.1, hm p.1⟩,
      ⟨j p.2.1 * p.2.2,
        Subgroup.mul_mem _ (Dynamic.centralizer_le_parabolic χ X (hz p.2.1))
          (Dynamic.unipotent_le_parabolic χ X (hplus p.2.2.property))⟩)
  intro p q hpq
  have hpairs : f p = f q :=
    hasInjectiveOppositeCellMultiplication_of_isAffine i ν X
      (by simpa only [f, mul_assoc] using hpq)
  have hv : (p.1 : rationalPoints G) = q.1 :=
    congrArg (fun r : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (r.1 : rationalPoints G)) hpairs
  have hzu : j p.2.1 * (p.2.2 : rationalPoints G) =
      j q.2.1 * (q.2.2 : rationalPoints G) :=
    congrArg (fun r : (Dynamic.unipotent χminus).carrier X ×
      (Dynamic.parabolic χ).carrier X => (r.2 : rationalPoints G)) hpairs
  have hlimp : Dynamic.HasLimit χ (j p.2.1 * (p.2.2 : rationalPoints G)) (j p.2.1) := by
    simpa only [mul_one] using
      (Dynamic.hasLimit_of_mem_centralizer χ (hz p.2.1)).mul χ (hplus p.2.2.property)
  have hlimq : Dynamic.HasLimit χ (j p.2.1 * (p.2.2 : rationalPoints G)) (j q.2.1) := by
    rw [hzu]
    simpa only [mul_one] using
      (Dynamic.hasLimit_of_mem_centralizer χ (hz q.2.1)).mul χ (hplus q.2.2.property)
  have hzj : j p.2.1 = j q.2.1 := hlimp.unique χ hlimq
  have hu : (p.2.2 : rationalPoints G) = q.2.2 := by
    rw [hzj] at hzu
    exact mul_left_cancel hzu
  exact Prod.ext (Subtype.ext hv) (Prod.ext (hj hzj) (Subtype.ext hu))

end Restriction

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The actual sharp three-factor multiplication is injective, for arbitrary
subsets, points and cocharacters. -/
theorem sharpUnipotentProduct_injective (C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S) : Function.Injective (D.sharpUnipotentProduct C x ν) :=
  unipotentTripleProduct_injective i ν
    (D.sharpUnipotentPoints (-ν) C) (D.sharpUnipotentPoints ν C)
    (fun z : D.sharpCentralizer {x} => (z : rationalPoints G))
    Subtype.val_injective inf_le_left inf_le_left (fun z => z.property.1)

/-- The sharp product, with its original value in `G(k)`, as an embedding. -/
def sharpUnipotentProductEmbedding (C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S) :
    (D.sharpUnipotentPoints (-ν) C × D.sharpCentralizer {x} ×
      D.sharpUnipotentPoints ν C) ↪ rationalPoints G where
  toFun := D.sharpUnipotentProduct C x ν
  inj' := D.sharpUnipotentProduct_injective C x ν

@[simp] theorem sharpUnipotentProductEmbedding_apply (C : Set D.Apartment) (x : D.Apartment)
    (ν : cocharacterLattice S) (p : D.sharpUnipotentPoints (-ν) C ×
      D.sharpCentralizer {x} × D.sharpUnipotentPoints ν C) :
    D.sharpUnipotentProductEmbedding C x ν p = D.sharpUnipotentProduct C x ν p :=
  rfl

end KPApartmentData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual full three-factor multiplication is injective, for every
subset and cocharacter, with central factor `Z(F)^0`. -/
theorem iwahoriUnipotentProduct_injective (C : Set P.Apartment)
    (ν : cocharacterLattice P.S) : Function.Injective (P.iwahoriUnipotentProduct C ν) := by
  apply unipotentTripleProduct_injective P.i ν
    (P.iwahoriUnipotentPoints (-ν) C) (P.iwahoriUnipotentPoints ν C)
    (fun z : P.centralizerZero => rationalPoints.map P.centralizer.j z)
  · intro z w h
    apply Subtype.ext
    have : Mono P.centralizer.j.hom.hom := P.centralizer.isRepresentedBy.1
    exact (cancel_mono P.centralizer.j.hom.hom).mp h
  · exact inf_le_left
  · exact inf_le_left
  · intro z
    exact map_mem_centralizerPoints P.centralizer.isRepresentedBy z

/-- The full product, with its actual centralizer inclusion, as an embedding. -/
def iwahoriUnipotentProductEmbedding (C : Set P.Apartment) (ν : cocharacterLattice P.S) :
    (P.iwahoriUnipotentPoints (-ν) C × P.centralizerZero ×
      P.iwahoriUnipotentPoints ν C) ↪ rationalPoints G where
  toFun := P.iwahoriUnipotentProduct C ν
  inj' := P.iwahoriUnipotentProduct_injective C ν

@[simp] theorem iwahoriUnipotentProductEmbedding_apply (C : Set P.Apartment)
    (ν : cocharacterLattice P.S) (p : P.iwahoriUnipotentPoints (-ν) C ×
      P.centralizerZero × P.iwahoriUnipotentPoints ν C) :
    P.iwahoriUnipotentProductEmbedding C ν p = P.iwahoriUnipotentProduct C ν p :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building
