import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProduct
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Finite product coverings by actual full affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {U : Domain K A} {V : Domain K B}

/-- The products of the original members cover the actual product domain.
The maps are actual product restrictions, and either index set may be empty. -/
def product (c : FiniteCover U) (d : FiniteCover V) : FiniteCover (U.product V) :=
  ofFintype
    (fun ij : Fin c.size × Fin d.size => (c.obj ij.1).product (d.obj ij.2))
    (fun ij => Domain.productRestriction (c.map ij.1) (d.map ij.2))
    (by
      intro x hx
      obtain ⟨i, hi⟩ := c.covers
        (BanachSpectrum.comap (AffinoidCoproduct.leftMap K A B).toBoundedRingHom x) hx.1
      obtain ⟨j, hj⟩ := d.covers
        (BanachSpectrum.comap (AffinoidCoproduct.rightMap K A B).toBoundedRingHom x) hx.2
      exact ⟨(i, j), hi, hj⟩)

@[simp]
theorem product_size (c : FiniteCover U) (d : FiniteCover V) :
    (c.product d).size = c.size * d.size := by
  simp [product, ofFintype, Fintype.card_prod]

/-- The actual finite ordinal indexing is equivalent to the pair of input indices. -/
def productIndexEquiv (c : FiniteCover U) (d : FiniteCover V) :
    Fin (c.product d).size ≃ Fin c.size × Fin d.size :=
  (Fintype.equivFin (Fin c.size × Fin d.size)).symm

/-- Select the product component belonging to two specified original members. -/
def productIndex (c : FiniteCover U) (d : FiniteCover V)
    (i : Fin c.size) (j : Fin d.size) : Fin (c.product d).size :=
  Fintype.equivFin (Fin c.size × Fin d.size) (i, j)

@[simp]
theorem productIndexEquiv_index (c : FiniteCover U) (d : FiniteCover V)
    (i : Fin c.size) (j : Fin d.size) :
    c.productIndexEquiv d (c.productIndex d i j) = (i, j) :=
  (Fintype.equivFin (Fin c.size × Fin d.size)).symm_apply_apply (i, j)

@[simp]
theorem product_obj (c : FiniteCover U) (d : FiniteCover V)
    (k : Fin (c.product d).size) :
    (c.product d).obj k =
      (c.obj (c.productIndexEquiv d k).1).product (d.obj (c.productIndexEquiv d k).2) := rfl

@[simp]
theorem product_map (c : FiniteCover U) (d : FiniteCover V)
    (k : Fin (c.product d).size) :
    (c.product d).map k = Domain.productRestriction
      (c.map (c.productIndexEquiv d k).1) (d.map (c.productIndexEquiv d k).2) := rfl

@[simp]
theorem product_obj_productIndex (c : FiniteCover U) (d : FiniteCover V)
    (i : Fin c.size) (j : Fin d.size) :
    (c.product d).obj (c.productIndex d i j) = (c.obj i).product (d.obj j) := by
  rw [product_obj, productIndexEquiv_index]

/-- Covers of both entire factors give a cover of the entire actual coproduct.
The members are precisely the preceding product domains, with their actual
full-domain inclusions into the whole spectrum. -/
def coproductCover (c : FiniteCover (Domain.whole K A))
    (d : FiniteCover (Domain.whole K B)) :
    FiniteCover (Domain.whole K (AffinoidCoproduct.algebra K A B)) where
  size := (c.product d).size
  obj := (c.product d).obj
  map i := Domain.inclusionOfSubset ((c.product d).obj i)
    (Domain.whole K (AffinoidCoproduct.algebra K A B)) (Set.subset_univ _)
  covers x _ := (c.product d).covers x ⟨Set.mem_univ _, Set.mem_univ _⟩

@[simp]
theorem coproductCover_size (c : FiniteCover (Domain.whole K A))
    (d : FiniteCover (Domain.whole K B)) :
    (c.coproductCover d).size = c.size * d.size :=
  c.product_size d

@[simp]
theorem coproductCover_obj (c : FiniteCover (Domain.whole K A))
    (d : FiniteCover (Domain.whole K B)) (k : Fin (c.coproductCover d).size) :
    (c.coproductCover d).obj k =
      (c.obj (c.productIndexEquiv d k).1).product (d.obj (c.productIndexEquiv d k).2) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
