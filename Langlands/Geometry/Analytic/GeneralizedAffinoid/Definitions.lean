import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Definitions
import Langlands.Geometry.Analytic.Affinoid

/-! # Actual finite positive-polyradius quotient presentations -/

noncomputable section

universe u

namespace Langlands.Analytic

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- A finite positive-polyradius Tate presentation with a closed ideal.
The carrier and its norm are constructed from this data below. -/
structure PresentedAffinoidAlgebra where
  arity : ℕ
  polyradius : PositivePolyradius (Fin arity)
  ideal : Ideal (GeneralizedTateAlgebra polyradius K)
  ideal_closed : IsClosed (ideal : Set (GeneralizedTateAlgebra polyradius K))

namespace PresentedAffinoidAlgebra

/-- The actual ring quotient by the displayed ideal. -/
def Carrier (A : PresentedAffinoidAlgebra K) :=
  GeneralizedTateAlgebra A.polyradius K ⧸ A.ideal

instance : CoeSort (PresentedAffinoidAlgebra K) (Type u) := ⟨Carrier K⟩

instance (A : PresentedAffinoidAlgebra K) : NormedCommRing A := by
  letI := A.ideal_closed
  exact inferInstanceAs
    (NormedCommRing (GeneralizedTateAlgebra A.polyradius K ⧸ A.ideal))

instance (A : PresentedAffinoidAlgebra K) : NormedAlgebra K A :=
  inferInstanceAs
    (NormedAlgebra K (GeneralizedTateAlgebra A.polyradius K ⧸ A.ideal))

instance (A : PresentedAffinoidAlgebra K) : IsUltrametricDist A :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a, rfl, ha⟩ := Ideal.Quotient.norm_mk_lt x hε
    obtain ⟨b, rfl, hb⟩ := Ideal.Quotient.norm_mk_lt y hε
    calc
      ‖Ideal.Quotient.mk A.ideal a + Ideal.Quotient.mk A.ideal b‖
          ≤ ‖a + b‖ := by
            rw [← map_add]
            exact Ideal.Quotient.norm_mk_le A.ideal _
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (‖Ideal.Quotient.mk A.ideal a‖ + ε)
          (‖Ideal.Quotient.mk A.ideal b‖ + ε) := max_le_max ha.le hb.le
      _ = _ := max_add_add_right _ _ _

/-- The bounded quotient map from the genuine weighted Tate algebra. -/
def presentationMap (A : PresentedAffinoidAlgebra K) :
    BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) A where
  toAlgHom := Ideal.Quotient.mkₐ K A.ideal
  bounded := ⟨1, zero_lt_one, fun a => by
    rw [one_mul]
    change ‖Ideal.Quotient.mk A.ideal a‖ ≤ ‖a‖
    exact Ideal.Quotient.norm_mk_le A.ideal a⟩

theorem norm_presentationMap_le (A : PresentedAffinoidAlgebra K)
    (f : GeneralizedTateAlgebra A.polyradius K) :
    ‖presentationMap K A f‖ ≤ ‖f‖ :=
  Ideal.Quotient.norm_mk_le A.ideal f

theorem presentationMap_surjective (A : PresentedAffinoidAlgebra K) :
    Function.Surjective (presentationMap K A) :=
  Ideal.Quotient.mkₐ_surjective K A.ideal

@[simp] theorem presentationMap_eq_zero_iff (A : PresentedAffinoidAlgebra K)
    (f : GeneralizedTateAlgebra A.polyradius K) :
    presentationMap K A f = 0 ↔ f ∈ A.ideal :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The norm is the quotient norm: representatives have arbitrarily small excess. -/
theorem exists_representative_norm_lt (A : PresentedAffinoidAlgebra K)
    (a : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, presentationMap K A f = a ∧ ‖f‖ < ‖a‖ + ε :=
  Ideal.Quotient.norm_mk_lt a hε

/-- The image of a presentation variable. -/
def coordinate (A : PresentedAffinoidAlgebra K) (i : Fin A.arity) : A :=
  presentationMap K A
    (GeneralizedTateAlgebra.monomial A.polyradius K (Finsupp.single i 1) 1)

theorem norm_coordinate_le (A : PresentedAffinoidAlgebra K) (i : Fin A.arity) :
    ‖coordinate K A i‖ ≤ A.polyradius i := by
  have h := norm_presentationMap_le K A
    (GeneralizedTateAlgebra.monomial A.polyradius K (Finsupp.single i 1) 1)
  simpa [coordinate, GeneralizedTateAlgebra.norm_monomial,
    PositivePolyradius.weight] using h

/-- The zero-ideal presentation of a closed polydisc with the specified radii. -/
def polydisc (n : ℕ) (r : PositivePolyradius (Fin n)) : PresentedAffinoidAlgebra K where
  arity := n
  polyradius := r
  ideal := ⊥
  ideal_closed := by
    change IsClosed ({0} : Set (GeneralizedTateAlgebra r K))
    exact isClosed_singleton

open CategoryTheory

instance : Category (PresentedAffinoidAlgebra K) where
  Hom A B := BoundedAlgHom K A B
  id A := BoundedAlgHom.id K A
  comp f g := g.comp f
  id_comp _ := BoundedAlgHom.ext fun _ => rfl
  comp_id _ := BoundedAlgHom.ext fun _ => rfl
  assoc _ _ _ := BoundedAlgHom.ext fun _ => rfl

end PresentedAffinoidAlgebra

open CategoryTheory

/-- The opposite category of the actual finite weighted quotient presentations.
Completeness and analytic-space structure are separate obligations. -/
abbrev PresentedAffinoidSpace := (PresentedAffinoidAlgebra K)ᵒᵖ

/-- The concrete spectrum functor on the constructed quotient normed algebras.
It is defined even before proving completeness over complete coefficients. -/
def affinoidSpectrumFunctor : PresentedAffinoidSpace K ⥤ TopCat.{u} where
  obj A := TopCat.of (BanachSpectrum A.unop)
  map f := TopCat.ofHom (BanachSpectrum.comapContinuous f.unop.toBoundedRingHom)
  map_id A := by
    apply TopCat.ext
    intro x
    apply BanachSpectrum.ext
    intro a
    rfl
  map_comp f g := by
    apply TopCat.ext
    intro x
    apply BanachSpectrum.ext
    intro a
    rfl

end Langlands.Analytic
