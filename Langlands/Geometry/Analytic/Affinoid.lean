import Langlands.Geometry.Analytic.TateAlgebra
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Analysis.Normed.Group.Quotient

/-! # Presented strict affinoid algebras and their spectra -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

/-- A bounded algebra homomorphism, with an explicit positive norm bound. -/
structure BoundedAlgHom (K : Type u) (A : Type v) (B : Type w)
    [NormedField K] [NormedCommRing A] [NormedCommRing B]
    [Algebra K A] [Algebra K B] extends A →ₐ[K] B where
  bounded : toAlgHom.toRingHom.IsBounded

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

instance : CoeFun (BoundedAlgHom K A B) (fun _ => A → B) := ⟨fun f => f.toAlgHom⟩

@[ext]
theorem ext {f g : BoundedAlgHom K A B} (h : ∀ a, f a = g a) : f = g := by
  cases f
  cases g
  congr 1
  exact AlgHom.ext h

/-- Forget scalar compatibility, retaining the actual bounded ring map. -/
def toBoundedRingHom (f : BoundedAlgHom K A B) : BoundedRingHom A B :=
  ⟨f.toAlgHom.toRingHom, f.bounded⟩

/-- The bounded identity algebra map. -/
def id (K : Type u) (A : Type v) [NormedField K] [NormedCommRing A] [Algebra K A] :
    BoundedAlgHom K A A where
  toAlgHom := AlgHom.id K A
  bounded := ⟨1, zero_lt_one, fun a => by simp⟩

/-- Composition multiplies the positive bounds. -/
def comp (g : BoundedAlgHom K B C) (f : BoundedAlgHom K A B) :
    BoundedAlgHom K A C where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  bounded := (g.toBoundedRingHom.comp f.toBoundedRingHom).bounded

end BoundedAlgHom

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- A strict affinoid algebra with a chosen finite Tate presentation.
Its carrier is constructed as the actual quotient by the displayed closed ideal.
The number `arity` counts presentation variables, not Krull dimension. -/
structure PresentedStrictAffinoidAlgebra where
  arity : ℕ
  ideal : Ideal (StrictTateAlgebra (Fin arity) K)
  ideal_closed : IsClosed (ideal : Set (StrictTateAlgebra (Fin arity) K))

namespace PresentedStrictAffinoidAlgebra

/-- The actual quotient algebra, with its quotient norm. -/
def Carrier (A : PresentedStrictAffinoidAlgebra K) :=
  StrictTateAlgebra (Fin A.arity) K ⧸ A.ideal

instance : CoeSort (PresentedStrictAffinoidAlgebra K) (Type u) := ⟨Carrier K⟩

instance (A : PresentedStrictAffinoidAlgebra K) : NormedCommRing A := by
  letI := A.ideal_closed
  exact inferInstanceAs
    (NormedCommRing (StrictTateAlgebra (Fin A.arity) K ⧸ A.ideal))

instance [CompleteSpace K] (A : PresentedStrictAffinoidAlgebra K) : CompleteSpace A :=
  inferInstanceAs (CompleteSpace (StrictTateAlgebra (Fin A.arity) K ⧸ A.ideal))

instance (A : PresentedStrictAffinoidAlgebra K) : NormedAlgebra K A :=
  inferInstanceAs (NormedAlgebra K (StrictTateAlgebra (Fin A.arity) K ⧸ A.ideal))

instance (A : PresentedStrictAffinoidAlgebra K) : IsUltrametricDist A :=
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

/-- The bounded quotient map from the genuine finite Tate algebra. -/
def presentationMap (A : PresentedStrictAffinoidAlgebra K) :
    BoundedAlgHom K (StrictTateAlgebra (Fin A.arity) K) A where
  toAlgHom := Ideal.Quotient.mkₐ K A.ideal
  bounded := ⟨1, zero_lt_one, fun a => by
    rw [one_mul]
    change ‖Ideal.Quotient.mk A.ideal a‖ ≤ ‖a‖
    exact Ideal.Quotient.norm_mk_le A.ideal a⟩

/-- Every quotient element has a power-series representative. -/
theorem presentationMap_surjective (A : PresentedStrictAffinoidAlgebra K) :
    Function.Surjective (presentationMap K A) :=
  Ideal.Quotient.mkₐ_surjective K A.ideal

/-- The quotient norm admits representatives with arbitrarily small excess.
This witnesses the quotient Banach topology directly. -/
theorem exists_representative_norm_lt (A : PresentedStrictAffinoidAlgebra K)
    (a : A) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, presentationMap K A f = a ∧ ‖f‖ < ‖a‖ + ε :=
  Ideal.Quotient.norm_mk_lt a hε

/-- The presentation with zero ideal gives the closed unit polydisc algebra. -/
def polydisc (n : ℕ) : PresentedStrictAffinoidAlgebra K where
  arity := n
  ideal := ⊥
  ideal_closed := by
    change IsClosed ({0} : Set (StrictTateAlgebra (Fin n) K))
    exact isClosed_singleton

open CategoryTheory

instance : Category (PresentedStrictAffinoidAlgebra K) where
  Hom A B := BoundedAlgHom K A B
  id A := BoundedAlgHom.id K A
  comp f g := g.comp f
  id_comp _ := BoundedAlgHom.ext fun _ => rfl
  comp_id _ := BoundedAlgHom.ext fun _ => rfl
  assoc _ _ _ := BoundedAlgHom.ext fun _ => rfl

/-- Forget a finite presentation while retaining the actual Banach algebra. -/
def toBanachRing [CompleteSpace K] : PresentedStrictAffinoidAlgebra K ⥤ BanachRing where
  obj A := BanachRing.of A
  map f := f.toBoundedRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

end PresentedStrictAffinoidAlgebra

open CategoryTheory

/-- Presented strict affinoid spaces form the opposite of the bounded-algebra
category. Their underlying points and topology are supplied by the spectrum
functor below, not by arbitrary space data. -/
abbrev PresentedStrictAffinoidSpace := (PresentedStrictAffinoidAlgebra K)ᵒᵖ

/-- The actual topological space underlying each presented strict affinoid. -/
def strictAffinoidSpectrumFunctor [CompleteSpace K] : PresentedStrictAffinoidSpace K ⥤ TopCat :=
  (PresentedStrictAffinoidAlgebra.toBanachRing K).op ⋙ banachSpectrumFunctor

end Langlands.Analytic
