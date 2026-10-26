import Langlands.Geometry.Analytic.Affinoid
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.CategoryTheory.Widesubcategory

/-! # Algebraically finite étale bounded affinoid maps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

/-- The underlying ring map of this actual bounded algebra map is finite and
étale. Analytic domain restriction and Banach admissibility are separate issues. -/
def AlgebraicallyFiniteEtale (f : BoundedAlgHom K A B) : Prop :=
  f.toAlgHom.toRingHom.Finite ∧ f.toAlgHom.toRingHom.Etale

/-- The condition can equivalently be expressed by finite generation, flatness,
formal unramifiedness and finite presentation of the underlying ring map. -/
theorem algebraicallyFiniteEtale_iff (f : BoundedAlgHom K A B) :
    f.AlgebraicallyFiniteEtale ↔
      f.toAlgHom.toRingHom.Finite ∧ f.toAlgHom.toRingHom.Flat ∧
        f.toAlgHom.toRingHom.FormallyUnramified ∧
          f.toAlgHom.toRingHom.FinitePresentation := by
  rw [AlgebraicallyFiniteEtale, RingHom.Etale.iff_flat_and_formallyUnramified]

/-- Bijective bounded algebra maps satisfy the algebraic finite étale condition;
this assertion does not construct a bounded inverse. -/
theorem AlgebraicallyFiniteEtale.of_bijective (f : BoundedAlgHom K A B)
    (hf : Function.Bijective f) : f.AlgebraicallyFiniteEtale :=
  ⟨RingHom.Finite.of_surjective _ hf.2, RingHom.Etale.of_bijective hf⟩

/-- Identity bounded maps are algebraically finite étale. -/
theorem algebraicallyFiniteEtale_id :
    (BoundedAlgHom.id K A).AlgebraicallyFiniteEtale :=
  AlgebraicallyFiniteEtale.of_bijective _ Function.bijective_id

/-- Composition retains both boundedness and the algebraic finite étale
condition. -/
theorem AlgebraicallyFiniteEtale.comp {g : BoundedAlgHom K B C}
    {f : BoundedAlgHom K A B} (hg : g.AlgebraicallyFiniteEtale)
    (hf : f.AlgebraicallyFiniteEtale) : (g.comp f).AlgebraicallyFiniteEtale := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra B C := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := (g.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale A B := hf.2
  let : Algebra.Etale B C := hg.2
  exact Algebra.Etale.comp A B C

end BoundedAlgHom

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The algebraic finite étale condition on bounded maps between the actual
presented strict Tate quotients over `K`. -/
def algebraicallyFiniteEtaleProperty :
    MorphismProperty (PresentedStrictAffinoidAlgebra K) :=
  fun _ _ f => f.AlgebraicallyFiniteEtale

instance : (algebraicallyFiniteEtaleProperty K).IsMultiplicative where
  id_mem _ := BoundedAlgHom.algebraicallyFiniteEtale_id
  comp_mem _ _ hf hg := hg.comp hf

/-- The wide subcategory with all presented strict affinoid algebras as objects
and actual bounded algebraically finite étale maps as morphisms. -/
abbrev AlgebraicallyFiniteEtaleAffinoidAlgebra :=
  WideSubcategory (algebraicallyFiniteEtaleProperty K)

/-- Forget the ring-theoretic finite étale condition while retaining the
presented algebra and bounded map. -/
def algebraicallyFiniteEtaleInclusion :
    AlgebraicallyFiniteEtaleAffinoidAlgebra K ⥤ PresentedStrictAffinoidAlgebra K :=
  wideSubcategoryInclusion (algebraicallyFiniteEtaleProperty K)

instance : (algebraicallyFiniteEtaleInclusion K).Faithful :=
  inferInstanceAs (wideSubcategoryInclusion (algebraicallyFiniteEtaleProperty K)).Faithful

/-- The opposite category, oriented in the direction of spectrum maps. -/
abbrev AlgebraicallyFiniteEtaleAffinoidSpace :=
  (AlgebraicallyFiniteEtaleAffinoidAlgebra K)ᵒᵖ

/-- The underlying topological spaces and maps are the existing multiplicative
spectra and seminorm pullbacks of the actual quotient algebras. -/
def algebraicallyFiniteEtaleSpectrumFunctor [CompleteSpace K] :
    AlgebraicallyFiniteEtaleAffinoidSpace K ⥤ TopCat :=
  (algebraicallyFiniteEtaleInclusion K).op ⋙ strictAffinoidSpectrumFunctor K

@[simp]
theorem algebraicallyFiniteEtaleSpectrumFunctor_map_apply [CompleteSpace K]
    {X Y : AlgebraicallyFiniteEtaleAffinoidSpace K} (f : X ⟶ Y)
    (x : BanachSpectrum X.unop.obj) (a : Y.unop.obj) :
    BanachSpectrum.toMulRingSeminorm
      ((algebraicallyFiniteEtaleSpectrumFunctor K).map f x) a =
        x.toMulRingSeminorm (BoundedAlgHom.toAlgHom f.unop.hom a) :=
  rfl

end Langlands.Analytic
