import Langlands.Cohomology.SiteCech.LiftDescent
import Langlands.Cohomology.SiteCech.HomDimensionShift
import Langlands.Cohomology.SiteCech.InjectiveCoefficients
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Finite augmented test systems and coefficient lifting -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits

universe u v a b w

variable {D : Type u} [Category.{v} D] [Abelian D]
variable {ι : Type a} (B : ι → D)

/-- Exact augmented complexes with finite presentations by test objects and
local lifting of maps through short exact coefficient sequences. -/
structure FiniteCechSystem where
  Cover : ι → Type b
  complex : ∀ i, Cover i → ChainComplex D ℕ
  augmentation : ∀ i c, (complex i c).X 0 ⟶ B i
  augmentation_zero : ∀ i c, (complex i c).d 1 0 ≫ augmentation i c = 0
  augmentation_epi : ∀ i c, Epi (augmentation i c)
  augmentation_exact : ∀ i c,
    (ShortComplex.mk ((complex i c).d 1 0) (augmentation i c)
      (augmentation_zero i c)).Exact
  positive_exact : ∀ i c n, (complex i c).ExactAt (n + 1)
  termSize : ∀ i, Cover i → ℕ → ℕ
  termIndex : ∀ i c n, Fin (termSize i c n) → ι
  termIso : ∀ i c n, (complex i c).X n ≅ ∐ (fun j => B (termIndex i c n j))
  local_lift : ∀ (S : ShortComplex D), S.ShortExact →
    ∀ i (s : B i ⟶ S.X₃), ∃ (c : Cover i) (t : (complex i c).X 0 ⟶ S.X₂),
      t ≫ S.g = augmentation i c ≫ s

variable {B} (K : FiniteCechSystem.{u, v, a, b} B)
variable (R : Type w) [CommRing R] [Linear R D]

/-- Positive exactness of all the test-system Hom cochain complexes. -/
def FiniteCechSystem.HomAcyclic (F : D) : Prop :=
  ∀ i c n, ((K.complex i c).linearYonedaObj R F).ExactAt (n + 1)

/-- An injective coefficient is Hom-acyclic for an exact test system. -/
theorem FiniteCechSystem.homAcyclic_of_injective (I : D) [Injective I] :
    K.HomAcyclic R I :=
  fun i c n => exactAt_linearYonedaObj_of_injective R (K.complex i c) I n
    (K.positive_exact i c n)

/-- Hom-acyclicity corrects a local lift and descends it to the test object. -/
theorem FiniteCechSystem.exists_lift (S : ShortComplex D) (hS : S.ShortExact)
    (hF : K.HomAcyclic R S.X₁) (i : ι) (s : B i ⟶ S.X₃) :
    ∃ t : B i ⟶ S.X₂, t ≫ S.g = s := by
  obtain ⟨c, t, ht⟩ := K.local_lift S hS i s
  have := hS.mono_f
  have := K.augmentation_epi i c
  let l := liftByCechExactness (K.complex i c) (K.augmentation i c)
    (K.augmentation_zero i c) S hS.exact s t ht R (K.augmentation_exact i c) (hF i c 0)
  exact ⟨l.val, l.property⟩

/-- Finite coproduct presentations extend test-object lifting to every
chain term of every complex in the system. -/
theorem FiniteCechSystem.exists_term_lift (S : ShortComplex D) (hS : S.ShortExact)
    (hF : K.HomAcyclic R S.X₁) (i : ι) (c : K.Cover i) (n : ℕ)
    (x : (K.complex i c).X n ⟶ S.X₃) :
    ∃ y : (K.complex i c).X n ⟶ S.X₂, y ≫ S.g = x := by
  let e := K.termIso i c n
  have h := fun j => K.exists_lift R S hS hF (K.termIndex i c n j)
    (Sigma.ι (fun j => B (K.termIndex i c n j)) j ≫ e.inv ≫ x)
  choose t ht using h
  refine ⟨e.hom ≫ Sigma.desc t, ?_⟩
  have he : Sigma.desc t ≫ S.g = e.inv ≫ x := by
    apply Sigma.hom_ext
    intro j
    simpa only [Category.assoc, Sigma.ι_comp_desc_assoc] using ht j
  rw [Category.assoc, he, e.hom_inv_id_assoc]

/-- Positive Hom exactness is closed under a short exact quotient whose
middle coefficient is injective. -/
theorem FiniteCechSystem.homAcyclic_quotient (S : ShortComplex D)
    (hS : S.ShortExact) [Injective S.X₂] (hF : K.HomAcyclic R S.X₁) :
    K.HomAcyclic R S.X₃ := by
  have := hS.mono_f
  intro i c
  exact exactAt_linearYonedaObj_quotient_all R (K.complex i c) S hS.exact
    (fun n x => K.exists_term_lift R S hS hF i c (n + 1) x)
    (hF i c) (K.homAcyclic_of_injective R S.X₂ i c)

end Langlands.Cohomology.SiteCech
