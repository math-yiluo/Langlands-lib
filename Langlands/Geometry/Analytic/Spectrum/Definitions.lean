import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.Ideal.Prime

/-!
# Multiplicative spectra of normed commutative rings

This is the concrete topological spectrum underlying the later affinoid construction.
It does not yet supply a structure sheaf, an affinoid presentation, or an analytic site.
-/

universe u v w

namespace Langlands.Analytic

/-- A bounded unital ring homomorphism, with the usual positive linear norm bound. -/
structure BoundedRingHom (A : Type u) (B : Type v)
    [NormedCommRing A] [NormedCommRing B] extends A →+* B where
  bounded : toRingHom.IsBounded

namespace BoundedRingHom

variable {A : Type u} {B : Type v} {C : Type w}
  [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]

instance : CoeFun (BoundedRingHom A B) (fun _ => A → B) :=
  ⟨fun f => f.toRingHom⟩

@[ext]
theorem ext {f g : BoundedRingHom A B} (h : ∀ a, f a = g a) : f = g := by
  cases f
  cases g
  congr 1
  exact RingHom.ext h

/-- The bounded identity homomorphism. -/
def id (A : Type u) [NormedCommRing A] : BoundedRingHom A A where
  toRingHom := RingHom.id A
  bounded := ⟨1, zero_lt_one, fun x => by simp⟩

/-- Composition of bounded homomorphisms. -/
def comp (g : BoundedRingHom B C) (f : BoundedRingHom A B) : BoundedRingHom A C where
  toRingHom := g.toRingHom.comp f.toRingHom
  bounded := by
    obtain ⟨Cg, hCg, hg⟩ := g.bounded
    obtain ⟨Cf, hCf, hf⟩ := f.bounded
    refine ⟨Cg * Cf, mul_pos hCg hCf, fun x => ?_⟩
    exact (hg (f x)).trans ((mul_le_mul_of_nonneg_left (hf x) hCg.le).trans_eq
      (mul_assoc Cg Cf ‖x‖).symm)

/-- The scalar map of a normed algebra is bounded, without requiring a separately
normalized ring norm on the algebra. -/
def scalarHom (K : Type u) (A : Type v) [NormedField K] [NormedCommRing A]
    [NormedAlgebra K A] : BoundedRingHom K A where
  toRingHom := algebraMap K A
  bounded := by
    refine ⟨max 1 ‖(1 : A)‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun c => ?_⟩
    rw [norm_algebraMap, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg c)

end BoundedRingHom

/-- The bounded multiplicative spectrum. The normalization `x 1 = 1` is part of
`MulRingSeminorm`; the constant-one bound is equivalent to boundedness. -/
structure BanachSpectrum (A : Type u) [NormedCommRing A] extends MulRingSeminorm A where
  le_norm : ∀ a : A, toMulRingSeminorm a ≤ ‖a‖

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]

instance : CoeFun (BanachSpectrum A) (fun _ => A → ℝ) :=
  ⟨fun x => x.toMulRingSeminorm⟩

@[ext]
theorem ext {x y : BanachSpectrum A} (h : ∀ a, x a = y a) : x = y := by
  cases x
  cases y
  congr 1
  exact MulRingSeminorm.ext h

/-- The topology of pointwise convergence of multiplicative seminorms. -/
instance : TopologicalSpace (BanachSpectrum A) :=
  TopologicalSpace.induced (fun x : BanachSpectrum A => (x : A → ℝ)) inferInstance

private theorem continuous_evaluation (a : A) :
    Continuous (fun x : BanachSpectrum A => x a) :=
  (continuous_apply a).comp continuous_induced_dom

/-- Evaluation of an algebra element as a continuous real-valued function. -/
def evaluation (a : A) : C(BanachSpectrum A, ℝ) :=
  ⟨fun x => x a, continuous_evaluation a⟩

/-- A bounded multiplicative seminorm defines a point: taking powers removes the
arbitrary positive bound constant. -/
def ofBounded (x : MulRingSeminorm A)
    (hx : ∃ C : ℝ, 0 < C ∧ ∀ a, x a ≤ C * ‖a‖) : BanachSpectrum A where
  toMulRingSeminorm := x
  le_norm a := contraction_of_isPowMul_of_boundedWrt
    (SeminormedRing.toRingSeminorm A) (fun a n _ => map_pow x a n)
    (f := RingHom.id A) hx a

/-- The point of the spectrum of a normed field defined by its given norm. -/
def fieldPoint (K : Type u) [NormedField K] : BanachSpectrum K where
  toMulRingSeminorm := (NormedField.toMulRingNorm K).toMulRingSeminorm
  le_norm _ := le_rfl

variable {B : Type v} [NormedCommRing B]

/-- Pullback of a bounded multiplicative seminorm along a bounded ring map. -/
def comap (f : BoundedRingHom A B) (x : BanachSpectrum B) : BanachSpectrum A :=
  ofBounded
    { toFun := fun a => x (f a)
      map_zero' := by simp [map_zero]
      map_one' := by simp [map_one]
      map_mul' := fun a b => by
        change x.toMulRingSeminorm (f.toRingHom (a * b)) = _
        rw [map_mul, map_mul]
      add_le' := fun a b => by
        change x.toMulRingSeminorm (f.toRingHom (a + b)) ≤ _
        rw [map_add]
        exact map_add_le_add x.toMulRingSeminorm _ _
      neg' := fun a => by
        change x.toMulRingSeminorm (f.toRingHom (-a)) = _
        rw [map_neg, map_neg_eq_map] }
    (by
      obtain ⟨C, hC, hf⟩ := f.bounded
      exact ⟨C, hC, fun a => (x.le_norm (f a)).trans (hf a)⟩)

/-- The contravariant continuous map on spectra. -/
def comapContinuous (f : BoundedRingHom A B) : C(BanachSpectrum B, BanachSpectrum A) where
  toFun := comap f
  continuous_toFun := continuous_induced_rng.mpr
    (continuous_pi fun a => continuous_evaluation (f a))

/-- The actual kernel ideal of a multiplicative seminorm. -/
def kernel (x : BanachSpectrum A) : Ideal A where
  carrier := {a | x a = 0}
  zero_mem' := map_zero x.toMulRingSeminorm
  add_mem' := by
    intro a b ha hb
    change x.toMulRingSeminorm a = 0 at ha
    change x.toMulRingSeminorm b = 0 at hb
    apply le_antisymm _ (apply_nonneg x.toMulRingSeminorm _)
    simpa only [ha, hb, add_zero] using map_add_le_add x.toMulRingSeminorm a b
  smul_mem' := by
    intro a b hb
    change x.toMulRingSeminorm (a * b) = 0
    rw [map_mul, hb, mul_zero]

/-- An inequality locus, specializing to a Laurent locus for finite tuples and
positive radii. Representability by an affinoid algebra is a separate construction;
this definition only names its subset of the spectrum. -/
def laurentLocus {ι κ : Type*} (f : ι → A) (r : ι → ℝ) (g : κ → A) (s : κ → ℝ) :
    Set (BanachSpectrum A) :=
  {x | (∀ i, x (f i) ≤ r i) ∧ ∀ j, s j ≤ x (g j)}

end BanachSpectrum

/-- The category of actual complete normed commutative rings and bounded unital
ring maps. No analytic-space, affinoid, or cohomological axioms are included. -/
structure BanachRing where
  carrier : Type u
  [normedCommRing : NormedCommRing carrier]
  [completeSpace : CompleteSpace carrier]

namespace BanachRing

instance : CoeSort BanachRing (Type u) := ⟨carrier⟩
attribute [instance] normedCommRing completeSpace

open CategoryTheory

instance : Category BanachRing where
  Hom A B := BoundedRingHom A B
  id A := BoundedRingHom.id A
  comp f g := g.comp f
  id_comp _f := BoundedRingHom.ext fun _ => rfl
  comp_id _f := BoundedRingHom.ext fun _ => rfl
  assoc _f _g _h := BoundedRingHom.ext fun _ => rfl

/-- Bundle an existing complete normed commutative ring. -/
def of (A : Type u) [NormedCommRing A] [CompleteSpace A] : BanachRing :=
  ⟨A⟩

end BanachRing

open CategoryTheory in
/-- The concrete contravariant spectrum functor on commutative Banach rings. -/
def banachSpectrumFunctor : BanachRing.{u}ᵒᵖ ⥤ TopCat.{u} where
  obj A := TopCat.of (BanachSpectrum A.unop)
  map f := TopCat.ofHom (BanachSpectrum.comapContinuous f.unop)
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
