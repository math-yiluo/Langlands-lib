import Langlands.Algebra.FiberZeroConstructibility

/-! # Equality of actual residue-fibre algebra maps -/

noncomputable section

universe u v w

open TensorProduct Set Topology

namespace Langlands.Algebra.FiberMapEquality

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]

/-- The actual scalar extension of an algebra map. -/
def baseChangeMap (S : Type*) [CommRing S] [Algebra R S] (f : A →ₐ[R] B) :
    S ⊗[R] A →ₐ[S] S ⊗[R] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) f

@[simp]
theorem baseChangeMap_tmul (S : Type*) [CommRing S] [Algebra R S]
    (f : A →ₐ[R] B) (s : S) (a : A) :
    baseChangeMap S f (s ⊗ₜ[R] a) = s ⊗ₜ[R] f a := rfl

/-- Algebra maps out of a scalar extension agree exactly when they agree on
all original algebra elements. -/
theorem tensorMap_eq_iff (S : Type*) [CommRing S] [Algebra R S]
    {C : Type*} [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
    (f g : S ⊗[R] A →ₐ[S] C) :
    f = g ↔ ∀ a, f ((1 : S) ⊗ₜ[R] a) = g ((1 : S) ⊗ₜ[R] a) := by
  constructor
  · rintro rfl a
    rfl
  · intro h
    apply Algebra.TensorProduct.ext
    · ext
    · exact AlgHom.ext h

theorem baseChangeMap_eq_iff (S : Type*) [CommRing S] [Algebra R S]
    (f g : A →ₐ[R] B) :
    baseChangeMap S f = baseChangeMap S g ↔
      ∀ a, (1 : S) ⊗ₜ[R] f a = (1 : S) ⊗ₜ[R] g a :=
  tensorMap_eq_iff S _ _

/-- The primes at which the two full residue-field algebra maps are equal. -/
def fiberMapEqualityLocus (f g : A →ₐ[R] B) : Set (PrimeSpectrum R) :=
  {p | baseChangeMap p.asIdeal.ResidueField f = baseChangeMap p.asIdeal.ResidueField g}

theorem mem_fiberMapEqualityLocus_iff (f g : A →ₐ[R] B) (p : PrimeSpectrum R) :
    p ∈ fiberMapEqualityLocus f g ↔
      ∀ a, (1 : p.asIdeal.ResidueField) ⊗ₜ[R] (f a - g a) = 0 := by
  rw [fiberMapEqualityLocus, Set.mem_ofPred_eq, baseChangeMap_eq_iff]
  simp only [tmul_sub, sub_eq_zero]

/-- A generating set suffices to check equality in every full fibre algebra. -/
theorem fiberMapEqualityLocus_eq_biInter (f g : A →ₐ[R] B)
    (s : Set A) (hs : Algebra.adjoin R s = ⊤) :
    fiberMapEqualityLocus f g =
      ⋂ a ∈ s, FiberZeroConstructibility.fiberZeroLocus (R := R) (f a - g a) := by
  ext p
  rw [mem_fiberMapEqualityLocus_iff]
  simp only [Set.mem_iInter, FiberZeroConstructibility.fiberZeroLocus, Set.mem_ofPred_eq]
  constructor
  · exact fun h a _ => h a
  · intro h
    have he :
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.ResidueField ⊗[R] B).comp f =
          Algebra.TensorProduct.includeRight.comp g := by
      apply AlgHom.ext_of_adjoin_eq_top hs
      intro a ha
      apply sub_eq_zero.mp
      simpa only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
        tmul_sub] using h a ha
    intro a
    simpa only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      tmul_sub, sub_eq_zero] using AlgHom.congr_fun he a

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the actual fibre maps is preserved and reflected by arbitrary
base change at the contracted prime. -/
theorem mem_fiberMapEqualityLocus_baseChange_iff
    {S : Type*} [CommRing S] [Algebra R S] (f g : A →ₐ[R] B)
    (q : PrimeSpectrum S) :
    q ∈ fiberMapEqualityLocus (baseChangeMap S f) (baseChangeMap S g) ↔
      PrimeSpectrum.comap (algebraMap R S) q ∈ fiberMapEqualityLocus f g := by
  let K := q.asIdeal.ResidueField
  let F : S ⊗[R] A →ₐ[S] K ⊗[S] (S ⊗[R] B) :=
    Algebra.TensorProduct.includeRight.comp (baseChangeMap S f)
  let G : S ⊗[R] A →ₐ[S] K ⊗[S] (S ⊗[R] B) :=
    Algebra.TensorProduct.includeRight.comp (baseChangeMap S g)
  change baseChangeMap K (baseChangeMap S f) = baseChangeMap K (baseChangeMap S g) ↔ _
  rw [baseChangeMap_eq_iff]
  change (∀ x, F x = G x) ↔ _
  rw [← AlgHom.ext_iff, tensorMap_eq_iff S F G, mem_fiberMapEqualityLocus_iff]
  apply forall_congr'
  intro a
  simpa only [F, G, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    baseChangeMap_tmul, tmul_sub, sub_eq_zero] using
    FiberZeroConstructibility.mem_fiberZeroLocus_baseChange_iff (R := R) (f a - g a) q

/-- Scalar extension pulls the equality locus back to its full inverse image. -/
theorem fiberMapEqualityLocus_baseChange
    {S : Type*} [CommRing S] [Algebra R S] (f g : A →ₐ[R] B) :
    fiberMapEqualityLocus (baseChangeMap S f) (baseChangeMap S g) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' fiberMapEqualityLocus f g := by
  ext q
  exact mem_fiberMapEqualityLocus_baseChange_iff f g q

/-- The actual fibre equality locus is constructible for finite type algebras
on a noetherian base. -/
theorem isConstructible_fiberMapEqualityLocus
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (f g : A →ₐ[R] B) : IsConstructible (fiberMapEqualityLocus f g) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  rw [fiberMapEqualityLocus_eq_biInter f g (s : Set A) hs]
  exact IsConstructible.biInter s.finite_toSet fun a _ =>
    FiberZeroConstructibility.isConstructible_fiberZeroLocus (f a - g a)

end Langlands.Algebra.FiberMapEquality
