import Langlands.GroupScheme.SmoothIsomorphismLocus
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Detecting isomorphisms of supplied homomorphisms modulo nil ideals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every field-valued point factors through a quotient by a nil ideal. -/
theorem fieldPoint_factors_nilIdeal
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      y ≫ algebraBaseMap R (R ⧸ I) = x := by
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective x
  let : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime φ.hom
  have hz : ∀ r : R, r ∈ I → φ.hom r = 0 := fun r hr =>
    (hI.trans (nilradical_le_prime (RingHom.ker φ.hom))) hr
  let ψ : R ⧸ I →+* k := Ideal.Quotient.lift I φ.hom hz
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  change Spec.map (CommRingCat.ofHom ψ) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map φ
  rw [← Spec.map_comp]
  congr 1

/-- A supplied homomorphism from a smooth group to a locally finite type group
is invertible if its pullback modulo a nil ideal is invertible. -/
theorem isIso_of_nilIdeal_baseChange
    (R : Type u) [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H)
    (hf : IsIso ((baseChange (algebraBaseMap R (R ⧸ I))).map f)) :
    IsIso f := by
  let := hf
  apply SmoothIsomorphismLocus.isIso_of_group_residueField_fibres
  intro s
  obtain ⟨y, hy⟩ := fieldPoint_factors_nilIdeal R I hI _
    ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  have h : IsIso ((baseChange (y ≫ algebraBaseMap R (R ⧸ I))).map f) :=
    (TorusIsomorphismLocus.isIso_comp_baseChange_iff
      (algebraBaseMap R (R ⧸ I)) y f).mpr inferInstance
  rwa [hy] at h

/-- The isomorphism test for an already supplied homomorphism, without a
nilpotence exponent or locality assumption. -/
def NilIdealHomIsomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R), I ≤ nilradical R →
    ∀ (G H : GroupScheme (Spec (CommRingCat.of R)))
      [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H),
      IsIso ((baseChange (algebraBaseMap R (R ⧸ I))).map f) → IsIso f

/-- Isomorphisms of supplied smooth-source homomorphisms are detected modulo
arbitrary nil ideals. -/
theorem nilIdealHomIsomorphism : NilIdealHomIsomorphismStatement.{u} := by
  intro R _ I hI G H _ _ f hf
  exact isIso_of_nilIdeal_baseChange R I hI f hf

end Langlands.GroupScheme
