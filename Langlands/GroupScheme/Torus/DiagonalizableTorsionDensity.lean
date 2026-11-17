import Langlands.GroupScheme.Torus.TorsionDensityLattice

/-! # Torsion points are dense in a diagonalizable group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorsionDensity

/-- A closed immersion `z : Z → Spec A` is an isomorphism as soon as, for every nonzero `a ∈ A`,
some ring map `φ : A → B` with `φ a ≠ 0` has `Spec φ` factoring through `z`. -/
theorem isIso_of_forall_ne_zero {A : CommRingCat.{u}} {Z : Scheme.{u}} (z : Z ⟶ Spec A)
    (hz : IsClosedImmersion z)
    (h : ∀ a : A, a ≠ 0 → ∃ (B : CommRingCat.{u}) (φ : A ⟶ B) (y : Spec B ⟶ Z),
      y ≫ z = Spec.map φ ∧ φ a ≠ 0) : IsIso z := by
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  intro a₁ a₂ h12
  by_contra hne
  obtain ⟨B, φ, y, hy, hφ⟩ := h ((Scheme.ΓSpecIso A).hom (a₁ - a₂)) (by
    intro h0
    apply hne
    rw [← sub_eq_zero]
    have := congrArg (Scheme.ΓSpecIso A).inv h0
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this)
  apply hφ
  have h1 : (y ≫ z).appTop (a₁ - a₂) = 0 := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_sub, h12, sub_self, map_zero]
  rw [hy] at h1
  have h2 := congrArg (Scheme.ΓSpecIso B).hom h1
  rwa [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
    map_zero] at h2

variable (R : CommRingCat.{u}) {Λ : Type u} [AddCommGroup Λ]

/-- The quotient map `R[Λ] → R[Λ ⧸ nΛ]` of group algebras. -/
abbrev quotientMap (n : ℕ) :
    Diagonalizable.algebra R Λ ⟶ Diagonalizable.algebra R (Λ ⧸ multiples Λ n) :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R R (QuotientAddGroup.mk' (multiples Λ n)))

/-- The point of `D(Λ)` with values in `D(Λ ⧸ nΛ)` given by the quotient map of group
algebras. -/
abbrev quotientPoint (n : ℕ) :
    (algSpec R).obj (op (Diagonalizable.algebra R (Λ ⧸ multiples Λ n))) ⟶
      (Diagonalizable.groupScheme R Λ).toGrp.X :=
  (algSpec R).map (quotientMap R n).op

set_option backward.isDefEq.respectTransparency false in
/-- The quotient point `D(Λ ⧸ nΛ) → D(Λ)` is `n`-torsion. -/
theorem quotientPoint_pow (n : ℕ) : quotientPoint R (Λ := Λ) n ^ n = 1 := by
  apply (Corepresented.affinePointsEquiv (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) _).injective
  rw [map_pow, map_one, Corepresented.affinePointsEquiv_map]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change ((DFunLike.coe (F := Multiplicative Λ →* (AddMonoidAlgebra R (Λ ⧸ multiples Λ n))ˣ)
    ((Diagonalizable.corepresentation R Λ).homEquiv (quotientMap R n)) m :
      AddMonoidAlgebra R (Λ ⧸ multiples Λ n)) ^ n) = 1
  rw [Diagonalizable.corepresentation_homEquiv_apply]
  change (AddMonoidAlgebra.mapDomainAlgHom R R (QuotientAddGroup.mk' (multiples Λ n))
    (AddMonoidAlgebra.single m.toAdd 1)) ^ n = 1
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.one_def, ← map_nsmul]
  congr 1
  exact (QuotientAddGroup.eq_zero_iff _).mpr (nsmul_mem_multiples n m.toAdd)

/-- **Torsion density in `D(Λ)`.** Let `N` be such that every nonzero element of `R[Λ]` stays
nonzero in `R[Λ ⧸ nΛ]` for all large multiples `n` of `N`, and let `P` be a set of exponents
containing arbitrarily large multiples of `N`. A closed immersion into `D(Λ)` through which every
`n`-torsion point factors, for every `n ∈ P`, is an isomorphism. -/
theorem isIso_of_torsion_factors {N : ℕ}
    (hN : ∀ f : AddMonoidAlgebra R Λ, f ≠ 0 → ∃ M : ℕ, ∀ n : ℕ, N ∣ n → M < n →
      AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' (multiples Λ n)) f ≠ 0)
    (P : ℕ → Prop) (hP : ∀ M : ℕ, ∃ n, P n ∧ N ∣ n ∧ M < n)
    {Z : Scheme.{u}} (z : Z ⟶ (Diagonalizable.groupScheme R Λ).toGrp.X.left)
    [IsClosedImmersion z]
    (h : ∀ n, P n → ∀ (T : Over (Spec R)) (x : T ⟶ (Diagonalizable.groupScheme R Λ).toGrp.X),
      x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) :
    IsIso z := by
  refine isIso_of_forall_ne_zero (A := CommRingCat.of (AddMonoidAlgebra R Λ)) z ‹_› ?_
  intro f hf
  obtain ⟨M, hM⟩ := hN f hf
  obtain ⟨n, hPn, hNn, hMn⟩ := hP M
  obtain ⟨y, hy⟩ := h n hPn _ (quotientPoint R n) (quotientPoint_pow R n)
  refine ⟨CommRingCat.of (AddMonoidAlgebra R (Λ ⧸ multiples Λ n)),
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R R
      (QuotientAddGroup.mk' (multiples Λ n))).toRingHom, y, ?_, ?_⟩
  · exact hy
  · exact hM n hNn hMn

end Langlands.GroupScheme.TorsionDensity
