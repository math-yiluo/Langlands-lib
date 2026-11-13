import Langlands.Geometry.FormalGroup.KernelTransport

/-! # Scalar divisibility and finite height over a nilpotent base -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

@[simp]
theorem scalarHom_one (M : ModuleLaw O R σ) : M.scalarHom 1 = Hom.id M := by
  simp only [scalarHom, one_smul]

/-- Multiplication of scalars is composition of the actual scalar homomorphisms. -/
theorem scalarHom_mul (M : ModuleLaw O R σ) (a b : O) :
    M.scalarHom (a * b) = (M.scalarHom a).comp (M.scalarHom b) := by
  simp only [scalarHom, Hom.smul_comp, Hom.comp_smul, Hom.id_comp, mul_smul]
  exact smul_comm a b (Hom.id M)

/-- Every O-linear formal homomorphism commutes with scalar homomorphisms. -/
theorem Hom.comp_scalarHom (f : Hom M N) (a : O) :
    f.comp (M.scalarHom a) = (N.scalarHom a).comp f := by
  simp only [scalarHom, Hom.comp_smul, Hom.smul_comp, Hom.comp_id, Hom.id_comp]

namespace Hom

/-- Successive affine fppf lifts give a lift through a composite. -/
theorem IsFppfLocallySurjective.comp {f : Hom M N} {g : Hom N P}
    (hg : g.IsFppfLocallySurjective) (hf : f.IsFppfLocallySurjective) :
    (g.comp f).IsFppfLocallySurjective := by
  intro A y
  obtain ⟨B, φ, hφff, hφfp, z, hz⟩ := hg A y
  obtain ⟨C, ψ, hψff, hψfp, x, hx⟩ := hf B z
  refine ⟨C, φ ≫ ψ, ?_, ?_, x, ?_⟩
  · exact RingHom.FaithfullyFlat.stableUnderComposition
      φ.hom.toRingHom ψ.hom.toRingHom hφff hψff
  · exact hψfp.comp hφfp
  · rw [onAlgebraPoints_comp, hx, ← onAlgebraPoints_natural, hz]
    exact (P.algebraMapPoints_comp φ.hom ψ.hom y).symm

end Hom

/-- Every actual point is annihilated by some power of the distinguished scalar. -/
def IsPiPowerTorsion (M : ModuleLaw O R σ) (π : O) : Prop :=
  ∀ (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A), ∃ n : ℕ, (π ^ n) • x = 0

/-- The affine scalar-divisibility condition on a base where π is nilpotent.
It requires actual torsion, affine fppf lifting, and represented finite kernels. -/
def IsPiDivisible (M : ModuleLaw O R σ) (π : O) : Prop :=
  IsNilpotent (algebraMap O R π) ∧ M.IsPiPowerTorsion π ∧
    (M.scalarHom π).IsFppfLocallySurjective ∧
      ∀ n : ℕ, (M.scalarHom (π ^ n)).HasFiniteLocallyFreeKernel

/-- Finite O-height h is the actual rank q^(n*h) of every scalar-power kernel. -/
def HasPiHeight (M : ModuleLaw O R σ) (π : O) (q h : ℕ) : Prop :=
  M.IsPiDivisible π ∧ ∀ n : ℕ, (M.scalarHom (π ^ n)).HasKernelRank (q ^ (n * h))

namespace IsPiDivisible

variable {π : O}

theorem base_nilpotent (hM : M.IsPiDivisible π) :
    IsNilpotent (algebraMap O R π) := hM.1

theorem torsion (hM : M.IsPiDivisible π) : M.IsPiPowerTorsion π := hM.2.1

theorem scalar_locallySurjective (hM : M.IsPiDivisible π) :
    (M.scalarHom π).IsFppfLocallySurjective := hM.2.2.1

theorem scalarPower_finiteKernel (hM : M.IsPiDivisible π) (n : ℕ) :
    (M.scalarHom (π ^ n)).HasFiniteLocallyFreeKernel := hM.2.2.2 n

/-- Iterating the scalar lift supplies affine lifts for every scalar power. -/
theorem scalarPower_locallySurjective (hM : M.IsPiDivisible π) (n : ℕ) :
    (M.scalarHom (π ^ n)).IsFppfLocallySurjective := by
  induction n with
  | zero =>
    rw [pow_zero, scalarHom_one]
    exact (Iso.refl M).isFppfLocallySurjective
  | succ n ih =>
    rw [pow_succ, scalarHom_mul]
    exact ih.comp hM.scalar_locallySurjective

theorem scalarPower_isIsogeny (hM : M.IsPiDivisible π) (n : ℕ) :
    (M.scalarHom (π ^ n)).IsIsogeny :=
  ⟨hM.scalarPower_locallySurjective n, hM.scalarPower_finiteKernel n⟩

end IsPiDivisible

namespace HasPiHeight

variable {π : O} {q h k : ℕ}

theorem piDivisible (hM : M.HasPiHeight π q h) : M.IsPiDivisible π := hM.1

theorem scalarPower_rank (hM : M.HasPiHeight π q h) (n : ℕ) :
    (M.scalarHom (π ^ n)).HasKernelRank (q ^ (n * h)) := hM.2 n

theorem scalarPower_height (hM : M.HasPiHeight π q h) (n : ℕ) :
    (M.scalarHom (π ^ n)).HasHeight q (n * h) :=
  ⟨hM.1.scalarPower_isIsogeny n, hM.2 n⟩

theorem scalar_height (hM : M.HasPiHeight π q h) :
    (M.scalarHom π).HasHeight q h := by
  simpa only [pow_one, one_mul] using hM.scalarPower_height 1

/-- Height is determined by the actual rank of the π-kernel. -/
theorem unique [Nontrivial R] (hq : 2 ≤ q)
    (hM : M.HasPiHeight π q h) (hM' : M.HasPiHeight π q k) : h = k :=
  hM.scalar_height.unique hq hM'.scalar_height

end HasPiHeight

namespace Iso

variable (e : Iso M N) (π : O)

include e

/-- Pointwise scalar-power torsion is invariant under actual O-linear isomorphisms. -/
theorem isPiPowerTorsion (hM : M.IsPiPowerTorsion π) : N.IsPiPowerTorsion π := by
  intro A y
  obtain ⟨n, hn⟩ := hM A (e.inv.onAlgebraPoints y)
  refine ⟨n, ?_⟩
  have h := congrArg e.hom.onAlgebraPoints hn
  simpa only [map_smul, map_zero, onAlgebraPoints_hom_inv] using h

/-- The scalar square is a commuting isomorphism of actual arrows. -/
theorem scalar_square (a : O) :
    (N.scalarHom a).comp e.hom = e.hom.comp (M.scalarHom a) :=
  (e.hom.comp_scalarHom a).symm

theorem isPiDivisible (hM : M.IsPiDivisible π) : N.IsPiDivisible π := by
  refine ⟨hM.base_nilpotent, e.isPiPowerTorsion π hM.torsion,
    Hom.isFppfLocallySurjective_of_isoSquare
      (M.scalarHom π) (N.scalarHom π) e e (e.scalar_square π)
      hM.scalar_locallySurjective, ?_⟩
  intro n
  obtain ⟨K⟩ := hM.scalarPower_finiteKernel n
  exact ⟨K.transport (Hom.kernelSetIsoOfIsoSquare
    (M.scalarHom (π ^ n)) (N.scalarHom (π ^ n)) e e (e.scalar_square (π ^ n)))⟩

theorem isPiDivisible_iff : M.IsPiDivisible π ↔ N.IsPiDivisible π :=
  ⟨e.isPiDivisible π, e.symm.isPiDivisible π⟩

theorem hasPiHeight {q h : ℕ} (hM : M.HasPiHeight π q h) :
    N.HasPiHeight π q h := by
  refine ⟨e.isPiDivisible π hM.1, fun n => ?_⟩
  exact (Hom.hasKernelRank_iff_of_kernelSetIso
    (M.scalarHom (π ^ n)) (N.scalarHom (π ^ n))
    (Hom.kernelSetIsoOfIsoSquare (M.scalarHom (π ^ n)) (N.scalarHom (π ^ n))
      e e (e.scalar_square (π ^ n))) (q ^ (n * h))).mp (hM.2 n)

theorem hasPiHeight_iff (q h : ℕ) : M.HasPiHeight π q h ↔ N.HasPiHeight π q h :=
  ⟨e.hasPiHeight π, e.symm.hasPiHeight π⟩

end Iso

end Langlands.FormalGroup.ModuleLaw
