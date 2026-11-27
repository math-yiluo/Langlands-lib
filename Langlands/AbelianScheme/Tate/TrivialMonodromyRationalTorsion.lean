import Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement
import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.Tate.PrimeAdicSeparation
import Langlands.AbelianScheme.Tate.RestrictedProductProof
import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.FixedPointSection

/-! # Trivial rational prime-adic monodromy makes prime-power torsion rational -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme.Tate.PrimeAdic

variable {L : Type u} [Field L] (B : AbelianScheme (Spec (.of L))) (ℓ : ℕ) [Fact ℓ.Prime]
  (hu : ∀ m : ℕ, IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of L), ⊤)))

/-- The geometric point of `Spec L` given by the algebraic closure of `L`. -/
abbrev closurePoint (L : Type u) [Field L] :
    Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of L) :=
  Spec.algebraMap L (AlgebraicClosure L)

/-- If every element of the fundamental group acts trivially on the rational
prime-adic Tate module, it acts trivially on the integral one. -/
theorem monodromyMap_eq_self_of_rationalMonodromy_eq_one
    (h : ∀ g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)),
      rationalMonodromyRepresentation (closurePoint L) (geometricFiberFinite (closurePoint L))
        torsionFiniteEtale B ℓ hu g = 1)
    (g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)))
    (x : Integral B (Over.mk (closurePoint L)) ℓ) :
    monodromyMap (closurePoint L) (geometricFiberFinite (closurePoint L)) torsionFiniteEtale
      B ℓ hu g x = x := by
  apply GroupScheme.Tate.PrimeAdic.toRational_injective B.toGrp (Over.mk (closurePoint L)) ℓ
  have h1 := toRational_monodromy (closurePoint L) (geometricFiberFinite (closurePoint L))
    torsionFiniteEtale B ℓ hu g x
  have h2 : rationalMonodromy (closurePoint L) (geometricFiberFinite (closurePoint L))
      torsionFiniteEtale B ℓ hu g
        (GroupScheme.Tate.PrimeAdic.toRational B.toGrp (Over.mk (closurePoint L)) ℓ x) =
      GroupScheme.Tate.PrimeAdic.toRational B.toGrp (Over.mk (closurePoint L)) ℓ x := by
    have := congrArg (fun φ => φ (GroupScheme.Tate.PrimeAdic.toRational B.toGrp
      (Over.mk (closurePoint L)) ℓ x)) (h g)
    exact this
  exact h1.trans h2

omit [Fact ℓ.Prime] in
include hu in
/-- The prime is nonzero in the algebraic closure when it is a unit on `Spec L`. -/
theorem natCast_ne_zero_closure : ((ℓ : ℕ) : AlgebraicClosure L) ≠ 0 := by
  have h1 : IsUnit ((ℓ : ℕ) : Γ(Spec (.of L), ⊤)) := by simpa using hu 1
  have h2 : IsUnit ((ℓ : ℕ) : L) := by
    have := h1.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
    simpa using this
  intro h0
  apply h2.ne_zero
  apply (algebraMap L (AlgebraicClosure L)).injective
  simpa using h0

/-- Trivial rational monodromy fixes every point of each prime-power torsion level. -/
theorem levelMonodromy_eq_self_of_rationalMonodromy_eq_one
    (h : ∀ g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)),
      rationalMonodromyRepresentation (closurePoint L) (geometricFiberFinite (closurePoint L))
        torsionFiniteEtale B ℓ hu g = 1)
    (ν : ℕ) (g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)))
    (y : Level B (Over.mk (closurePoint L)) ℓ ν) :
    levelMonodromy (closurePoint L) (geometricFiberFinite (closurePoint L)) torsionFiniteEtale
      B (ℓ ^ ν) (pow_pos (Fact.out : ℓ.Prime).pos ν) (hu ν) g y = y := by
  have hdiv : ∀ z : Over.mk (closurePoint L) ⟶ B.toGrp.X, ∃ w, w ^ ℓ = z := fun z =>
    algClosedPointDivisibility _ B (AlgebraicClosure L) (closurePoint L) ℓ
      (natCast_ne_zero_closure ℓ hu) z
  obtain ⟨x, rfl⟩ := GroupScheme.Tate.PrimeAdic.evaluation_surjective_of_pow B.toGrp
    (Over.mk (closurePoint L)) ℓ hdiv ν y
  rw [← evaluation_monodromyMap,
    monodromyMap_eq_self_of_rationalMonodromy_eq_one B ℓ hu h g x]

/-- Trivial rational prime-adic monodromy at the algebraic closure makes every
geometric `ℓ ^ ν`-torsion point of `B` rational over `L`. -/
theorem hasRationalGeometricTorsion_of_rationalMonodromy_eq_one
    (h : ∀ g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)),
      rationalMonodromyRepresentation (closurePoint L) (geometricFiberFinite (closurePoint L))
        torsionFiniteEtale B ℓ hu g = 1)
    (ν : ℕ) : HasRationalGeometricTorsion B (ℓ ^ ν) := by
  intro x hx
  have hn : 0 < ℓ ^ ν := pow_pos (Fact.out : ℓ.Prime).pos ν
  have hx' : x ^ (ℓ ^ ν) = 1 := by
    have := (GroupScheme.mem_torsionPoints B.toGrp ((ℓ ^ ν : ℕ) : ℤ) _ x).mp hx
    simpa only [zpow_natCast] using this
  let y : GroupScheme.Tate.Level B.toGrp (Over.mk (closurePoint L)) (ℓ ^ ν) :=
    Additive.ofMul ⟨x, (GroupScheme.Tate.mem_levelGroup B.toGrp (Over.mk (closurePoint L))
      (ℓ ^ ν) x).mpr hx'⟩
  let k := (GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (closurePoint L)) (ℓ ^ ν)).symm y
  have hfix : ∀ g : FundamentalGroup (closurePoint L) (geometricFiberFinite (closurePoint L)),
      g • (show Fiber (closurePoint L) (torsionCover torsionFiniteEtale B (ℓ ^ ν) hn (hu ν))
        from k.toMul) = k.toMul := by
    intro g
    have h1 := kernelPoint_levelMonodromy (closurePoint L) (geometricFiberFinite (closurePoint L))
      torsionFiniteEtale B (ℓ ^ ν) hn (hu ν) g y
    rw [levelMonodromy_eq_self_of_rationalMonodromy_eq_one B ℓ hu h ν g y] at h1
    exact h1.symm
  obtain ⟨σ, hσ1, hσ2⟩ := sectionOfFixedGeometricLift (closurePoint L)
    (geometricFiberFinite (closurePoint L))
    (torsionCover torsionFiniteEtale B (ℓ ^ ν) hn (hu ν)) k.toMul hfix
  let incl := (GroupScheme.kernelι (GroupScheme.multiplication B.toGrp ((ℓ ^ ν : ℕ) : ℤ))).hom.hom
  have hk : k.toMul ≫ incl = x := by
    have h2 := GroupScheme.kernelPointsEquiv_val
      (GroupScheme.multiplication B.toGrp ((ℓ ^ ν : ℕ) : ℤ)) (Over.mk (closurePoint L)) k.toMul
    have h3 : (GroupScheme.Tate.kernelLevelEquiv B.toGrp (Over.mk (closurePoint L)) (ℓ ^ ν))
        k = y := AddEquiv.apply_symm_apply _ y
    exact h2.symm.trans (congrArg (fun z => (Additive.toMul z).val) h3)
  refine ⟨Over.homMk (σ ≫ incl.left) ?_, ?_⟩
  · change (σ ≫ incl.left) ≫ B.X.hom = 𝟙 _
    rw [Category.assoc, Over.w incl]
    exact hσ1
  · apply Over.OverMorphism.ext
    change closurePoint L ≫ σ ≫ incl.left = x.left
    rw [← Category.assoc, hσ2]
    exact congrArg CommaMorphism.left hk

end Langlands.AbelianScheme.Tate.PrimeAdic
