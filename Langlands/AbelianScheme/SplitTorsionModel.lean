import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevel
import Langlands.AbelianScheme.BaseChangeCoherence
import Langlands.AbelianScheme.SubalgebraDescentProof
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FiniteEtale.FixedPointSection
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteFieldPointDescent

/-! # Descent of an abelian scheme with split geometric torsion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AbelianScheme

/-- Descent to a finitely generated ring where the torsion order is invertible, with all
points of the given geometric fibre of the torsion cover lifting to one finitely generated
extension subalgebra. -/
def SplitTorsionModelStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K)) (A : AbelianScheme (Spec (.of K))) (n : ℕ) (hn : 0 < n)
    (hu : IsUnit (n : Γ(Spec (.of K), ⊤))),
    (∀ (g : FundamentalGroup s (geometricFiberFinite s)) (x : Tate.Level A (Over.mk s) n),
      Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale A n hn hu g x = x) →
    ∃ (C D : Subalgebra ℤ K) (hCD : C ≤ D), C.FG ∧ D.FG ∧
      ∃ (A₀ : AbelianScheme (Spec (.of ↥C))) (hu₀ : IsUnit (n : Γ(Spec (.of ↥C), ⊤))),
        Nonempty (A ≅ (baseChange (Spec.algebraMap ↥C K)).obj A₀) ∧
        letI : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
        let Y := Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀
        ∀ x : Fiber (s ≫ Spec.algebraMap ↥C K) Y,
          ∃ y : RingPoint ↥C Y.obj ↥D, s ≫ Spec.algebraMap ↥D K ≫ y.left = x.left

private theorem existsInvertibleModel {K : Type u} [Field K]
    (A : AbelianScheme (Spec (.of K))) (n : ℕ) (hu : IsUnit (n : Γ(Spec (.of K), ⊤))) :
    ∃ (C : Subalgebra ℤ K), C.FG ∧
      ∃ (A₀ : AbelianScheme (Spec (.of ↥C))), IsUnit (n : Γ(Spec (.of ↥C), ⊤)) ∧
        Nonempty (A ≅ (baseChange (Spec.algebraMap ↥C K)).obj A₀) := by
  obtain ⟨C₁, hC₁, A₁, ⟨e₁⟩⟩ := subalgebraDescent (.of K) A
  have hnK : IsUnit (n : K) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  let T : Subalgebra ↥C₁ K := Algebra.adjoin ↥C₁ ({(n : K)⁻¹} : Set K)
  let C := T.restrictScalars ℤ
  have hT : T.FG := ⟨{(n : K)⁻¹}, by simp [T]⟩
  have hC : C.FG := SubalgebraDescentProof.fg_restrictScalars C₁ T hC₁ hT
  have hnC : IsUnit (n : C) := by
    let m : C := ⟨(n : K)⁻¹, Algebra.subset_adjoin (Set.mem_singleton _)⟩
    exact IsUnit.of_mul_eq_one m (Subtype.ext (by simpa [m] using mul_inv_cancel₀ hnK.ne_zero))
  let b := Spec.algebraMap ↥C K
  let c : Spec (.of ↥C) ⟶ Spec (.of ↥C₁) := Spec.algebraMap ↥C₁ ↥T
  let A₀ := (baseChange c).obj A₁
  have heq : Spec.algebraMap ↥C₁ K = b ≫ c := SubalgebraDescentProof.specMap_comp C₁ T
  let e : A ≅ (baseChange b).obj A₀ :=
    e₁ ≪≫ eqToIso (congrArg (fun f ↦ (baseChange f).obj A₁) heq) ≪≫ baseChangeCompIso c b A₁
  have hu₀ : IsUnit (n : Γ(Spec (.of ↥C), ⊤)) := by
    simpa using hnC.map (Scheme.ΓSpecIso (CommRingCat.of ↥C)).inv.hom
  exact ⟨C, hC, A₀, hu₀, ⟨e⟩⟩

private theorem fixedLevel_of_iso {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {A B : AbelianScheme S} (e : A ≅ B)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤)))
    (g : FundamentalGroup s (geometricFiberFinite s))
    (hfix : ∀ x, Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale A n hn hu g x = x)
    (x : Tate.Level B (Over.mk s) n) :
    Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale B n hn hu g x = x := by
  obtain ⟨z, rfl⟩ := (PolarizedFiniteLevel.levelIsoLinear e (Over.mk s) n).surjective x
  change Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale B n hn hu g
    (Tate.levelMap (Over.mk s) e.hom n z) = Tate.levelMap (Over.mk s) e.hom n z
  rw [Tate.levelMonodromy_map, hfix]

private theorem fixedFiber_of_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S')
    (A₀ : AbelianScheme S) (n : ℕ) (hn : 0 < n)
    (hu₀ : IsUnit (n : Γ(S, ⊤))) (hu : IsUnit (n : Γ(S', ⊤)))
    (g : FundamentalGroup s (geometricFiberFinite s))
    (hfix : ∀ z, Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale
      ((baseChange b).obj A₀) n hn hu g z = z)
    (x : Fiber (s ≫ b) (Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀)) :
    fundamentalGroupMap b s (s ≫ b) rfl (geometricFiberFinite s) (geometricFiberFinite (s ≫ b))
      g • x = x := by
  let t := s ≫ b
  let sFin := geometricFiberFinite s
  let tFin := geometricFiberFinite t
  let f := fundamentalGroupMap b s t rfl sFin tFin
  obtain ⟨z, hz⟩ := (GroupScheme.Tate.levelBaseChange b A₀.toGrp (Over.mk s) n).surjective
    (Tate.kernelLevelEquiv A₀ (Over.mk t) n (Additive.ofMul x))
  have hmon := Tate.levelBaseChange_monodromy b s sFin tFin torsionFiniteEtale A₀ n hn hu₀ hu g z
  rw [hfix, hz] at hmon
  have hk := Tate.levelMonodromy_kernel t tFin torsionFiniteEtale A₀ n hn hu₀ (f g)
    (Additive.ofMul x)
  rw [hk] at hmon
  exact congrArg Additive.toMul ((Tate.kernelLevelEquiv A₀ (Over.mk t) n).injective hmon.symm)

private theorem descendFixedFiberPoints {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]
    (C : Subalgebra ℤ K) (hC : C.FG) (s : Spec (.of Ω) ⟶ Spec (.of K))
    (Y : Cover (Spec (.of ↥C)))
    (hfixY : ∀ (g : FundamentalGroup s (geometricFiberFinite s))
      (x : Fiber (s ≫ Spec.algebraMap ↥C K) Y),
      fundamentalGroupMap (Spec.algebraMap ↥C K) s (s ≫ Spec.algebraMap ↥C K) rfl
        (geometricFiberFinite s) (geometricFiberFinite (s ≫ Spec.algebraMap ↥C K)) g • x = x) :
    ∃ (D : Subalgebra ℤ K) (hCD : C ≤ D), D.FG ∧
      letI : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
      ∀ x : Fiber (s ≫ Spec.algebraMap ↥C K) Y,
        ∃ y : RingPoint ↥C Y.obj ↥D, s ≫ Spec.algebraMap ↥D K ≫ y.left = x.left := by
  let b := Spec.algebraMap ↥C K
  let YK := (pullbackFunctor b).obj Y
  let t := s ≫ b
  let sFin := geometricFiberFinite s
  let tFin := geometricFiberFinite t
  let xK (x : Fiber t Y) := pullbackFiberEquiv b s t rfl Y x
  have hfixYK (x : Fiber t Y) (g : FundamentalGroup s sFin) : g • xK x = xK x := by
    have hg := pullbackFiberEquiv_smul b s t rfl sFin tFin g Y x
    rw [hfixY g x] at hg
    exact hg.symm
  let σ (x : Fiber t Y) := sectionOfFixedGeometricLift s sFin YK (xK x) (hfixYK x)
  let yK (x : Fiber t Y) : RingPoint ↥C Y.obj K := Over.homMk
    ((σ x).val ≫ pullback.fst Y.obj.hom b) (by
      change _ ≫ Y.obj.hom = b
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change ((σ x).val ≫ YK.obj.hom) ≫ b = b
      rw [(σ x).property.1, Category.id_comp])
  have hyK (x : Fiber t Y) : s ≫ (yK x).left = x.left := by
    change s ≫ ((σ x).val ≫ pullback.fst Y.obj.hom b) = x.left
    rw [← Category.assoc, (σ x).property.2]
    exact pullbackFiberEquiv_apply_left_fst b s t rfl Y x
  have : Finite (Fiber t Y) := tFin Y
  obtain ⟨D, hCD, hD, hy⟩ := Langlands.AlgebraicGeometry.finiteFieldPointDescent
    K C hC Y.obj (Fiber t Y) yK
  refine ⟨D, hCD, hD, ?_⟩
  let : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
  let : IsScalarTower ↥C ↥D K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨yD, hyD⟩ := hy
  intro x
  refine ⟨yD x, ?_⟩
  have hleft : Spec.algebraMap ↥D K ≫ (yD x).left = (yK x).left :=
    congrArg (fun p : RingPoint ↥C Y.obj K => p.left) (hyD x)
  rw [hleft, hyK]

/-- Descend the abelian scheme, adjoin the inverse of the level, and use fixed points as
sections over the field. Their coordinate maps descend together to a larger subalgebra. -/
theorem splitTorsionModel : SplitTorsionModelStatement.{u} := by
  intro K Ω _ _ _ s A n hn hu hfix
  obtain ⟨C, hC, A₀, hu₀, ⟨e⟩⟩ := existsInvertibleModel A n hu
  let b := Spec.algebraMap ↥C K
  let Y := Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀
  obtain ⟨D, hCD, hD, hDpts⟩ := descendFixedFiberPoints C hC s Y (fun g ↦
    fixedFiber_of_baseChange b s A₀ n hn hu₀ hu g (fixedLevel_of_iso s e n hn hu g (hfix g)))
  exact ⟨C, D, hCD, hC, hD, A₀, hu₀, ⟨e⟩, hDpts⟩

end Langlands.AbelianScheme
