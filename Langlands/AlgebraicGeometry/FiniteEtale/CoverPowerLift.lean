import Langlands.AlgebraicGeometry.FiniteEtale.CoverStabilizerLift
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Etale.Field

/-! # Lifting positive powers to a pointed finite étale cover -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (Y : Cover S) (x : Fiber s Y)
  (ht : ∀ Z : Cover Y.obj.left, Finite (Fiber x.left Z))

/-- The image of the fundamental group of a pointed finite étale cover has finite index. -/
theorem finiteIndex_range_fundamentalGroupMap :
    (fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs).range.FiniteIndex := by
  let : Finite (Fiber s Y) := hs Y
  rw [range_fundamentalGroupMap]
  have : Finite (FundamentalGroup s hs ⧸ MulAction.stabilizer (FundamentalGroup s hs) x) :=
    Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer (FundamentalGroup s hs) x)
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Lift a positive power to the supplied cover at the supplied geometric lift.
The exponent is uniform in the fundamental group element. -/
def liftPowerToCover (g : FundamentalGroup s hs) :
    {k : FundamentalGroup x.left ht //
      fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs k =
        g ^ Nat.card (Equiv.Perm (Fiber s Y))} := by
  letI : Finite (Fiber s Y) := hs Y
  let action := MulAction.toPermHom (FundamentalGroup s hs) (Fiber s Y)
  let m := Nat.card (Equiv.Perm (Fiber s Y))
  have hperm : action (g ^ m) = 1 := by rw [map_pow, pow_card_eq_one']
  have hfix : (g ^ m) • x = x :=
    congrArg (fun e : Equiv.Perm (Fiber s Y) => e x) hperm
  exact ⟨stabilizerLift s hs Y x ht (g ^ m) hfix,
    fundamentalGroupMap_stabilizerLift s hs Y x ht (g ^ m) hfix⟩

/-- A homomorphism trivial on the cover image takes values of finite order. -/
theorem isOfFinOrder_of_trivial_on_cover {G : Type*} [Group G]
    (ρ : FundamentalGroup s hs →* G)
    (hρ : ∀ k, ρ (fundamentalGroupMap Y.obj.hom x.left s (Over.w x) ht hs k) = 1)
    (g : FundamentalGroup s hs) : IsOfFinOrder (ρ g) := by
  let : Finite (Fiber s Y) := hs Y
  obtain ⟨k, hk⟩ := liftPowerToCover s hs Y x ht g
  refine isOfFinOrder_iff_pow_eq_one.mpr
    ⟨Nat.card (Equiv.Perm (Fiber s Y)), Finite.card_pos, ?_⟩
  rw [← map_pow, ← hk, hρ]

/-- The actual spectrum of a finite separable field extension as a finite étale cover. -/
def fieldExtensionCover (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Cover (Spec (.of K)) := by
  have : IsFinite (Spec.algebraMap K L) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FinitePresentation K L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Etale (Spec.algebraMap K L) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr (show Algebra.Etale K L from {}))
  exact cover (Spec.algebraMap K L)

/-- An algebraically closed geometric point lifts to the supplied finite separable extension. -/
def fieldExtensionCoverPoint (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K)) : Fiber s (fieldExtensionCover K L) := by
  letI : Algebra K Ω := (Spec.preimage s).hom.toAlgebra
  let e : L →ₐ[K] Ω := IsAlgClosed.lift
  refine Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) ?_
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K L)) = s
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom e.toRingHom =
      Spec.preimage s := by
    ext k
    exact e.commutes k
  rw [he, Spec.map_preimage]

end Langlands.AlgebraicGeometry.FiniteEtale
