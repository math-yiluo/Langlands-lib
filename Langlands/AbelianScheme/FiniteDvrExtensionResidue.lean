import Langlands.AbelianScheme.PotentialSemistableReductionStatement
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! # Residue fields of finite local DVR extensions -/

noncomputable section

open AlgebraicGeometry IsLocalRing Polynomial

set_option autoImplicit false

universe u

namespace Langlands.AbelianScheme

variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

namespace FiniteDvrExtension

/-- The residue algebra uses the given local homomorphism of DVRs. -/
@[instance_reducible]
def residueAlgebra (E : FiniteDvrExtension V K) :
    Algebra (ResidueField V) (ResidueField E.ring) := by
  letI := E.localHom
  infer_instance

/-- The residue extension of a local DVR extension with finite fraction-field
extension is algebraic. -/
theorem isAlgebraic_residue (E : FiniteDvrExtension V K) :
    letI := E.residueAlgebra
    Algebra.IsAlgebraic (ResidueField V) (ResidueField E.ring) := by
  classical
  let : IsLocalHom (algebraMap V E.ring) := E.localHom
  let L := E.fractionField
  let : Module.Finite K L := E.finite
  let : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower V E.ring L := IsScalarTower.of_algebraMap_eq' E.mapsCommute.symm
  let : StrongNormalizationMonoid V := UniqueFactorizationMonoid.strongNormalizationMonoid
  let : NormalizedGCDMonoid V := UniqueFactorizationMonoid.toNormalizedGCDMonoid V
  constructor
  intro b
  obtain ⟨x, rfl⟩ := residue_surjective b
  have hx : IsAlgebraic V x := by
    apply (isAlgebraic_algebraMap_iff (IsFractionRing.injective E.ring L)).mp
    exact (IsFractionRing.isAlgebraic_iff V K L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨f, hf, hfx⟩ := hx
  let g := f.primPart
  have hcomp : Function.Injective ((algebraMap E.ring L).comp (algebraMap V E.ring)) := by
    rw [E.mapsCommute]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  have hinj : Function.Injective (algebraMap V E.ring) :=
    fun _ _ h => hcomp (congrArg (algebraMap E.ring L) h)
  have hgx : eval₂ (algebraMap V E.ring) x g = 0 :=
    eval₂_primPart_eq_zero hinj hf hfx
  refine ⟨g.map (residue V), ?_, ?_⟩
  · intro h
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    apply hπ.not_isUnit
    apply (isPrimitive_iff_isUnit_of_C_dvd.mp (isPrimitive_primPart f)) π
    apply (C_dvd_iff_dvd_coeff π g).mpr
    intro i
    have hi : residue V (g.coeff i) = 0 := by
      rw [← coeff_map, h, coeff_zero]
    rwa [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← residue_eq_zero_iff]
  · change eval₂ (algebraMap (ResidueField V) (ResidueField E.ring)) (residue E.ring x)
      (g.map (residue V)) = 0
    rw [eval₂_map]
    have he : (algebraMap (ResidueField V) (ResidueField E.ring)).comp (residue V) =
        (residue E.ring).comp (algebraMap V E.ring) := by
      ext r
      rfl
    rw [he, ← hom_eval₂, hgx, map_zero]

omit [IsFractionRing V K] in
/-- Residue characteristic zero ascends along the given local extension. -/
theorem charZero_residue (E : FiniteDvrExtension V K) [CharZero (ResidueField V)] :
    CharZero (ResidueField E.ring) := by
  let : Algebra (ResidueField V) (ResidueField E.ring) := E.residueAlgebra
  exact charZero_of_injective_algebraMap (algebraMap (ResidueField V) _).injective

/-- An algebraically closed residue field remains algebraically closed in a finite local
extension of DVRs. -/
theorem isAlgClosed_residue (E : FiniteDvrExtension V K) [IsAlgClosed (ResidueField V)] :
    IsAlgClosed (ResidueField E.ring) := by
  let : Algebra (ResidueField V) (ResidueField E.ring) := E.residueAlgebra
  let : Algebra.IsAlgebraic (ResidueField V) (ResidueField E.ring) := E.isAlgebraic_residue
  exact IsAlgClosed.of_ringEquiv _ _ (RingEquiv.ofBijective
    (algebraMap (ResidueField V) (ResidueField E.ring))
    IsAlgClosed.algebraMap_bijective_of_isIntegral)

end FiniteDvrExtension

/-- Over a local ring of residue characteristic zero every positive integer is a unit. -/
theorem isUnit_natCast_of_charZero_residue (R : Type u) [CommRing R] [IsLocalRing R]
    [CharZero (ResidueField R)] {n : ℕ} (hn : 0 < n) : IsUnit (n : R) := by
  apply isUnit_of_map_unit (residue R) (n : R)
  rw [map_natCast, isUnit_iff_ne_zero, Nat.cast_ne_zero]
  exact hn.ne'

end Langlands.AbelianScheme
