import Langlands.ClassFieldTheory.Local.LocalUnramifiedNorm
import Langlands.ClassFieldTheory.Local.CyclicClassNormProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariant

noncomputable section

open Langlands.LocalClassField ValuativeRel

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private def localUnitOrderMod (d : ℕ) : Kˣ →* Multiplicative (ZMod d) where
  toFun a := Multiplicative.ofAdd (normalizedUnitOrder K (.ofMul a) : ZMod d)
  map_one' := by
    change Multiplicative.ofAdd (normalizedUnitOrder K 0 : ZMod d) = _
    rw [map_zero, Int.cast_zero]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd
      (normalizedUnitOrder K (.ofMul a + .ofMul b) : ZMod d) = _
    rw [map_add, Int.cast_add]
    rfl

private theorem localUnitOrderMod_surjective (d : ℕ) :
    Function.Surjective (localUnitOrderMod K d) := by
  intro z
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective z.toAdd
  obtain ⟨a, ha⟩ := normalizedUnitOrder_surjective K n
  refine ⟨a.toMul, ?_⟩
  change Multiplicative.ofAdd (normalizedUnitOrder K a : ZMod d) = z
  rw [ha, hn]
  rfl

variable (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

private theorem localUnitOrderMod_ker (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) :
    normSubgroup K L = (localUnitOrderMod K (Module.finrank K L)).ker := by
  ext a
  rw [mem_normSubgroup_iff_of_localUnramified K L hcont he, MonoidHom.mem_ker]
  change _ ↔ Multiplicative.ofAdd (normalizedUnitOrder K (.ofMul a) :
    ZMod (Module.finrank K L)) = Multiplicative.ofAdd 0
  rw [Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Normalized order modulo the degree on the actual unramified norm quotient. -/
def localUnramifiedNormOrderEquiv (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) :
    Additive (NormQuotient K L) ≃+ ZMod (Module.finrank K L) := by
  let d := Module.finrank K L
  let f : Kˣ →* Multiplicative (ZMod d) := localUnitOrderMod K d
  let e : NormQuotient K L ≃* Multiplicative (ZMod d) :=
    (QuotientGroup.quotientMulEquivOfEq (localUnitOrderMod_ker K L hcont he)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (localUnitOrderMod_surjective K d))
  exact e.toAdditiveLeft

theorem localUnramifiedNormOrderEquiv_projection (hcont : Continuous (algebraMap K L))
    (he : localRamificationFactor K L = 1) (a : Kˣ) :
    localUnramifiedNormOrderEquiv K L hcont he
      (.ofMul (normQuotientProjection K L a)) =
      (normalizedUnitOrder K (.ofMul a) : ZMod (Module.finrank K L)) := rfl

variable [IsGalois K L]
  (hcont : Continuous (algebraMap K L)) (he : localRamificationFactor K L = 1)
  (χ : Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)))

/-- The finite unramified invariant on relative unit cohomology for a cyclic coordinate. -/
def finiteLocalUnramifiedInvariantEquiv : relativeCohomology K L 2 ≃+
    denominatorSubgroup (Module.finrank K L) :=
  (cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)).trans
    ((localUnramifiedNormOrderEquiv K L hcont he).trans
      (denominatorEquiv _ Module.finrank_pos))

/-- The finite unramified invariant as a homomorphism into the actual quotient Q/Z. -/
def finiteLocalUnramifiedInvariant : relativeCohomology K L 2 →+ RationalModIntegers :=
  (denominatorSubgroup (Module.finrank K L)).subtype.comp
    (finiteLocalUnramifiedInvariantEquiv K L hcont he χ).toAddMonoidHom

theorem finiteLocalUnramifiedInvariant_injective :
    Function.Injective (finiteLocalUnramifiedInvariant K L hcont he χ) :=
  Subtype.val_injective.comp (finiteLocalUnramifiedInvariantEquiv K L hcont he χ).injective

theorem finiteLocalUnramifiedInvariant_range :
    (finiteLocalUnramifiedInvariant K L hcont he χ).range =
      denominatorSubgroup (Module.finrank K L) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (finiteLocalUnramifiedInvariantEquiv K L hcont he χ x).property
  · intro hy
    let e := finiteLocalUnramifiedInvariantEquiv K L hcont he χ
    exact ⟨e.symm ⟨y, hy⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩

local instance localDegree_neZero : NeZero (Module.finrank K L) :=
  ⟨Module.finrank_pos.ne'⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
private theorem cyclicH2NormEquiv_cyclicClass (a : Kˣ) :
    cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ) (cyclicCoordinateGenerator_generates χ)
      (cyclicClass K L χ.toMonoidHom a) = .ofMul (normQuotientProjection K L a) :=
  cyclicClassNormNormalization K L _ χ (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ) (χ.apply_symm_apply _) a

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- Each finite relative class is represented by a positive carry cocycle. -/
theorem exists_finiteLocal_cyclicClass (x : relativeCohomology K L 2) :
    ∃ a : Kˣ, cyclicClass K L χ.toMonoidHom a = x := by
  let e := cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (normSubgroup K L) (e x).toMul
  refine ⟨a, e.injective ?_⟩
  change cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ) (cyclicClass K L χ.toMonoidHom a) = e x
  rw [cyclicH2NormEquiv_cyclicClass]
  exact congrArg Additive.ofMul ha

/-- The finite invariant of the positive carry is normalized order divided by degree. -/
theorem finiteLocalUnramifiedInvariant_cyclicClass (a : Kˣ) :
    finiteLocalUnramifiedInvariant K L hcont he χ (cyclicClass K L χ.toMonoidHom a) =
      rationalClass ((normalizedUnitOrder K (.ofMul a) : ℚ) / Module.finrank K L) := by
  change (denominatorEquiv _ Module.finrank_pos (localUnramifiedNormOrderEquiv K L hcont he
    (cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ) (cyclicCoordinateGenerator_generates χ)
      (cyclicClass K L χ.toMonoidHom a))) : RationalModIntegers) = _
  rw [cyclicH2NormEquiv_cyclicClass, localUnramifiedNormOrderEquiv_projection,
    denominatorEquiv_intCast]

end Langlands.ClassFieldTheory.Local
