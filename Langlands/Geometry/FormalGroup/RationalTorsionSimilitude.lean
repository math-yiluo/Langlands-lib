import Langlands.Geometry.FormalGroup.TorsionPolarizationSimilitude
import Langlands.Geometry.FormalGroup.RationalSectionGlobal
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # The rational multiplier condition on scalar-divisible formal modules -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {C : Type w} [CommRing C]
variable {k : Type z} [Field k] [Algebra C k]
variable {O : Type u} [CommRing O] [Algebra C O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {p : C} {hM : M.IsPiDivisible (algebraMap C O p)}
variable {hN : N.IsPiDivisible (algebraMap C O p)}

/-- The two polarizations are compared by the same rational multiplier on every open.
An integral representative of `p^n` times the rational map has multiplier `p^(2n)` times
that rational multiplier. The integral relation is checked on the actual torsion. -/
def HasLocalTorsionSimilitude (p : C)
    {hM : M.IsPiDivisible (algebraMap C O p)} {hN : N.IsPiDivisible (algebraMap C O p)}
    (P : TorsionPrincipalPolarization hM) (Q : TorsionPrincipalPolarization hN)
    {U : Opens (PrimeSpectrum R)} (f : RationalSection F M N U) (c : kˣ) : Prop :=
  ∀ x : U,
    ∃ (V : Opens (PrimeSpectrum R)) (_hx : (x : PrimeSpectrum R) ∈ V) (i : V ⟶ U)
      (n : ℕ) (g : OpenIntegralHom M N V) (a : C),
      g.IsIsogeny ∧
        (algebraMap O F (algebraMap C O p)) ^ n • restrict i f = ofIntegral V g ∧
        algebraMap C k a = (algebraMap C k p) ^ (2 * n) * (c : k) ∧
        g.IsTorsionSimilitude
          (P.baseChange (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V))))
          (Q.baseChange (IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op V))))
          (algebraMap C O a)

namespace HasLocalTorsionSimilitude

variable {P : TorsionPrincipalPolarization hM} {Q : TorsionPrincipalPolarization hN}
variable {U : Opens (PrimeSpectrum R)} {f : RationalSection F M N U} {c : kˣ}

/-- The chosen numerator witnesses give the actual local-isogeny condition. -/
theorem isLocallyScalarIsogeny (hf : HasLocalTorsionSimilitude p P Q f c) :
    IsLocallyScalarIsogeny (algebraMap C O p) f := by
  intro x hx
  obtain ⟨V, hxV, i, n, g, _, hg, heq, _, _⟩ := hf ⟨x, hx⟩
  exact ⟨V, hxV, i, n, g, hg, heq⟩

/-- Regard the same section as a local quasi-isogeny. -/
def toLocalQuasiIsogeny (hf : HasLocalTorsionSimilitude p P Q f c)
    (hp : algebraMap O F (algebraMap C O p) ≠ 0) :
    LocalQuasiIsogeny F (algebraMap C O p) M N U where
  scalar_ne_zero := hp
  source_divisible := hM
  target_divisible := hN
  val := f
  isLocal := hf.isLocallyScalarIsogeny

@[simp]
theorem toLocalQuasiIsogeny_val (hf : HasLocalTorsionSimilitude p P Q f c)
    (hp : algebraMap O F (algebraMap C O p) ≠ 0) :
    (hf.toLocalQuasiIsogeny hp).val = f := rfl

/-- A global tensor presentation gives local similitude witnesses on every open. -/
theorem ofGlobalPresentationOn {z : RationalHom F M N} (n : ℕ) (g : Hom M N) (hg : g.IsIsogeny)
    (hrep : (algebraMap O F (algebraMap C O p)) ^ n • z = RationalHom.ofHom g)
    (a : C) (ha : algebraMap C k a = (algebraMap C k p) ^ (2 * n) * (c : k))
    (hpair : g.IsTorsionSimilitude P Q (algebraMap C O a)) :
    HasLocalTorsionSimilitude p P Q (RationalSection.ofGlobalOn U z) c := by
  intro x
  let φ := IsScalarTower.toAlgHom O R ((coefficientStructurePresheaf R).obj (op U))
  refine ⟨U, x.property, 𝟙 U, n, g.map φ, a, hg.map φ, ?_, ha, hpair.baseChange φ⟩
  have h := congrArg (RationalSection.ofGlobalOn U) hrep
  simpa only [restrict_id, map_smul, RationalSection.ofGlobalOn_ofHom,
    RationalSection.ofHom] using h

/-- An integral map with an integral multiplier has exponent zero. -/
theorem ofGlobalOn (g : Hom M N) (hg : g.IsIsogeny) (a : C)
    (ha : algebraMap C k a = (c : k))
    (hpair : g.IsTorsionSimilitude P Q (algebraMap C O a)) :
    HasLocalTorsionSimilitude p P Q
      (RationalSection.ofGlobalOn U (RationalHom.ofHom (F := F) g)) c :=
  ofGlobalPresentationOn 0 g hg (by rw [pow_zero, one_smul]) a
    (by simpa only [Nat.mul_zero, pow_zero, one_mul] using ha) hpair

/-- Compatible witnesses on an open cover give the same relation on the whole open. -/
theorem of_cover {ι : Type*} (V : ι → Opens (PrimeSpectrum R)) (i : ∀ j, V j ⟶ U)
    (hcover : ∀ x ∈ U, ∃ j, x ∈ V j)
    (hf : ∀ j, HasLocalTorsionSimilitude p P Q (RationalSection.restrict (i j) f) c) :
    HasLocalTorsionSimilitude p P Q f c := by
  intro x
  obtain ⟨j, hx⟩ := hcover x x.property
  obtain ⟨W, hxW, k, n, g, a, hg, heq, ha, hpair⟩ := hf j ⟨x, hx⟩
  exact ⟨W, hxW, k ≫ i j, n, g, a, hg, by simpa only [restrict_comp] using heq, ha, hpair⟩

/-- The identity rational section is a similitude with multiplier one. -/
theorem id (P : TorsionPrincipalPolarization hM) (U : Opens (PrimeSpectrum R)) :
    HasLocalTorsionSimilitude p P P (RationalSection.id (F := F) M U) (1 : kˣ) := by
  have hs : (Hom.id M).IsTorsionSimilitude P P (algebraMap C O 1) := by
    simpa only [map_one] using Hom.IsTorsionSimilitude.id P
  have hh := ofGlobalOn (p := p) (F := F) (U := U) (c := (1 : kˣ)) (Hom.id M)
    (Iso.refl M).isIsogeny 1 (map_one _) hs
  change HasLocalTorsionSimilitude p P P
    (RationalSection.ofGlobalOn U (RationalHom.id (F := F) M)) (1 : kˣ) at hh
  rwa [RationalSection.ofGlobalOn_id] at hh

end HasLocalTorsionSimilitude

/-- Harris's multiplier lies in the actual field of p-adic numbers. -/
abbrev HasPadicTorsionSimilitude (prime : ℕ) [Fact prime.Prime] [Algebra ℤ_[prime] O]
    {hM : M.IsPiDivisible (algebraMap ℤ_[prime] O (prime : ℤ_[prime]))}
    {hN : N.IsPiDivisible (algebraMap ℤ_[prime] O (prime : ℤ_[prime]))}
    (P : TorsionPrincipalPolarization hM) (Q : TorsionPrincipalPolarization hN)
    {U : Opens (PrimeSpectrum R)} (f : RationalSection F M N U) (c : ℚ_[prime]ˣ) : Prop :=
  HasLocalTorsionSimilitude (prime : ℤ_[prime]) P Q f c

end Langlands.FormalGroup.ModuleLaw.RationalSection
