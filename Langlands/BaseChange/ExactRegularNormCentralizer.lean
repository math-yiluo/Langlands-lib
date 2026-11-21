import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.OrbitalIntegral

/-! # Descent of the twisted centralizer at an exact regular norm -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v w

variable {F : Type u} [Field F] {R : Type v} [CommRing R] [Algebra F R]
  {S : Type w} [CommRing S] [Algebra F S] {n l : ℕ} {σ : S ≃ₐ[F] S}

/-- At an exact base-field norm, the element commutes with its own norm. -/
theorem commute_of_cyclicNorm_eq_baseChange (hσ : σ ^ l = 1)
    {δ : GeneralLinear n S} {g : GeneralLinear n F}
    (hn : cyclicNorm σ l δ = baseChange F S n g) :
    Commute δ (baseChange F S n g) := by
  have h := entrywiseAut_cyclicNorm σ l δ
  rw [hn, hσ, entrywiseAut_one_apply, entrywiseAut_baseChange] at h
  exact eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using h)

/-- At an exact regular base-field norm, the twisted centralizer is the
ordinary centralizer of the norm on the fixed matrices. -/
theorem mem_sigmaCentralizer_iff_commute_fixed (hσ : σ ^ l = 1)
    {g : GeneralLinear n F} (hg : IsRegularSemisimple g)
    {δ : GeneralLinear n S} (hn : cyclicNorm σ l δ = baseChange F S n g)
    (x : GeneralLinear n S) :
    x ∈ sigmaCentralizer σ n δ ↔
      Commute x (baseChange F S n g) ∧ entrywiseAut σ n x = x := by
  have hd := commute_of_cyclicNorm_eq_baseChange hσ hn
  rw [mem_sigmaCentralizer]
  constructor
  · intro hx
    have hnorm := cyclicNorm_twistedConj σ l x δ
    rw [hx, hn, hσ, entrywiseAut_one_apply] at hnorm
    have hc : Commute x (baseChange F S n g) :=
      eq_inv_mul_iff_mul_eq.mp (by simpa only [mul_assoc] using hnorm)
    refine ⟨hc, mul_left_cancel (a := δ) ?_⟩
    calc
      δ * entrywiseAut σ n x = x * δ := by
        simpa only [mul_assoc, mul_inv_cancel_left] using congrArg (x * ·) hx
      _ = δ * x := (commute_of_regular_baseChange hg hc hd).eq
  · rintro ⟨hc, hf⟩
    rw [hf, mul_assoc, ← (commute_of_regular_baseChange hg hc hd).eq, inv_mul_cancel_left]

variable (f : R →ₐ[F] S)

private theorem matrixMap_baseChange (g : GeneralLinear n F) :
    Matrix.GeneralLinearGroup.map f.toRingHom (baseChange F R n g) = baseChange F S n g := by
  ext i j
  exact f.commutes (g i j)

private theorem map_entrywise_fixed (hfix : ∀ a : R, σ (f a) = f a)
    (x : GeneralLinear n R) :
    entrywiseAut σ n (Matrix.GeneralLinearGroup.map f.toRingHom x) =
      Matrix.GeneralLinearGroup.map f.toRingHom x := by
  ext i j
  exact hfix (x i j)

private theorem exists_matrixMap_of_fixed (hf : Function.Injective f)
    (hfix : ∀ s : S, σ s = s → s ∈ Set.range f)
    {x : GeneralLinear n S} (hx : entrywiseAut σ n x = x) :
    ∃ y : GeneralLinear n R, Matrix.GeneralLinearGroup.map f.toRingHom y = x := by
  let m := f.toRingHom.mapMatrix (m := Fin n)
  have hinj : Function.Injective m := Matrix.map_injective hf
  have descend (a : GeneralLinear n S) (ha : entrywiseAut σ n a = a) :
      ∃ A : Matrix (Fin n) (Fin n) R, m A = a.val := by
    have hentry (i j : Fin n) : ∃ z : R, f z = a i j :=
      hfix _ (congrArg (fun g : GeneralLinear n S => g i j) ha)
    choose A hA using hentry
    exact ⟨Matrix.of A, Matrix.ext hA⟩
  obtain ⟨A, hA⟩ := descend x hx
  obtain ⟨B, hB⟩ := descend x⁻¹ (by rw [map_inv, hx])
  have hAB : A * B = 1 := hinj (by rw [map_mul, hA, hB, map_one]; exact x.val_inv)
  have hBA : B * A = 1 := hinj (by rw [map_mul, hA, hB, map_one]; exact x.inv_val)
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

set_option maxHeartbeats 600000 in
/-- When the fixed scalars are exactly the image of an injective
coefficient map, extending coefficients identifies the ordinary centralizer
with the twisted centralizer at an exact regular norm. -/
def exactRegularNormCentralizerEquiv (hf : Function.Injective f)
    (hfix : ∀ s : S, σ s = s ↔ s ∈ Set.range f)
    (hσ : σ ^ l = 1) {g : GeneralLinear n F} (hg : IsRegularSemisimple g)
    {δ : GeneralLinear n S} (hn : cyclicNorm σ l δ = baseChange F S n g) :
    Subgroup.centralizer ({baseChange F R n g} : Set (GeneralLinear n R))
      ≃* sigmaCentralizer σ n δ := by
  let mapGL := Matrix.GeneralLinearGroup.map (n := Fin n) f.toRingHom
  have hm : Function.Injective mapGL := Units.map_injective (Matrix.map_injective hf)
  let C := Subgroup.centralizer ({baseChange F R n g} : Set (GeneralLinear n R))
  let e := (mapGL.comp C.subtype).codRestrict (sigmaCentralizer σ n δ) (by
    intro x
    apply (mem_sigmaCentralizer_iff_commute_fixed hσ hg hn _).mpr
    have hc : Commute x.val (baseChange F R n g) :=
      Subgroup.mem_centralizer_singleton_iff.mp x.property
    refine ⟨?_, map_entrywise_fixed f (fun a => (hfix _).mpr ⟨a, rfl⟩) _⟩
    change Commute (mapGL x.val) (baseChange F S n g)
    simpa only [mapGL, matrixMap_baseChange] using hc.map mapGL)
  refine MulEquiv.ofBijective e ⟨fun x y h => Subtype.ext (hm (congrArg Subtype.val h)), ?_⟩
  intro x
  obtain ⟨hx, hxfix⟩ := (mem_sigmaCentralizer_iff_commute_fixed hσ hg hn x.val).mp x.property
  obtain ⟨y, hy⟩ := exists_matrixMap_of_fixed f hf (fun s => (hfix s).mp) hxfix
  have hyC : y ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply hm
    rw [map_mul, map_mul]
    change Matrix.GeneralLinearGroup.map f.toRingHom y *
        Matrix.GeneralLinearGroup.map f.toRingHom (baseChange F R n g) = _
    rw [hy, matrixMap_baseChange]
    exact hx.eq
  exact ⟨⟨y, hyC⟩, Subtype.ext hy⟩

@[simp]
theorem exactRegularNormCentralizerEquiv_apply_val (hf : Function.Injective f)
    (hfix : ∀ s : S, σ s = s ↔ s ∈ Set.range f)
    (hσ : σ ^ l = 1) {g : GeneralLinear n F} (hg : IsRegularSemisimple g)
    {δ : GeneralLinear n S} (hn : cyclicNorm σ l δ = baseChange F S n g)
    (x : Subgroup.centralizer ({baseChange F R n g} : Set (GeneralLinear n R))) :
    (exactRegularNormCentralizerEquiv f hf hfix hσ hg hn x).val =
      Matrix.GeneralLinearGroup.map f.toRingHom x.val := rfl

end Langlands.BaseChange
