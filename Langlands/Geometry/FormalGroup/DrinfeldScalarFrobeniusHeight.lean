import Langlands.Geometry.FormalGroup.Copies
import Langlands.Geometry.FormalGroup.DrinfeldResidueFrobenius
import Langlands.Geometry.FormalGroup.RelativeFrobeniusIsogenyProof
import Langlands.Geometry.FormalGroup.PiDivisible

/-! # Scalar-kernel heights when the uniformizer acts by Frobenius -/

noncomputable section

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory ValuativeRel FiniteKernelComposition

universe u v

attribute [local instance] coefficientAlgebra coefficientScalarTower

section CoordinateComparison

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N P : ModuleLaw O R τ}
variable {f : Hom M N} {g : Hom M P}
variable (h : f.toHom.toCoordinateMap = g.toHom.toCoordinateMap)

include h in
private theorem onAlgebraPoints_of_coordinates (A : CommAlgCat.{v} R) (x : M.AlgebraPoint A) :
    (f.onAlgebraPoints x : SeriesPoint A τ Empty) = g.onAlgebraPoints x := by
  change SeriesPoint.eval (f.toHom.toCoordinateMap.map (algebraMap R A)) x =
    SeriesPoint.eval (g.toHom.toCoordinateMap.map (algebraMap R A)) x
  rw [h]

/-- Formal maps given by the same actual coordinate series have the same point kernel. -/
def Hom.kernelSetIsoOfCoordinates : f.kernelSetFunctor ≅ g.kernelSetFunctor :=
  NatIso.ofComponents (fun A => ((Equiv.subtypeEquivRight (fun x : M.AlgebraPoint A => by
    rw [mem_kernelPoints, mem_kernelPoints]
    exact iff_of_eq (congrArg (fun y : SeriesPoint A τ Empty => y = (0 : N.AlgebraPoint A))
      (onAlgebraPoints_of_coordinates h A x)))) : f.kernelPoints A ≃ g.kernelPoints A).toIso)
    (fun φ => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      rfl)

include h in
/-- Local lifting and kernel-rank height depend only on the actual series of a map. -/
theorem Hom.hasHeight_of_coordinates {q k : ℕ} (hf : f.HasHeight q k) : g.HasHeight q k := by
  have hr := (hasKernelRank_iff_of_kernelSetIso f g (kernelSetIsoOfCoordinates h) (q ^ k)).mp hf.2
  refine ⟨⟨?_, hr.finiteLocallyFree⟩, hr⟩
  intro A y
  obtain ⟨B, φ, hff, hfp, x, hx⟩ := hf.1.1 A y
  refine ⟨B, φ, hff, hfp, x, ?_⟩
  exact (onAlgebraPoints_of_coordinates h B x).symm.trans hx

end CoordinateComparison

section ScalarFrobenius

open LocalDivision.DrinfeldResidue

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {σ : Type} [Finite σ] (M : ModuleLaw 𝒪[K] κ σ)
variable {π : 𝒪[K]} {p e m : ℕ} [ExpChar κ p]
variable (hcard : Nat.card 𝓀[K] = p ^ e)
variable (hπ : algebraMap 𝒪[K] κ π = 0)
variable (hPower : (M.scalarHom π).toHom.toCoordinateMap = CoordinateMap.frobeniusPow p (e * m))

include hPower in
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem scalarPower_frobeniusCoordinates (n : ℕ) :
    (M.scalarHom (π ^ n)).toHom.toCoordinateMap = CoordinateMap.frobeniusPow p (e * (n * m)) := by
  induction n with
  | zero => simp [Hom.id_toHom]
  | succ n ih =>
    rw [pow_succ, scalarHom_mul]
    change ((M.scalarHom (π ^ n)).toHom.toCoordinateMap).comp
      ((M.scalarHom π).toHom.toCoordinateMap) = _
    rw [ih, hPower, ← CoordinateMap.frobeniusPow_add]
    congr 1
    ring

include hcard hPower in
private theorem scalarPower_frobeniusHeight (n : ℕ) :
    (M.scalarHom (π ^ n)).HasHeight (Nat.card 𝓀[K]) (n * (m * Nat.card σ)) := by
  let θ := (frobenius K κ ^ ((n * m : ℕ) : ℤ)).toAlgHom
  let hθ := frobenius_natCast_toRingHom K κ p hcard (n * m)
  let g := M.frobeniusHom p (e * (n * m)) θ hθ
  have hg : g.HasHeight p ((e * (n * m)) * Nat.card σ) :=
    relativeFrobeniusIsogeny M p (e * (n * m)) θ hθ
  have hg' : g.HasHeight (Nat.card 𝓀[K]) (n * (m * Nat.card σ)) :=
    ⟨hg.1, by simpa only [hcard, ← pow_mul, Nat.mul_assoc] using hg.2⟩
  exact Hom.hasHeight_of_coordinates (scalarPower_frobeniusCoordinates M hPower n).symm hg'

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem coord_of_frobeniusCoordinates {f : Hom M M} {k : ℕ}
    (h : f.toHom.toCoordinateMap = CoordinateMap.frobeniusPow p k)
    {A : CommAlgCat.{u} κ} (x : M.AlgebraPoint A) (i : σ) :
    coord M (f.onAlgebraPoints x) i = coord M x i ^ (p ^ k) := by
  let z : SeriesPoint A σ Empty := x
  change MvPowerSeries.constantCoeff (MvPowerSeries.subst z.val
    ((f.toHom.toCoordinateMap.map (algebraMap κ A)).series i)) = _
  rw [h, CoordinateMap.map_series, CoordinateMap.frobeniusPow_series, map_pow, MvPowerSeries.map_X,
    MvPowerSeries.subst_pow z.property, MvPowerSeries.subst_X z.property, map_pow]
  rfl

include hcard hπ hPower in
/-- If the scalar uniformizer is a residue-Frobenius power on the coordinates,
all scalar powers have the actual ranks and divisibility defining the height. -/
theorem hasPiHeight_of_scalarFrobenius (hm : 0 < m) :
    M.HasPiHeight π (Nat.card 𝓀[K]) (m * Nat.card σ) := by
  have H := scalarPower_frobeniusHeight M hcard hPower
  refine ⟨⟨hπ ▸ IsNilpotent.zero, ?_, ?_, fun n => (H n).1.2⟩, fun n => (H n).2⟩
  · intro A x
    classical
    let := Fintype.ofFinite σ
    choose a ha using fun i => coord_isNilpotent x i
    let b := Finset.univ.sup a
    let q := Nat.card 𝓀[K]
    have hq : 2 ≤ q := Nat.succ_le_of_lt (Finite.one_lt_card (α := 𝓀[K]))
    have hb (n : ℕ) : n ≤ 2 ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hpos : 0 < 2 ^ n := by positivity
        rw [pow_succ]
        omega
    have hbpow : b ≤ q ^ (b * m) := calc
      b ≤ 2 ^ b := hb b
      _ ≤ q ^ b := Nat.pow_le_pow_left hq b
      _ ≤ q ^ (b * m) := pow_le_pow_right' (by omega : 1 ≤ q)
        (Nat.le_mul_of_pos_right b hm)
    refine ⟨b, ?_⟩
    rw [← scalarHom_onAlgebraPoints M (π ^ b) A x]
    apply ext_coord
    intro i
    rw [coord_zero, coord_of_frobeniusCoordinates M (scalarPower_frobeniusCoordinates M hPower b)]
    have hle : a i ≤ p ^ (e * (b * m)) := by
      rw [pow_mul, ← hcard]
      exact (Finset.le_sup (f := a) (Finset.mem_univ i)).trans hbpow
    exact pow_eq_zero_of_le hle (ha i)
  · simpa only [pow_one] using (H 1).1.1

end ScalarFrobenius

section Product

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I] (M : ModuleLaw O R Unit) {π : O} {p k : ℕ} [ExpChar R p]

/-- The scalar power formula of a one-dimensional law passes to every coordinate of its product. -/
theorem copies_scalarFrobenius (h : (M.scalarHom π).toHom.toCoordinateMap =
    CoordinateMap.frobeniusPow p k) :
    ((M.copies I).scalarHom π).toHom.toCoordinateMap = CoordinateMap.frobeniusPow p k := by
  have h' : (M.action π).toCoordinateMap = CoordinateMap.frobeniusPow (σ := Unit) p k := by
    simpa only [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id] using h
  simp only [scalarHom, Hom.smul_toHom, Hom.id_toHom, CommLaw.Hom.comp_id]
  apply CoordinateMap.ext
  funext i
  change (((M.action π).toCoordinateMap.comp (CoordinateMap.copyProjection i)).series ()) = _
  rw [h', CoordinateMap.comp_series, CoordinateMap.frobeniusPow_series, CoordinateMap.frobeniusPow_series,
    MvPowerSeries.subst_pow (CoordinateMap.copyProjection (R := R) i).hasSubst,
    MvPowerSeries.subst_X (CoordinateMap.copyProjection (R := R) i).hasSubst]
  rfl

end Product

end Langlands.FormalGroup.ModuleLaw
