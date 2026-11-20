import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.RationalSectionGlobal
import Langlands.Geometry.FormalGroup.GlobalAtlasRationalMorphism
import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.FiniteKernelComposition
import Langlands.Geometry.FormalGroup.ScalarIsogenyTensorInverse

/-! # Global scalar-denominator presentations with actual kernel ranks -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M M' : ModuleLaw O R σ} {N N' : ModuleLaw O R τ}

namespace RationalHom

/-- A global scalar denominator with a constant rank of the actual numerator kernel. -/
structure GlobalHeightPresentation (π : O) (q : ℕ) (z : RationalHom F M N)
    extends ScalarIsogenyPresentation π z where
  numeratorHeight : ℕ
  numeratorRank : representative.HasKernelRank (q ^ numeratorHeight)

namespace GlobalHeightPresentation

variable {π : O} {q H : ℕ} {z : RationalHom F M N}

/-- Signed kernel-rank height when the source has scalar height `H`. -/
def index (P : GlobalHeightPresentation π q z) (H : ℕ) : ℤ :=
  (P.numeratorHeight : ℤ) - (P.exponent : ℤ) * H

/-- Base change preserves the ranked integral numerator and its scalar denominator. -/
def map (P : GlobalHeightPresentation π q z) (φ : R →ₐ[O] S) :
    GlobalHeightPresentation π q (RationalHom.map φ z) where
  toScalarIsogenyPresentation := P.toScalarIsogenyPresentation.map φ
  numeratorHeight := P.numeratorHeight
  numeratorRank := P.numeratorRank.map φ

/-- The integral isogeny already furnishes an actual presentation with denominator one. -/
def ofIntegral (f : Hom M N) (h : ℕ) (hf : f.HasHeight q h) :
    GlobalHeightPresentation π q (RationalHom.ofHom (F := F) f) where
  toScalarIsogenyPresentation := ScalarIsogenyPresentation.ofIsogeny π f hf.1
  numeratorHeight := h
  numeratorRank := hf.2

@[simp]
theorem index_ofIntegral (f : Hom M N) (h : ℕ) (hf : f.HasHeight q h) :
    (ofIntegral (F := F) (π := π) f h hf).index H = h := by
  change (h : ℤ) - 0 * (H : ℤ) = h
  simp

/-- The denominator and numerator ranks furnish a presentation on every open. -/
def onOpen (P : GlobalHeightPresentation π q z) (hM : M.HasPiHeight π q H)
    (U : Opens (PrimeSpectrum R)) :
    RationalSection.HeightPresentation π q (RationalSection.ofGlobalOn U z) where
  exponent := P.exponent
  representative := P.representative.map (IsScalarTower.toAlgHom O R _)
  numeratorHeight := P.numeratorHeight
  denominatorHeight := P.exponent * H
  numerator := (show P.representative.HasHeight q P.numeratorHeight from
    ⟨P.isIsogeny, P.numeratorRank⟩).map _
  denominator := (hM.map (IsScalarTower.toAlgHom O R _)).scalarPower_height _
  represents := by
    have he := congrArg (RationalSection.ofGlobalOn U) P.represents
    simpa only [map_smul, RationalSection.ofGlobalOn_ofHom, RationalSection.ofHom] using he

@[simp]
theorem index_onOpen (P : GlobalHeightPresentation π q z) (hM : M.HasPiHeight π q H)
    (U : Opens (PrimeSpectrum R)) : (P.onOpen hM U).index = P.index H := by
  simp only [onOpen, RationalSection.HeightPresentation.index, index, Nat.cast_mul]

/-- A global ranked presentation gives the same local rank difference at every point. -/
theorem hasHeightFunction (P : GlobalHeightPresentation π q z)
    (hM : M.HasPiHeight π q H) :
    RationalSection.HasHeightFunction π q (RationalSection.ofGlobal z) (fun _ => P.index H) := by
  intro x
  have he : RationalSection.ofGlobalOn ⊤ z =
      RationalSection.restrict (𝟙 ⊤) (RationalSection.ofGlobal z) :=
    (RationalSection.restrict_ofGlobalOn (𝟙 ⊤) z).symm
  refine ⟨⊤, x.property, 𝟙 _, he ▸ P.onOpen hM ⊤, fun _ => ?_⟩
  exact (P.index_onOpen hM ⊤).symm.trans
    (RationalSection.HeightPresentation.index_cast he (P.onOpen hM ⊤)).symm

/-- The actual inverse tensor has a global presentation of opposite signed height.
Choose the dual exponent large enough for both the scalar denominator and the complementary rank. -/
theorem exists_inverse [IsDomain O] [IsFractionRing O F]
    (P : GlobalHeightPresentation π q z) (hπ : algebraMap O F π ≠ 0)
    (hq : 0 < q) (hH : 0 < H) (hM : M.HasPiHeight π q H) (hN : N.HasPiHeight π q H)
    (e : QuasiIsogeny F M N) (he : e.hom = z) :
    ∃ Q : GlobalHeightPresentation π q e.inv, Q.index H = -P.index H := by
  obtain ⟨k, hdual⟩ := P.isIsogeny.exists_dual hM.piDivisible hN.piDivisible
  let n := P.exponent
  let m := max k P.numeratorHeight
  let j := n + m
  obtain ⟨g, hg, hgf, _hfg⟩ := hdual j ((le_max_left _ _).trans (Nat.le_add_left m n))
  have hi : P.numeratorHeight ≤ j * H := by
    calc
      P.numeratorHeight ≤ m := le_max_right _ _
      _ ≤ j := Nat.le_add_left m n
      _ ≤ j * H := by simpa only [mul_one] using Nat.mul_le_mul_left j (show 1 ≤ H from hH)
  let i := j * H - P.numeratorHeight
  have hadd : P.numeratorHeight + i = j * H := Nat.add_sub_of_le hi
  have hrank : g.HasKernelRank (q ^ i) := by
    obtain ⟨A, hA⟩ := P.numeratorRank
    obtain ⟨B⟩ := hg.2
    obtain ⟨C, hC⟩ := Hom.finiteKernelCompositionStatement M N M
      P.representative g P.isIsogeny.1 A B
    have hc : (g.comp P.representative).HasKernelRank (q ^ (j * H)) := by
      rw [hgf]
      exact hM.scalarPower_rank j
    have hC' := (Hom.hasKernelRank_iff _ C _).mp hc
    refine ⟨B, fun x => Nat.eq_of_mul_eq_mul_left (pow_pos hq P.numeratorHeight) ?_⟩
    calc
      q ^ P.numeratorHeight * B.rank x = C.rank x := by rw [hC x, hA x]
      _ = q ^ (j * H) := hC' x
      _ = q ^ P.numeratorHeight * q ^ i := by rw [← hadd, pow_add]
  let c := algebraMap O F π
  have hn : c ^ n ≠ 0 := pow_ne_zero _ hπ
  have hm : c ^ m ≠ 0 := pow_ne_zero _ hπ
  have hz : z = (c ^ n)⁻¹ • ofHom P.representative := by
    change z = (c ^ P.exponent)⁻¹ • ofHom P.representative
    rw [← P.represents, inv_smul_smul₀ hn]
  have hc : (c ^ m)⁻¹ * ((c ^ n)⁻¹ * c ^ j) = 1 := by
    change (c ^ m)⁻¹ * ((c ^ n)⁻¹ * c ^ (n + m)) = 1
    rw [pow_add, inv_mul_cancel_left₀ hn, inv_mul_cancel₀ hm]
  have hinv : (c ^ m)⁻¹ • (ofHom g : RationalHom F N M) = e.inv := by
    apply e.inv_unique
    rw [he, hz, smul_comp, comp_smul, ← ofHom_comp, hgf, ofHom_scalarHom,
      map_pow, smul_smul, smul_smul, mul_assoc]
    change ((c ^ m)⁻¹ * ((c ^ n)⁻¹ * c ^ j)) • id M = _
    rw [hc, one_smul]
  let Q : GlobalHeightPresentation π q e.inv :=
    { exponent := m
      representative := g
      isIsogeny := hg
      represents := by rw [← hinv, smul_smul, mul_inv_cancel₀ hm, one_smul]
      numeratorHeight := i
      numeratorRank := hrank }
  refine ⟨Q, ?_⟩
  have hcast := congrArg (fun x : ℕ => (x : ℤ)) hadd
  push_cast at hcast
  change (P.numeratorHeight : ℤ) + (i : ℤ) = ((n : ℤ) + (m : ℤ)) * (H : ℤ) at hcast
  change (i : ℤ) - (m : ℤ) * (H : ℤ) =
    -((P.numeratorHeight : ℤ) - (n : ℤ) * (H : ℤ))
  rw [add_mul] at hcast
  linarith

end GlobalHeightPresentation
end RationalHom

namespace BasicAtlas.RationalHom

/-- A global presentation gives the same signed rank on every chart of an actual cover. -/
theorem hasConstantChartHeight_ofGlobal {π : O} {q H : ℕ}
    {z : ModuleLaw.RationalHom F M N} (P : ModuleLaw.RationalHom.GlobalHeightPresentation π q z)
    (hM : M.HasPiHeight π q H) (s : Set R) (hs : Ideal.span s = ⊤) :
    (ofGlobalRationalHom s hs z).HasConstantChartHeight π q (P.index H) := by
  intro A b hb
  let φ : R →ₐ[O] A := IsScalarTower.toAlgHom O R A
  let b' : s := b
  have he := (onChart_ofGlobalRationalHom z s hs A b' hb).trans
    (ModuleLaw.RationalHom.isoTransport_eq_comp
      (globalChartIso M b'.val A hb).symm (globalChartIso N b'.val A hb).symm
      (ModuleLaw.RationalHom.map φ z)).symm
  rw [he]
  exact ((P.map φ).hasHeightFunction (hM.map φ)).ofGlobal_isoTransport
    (globalChartIso M b'.val A hb).symm (globalChartIso N b'.val A hb).symm

end BasicAtlas.RationalHom

end Langlands.FormalGroup.ModuleLaw
