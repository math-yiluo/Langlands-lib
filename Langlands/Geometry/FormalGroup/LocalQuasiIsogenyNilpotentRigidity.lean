import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyNilpotentRigidityStatement
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyInverseAssembly
import Langlands.Geometry.FormalGroup.NilpotentIsogenyLift
import Langlands.Geometry.FormalGroup.NilpotentRationalSection
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Nilpotent rigidity of actual local quasi-isogenies -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

section

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F] [Module.Flat O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

set_option maxHeartbeats 600000 in
/-- Pullback across a nilpotent coefficient thickening is bijective on actual
local quasi-isogenies of scalar-divisible formal laws. -/
theorem LocalQuasiIsogeny.baseChange_bijective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hspec : Function.Surjective (coefficientSpectrumMap φ))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (hc : algebraMap O F π ≠ 0)
    (U : Opens (PrimeSpectrum R)) :
    Function.Bijective (fun z : LocalQuasiIsogeny F π M N U => z.baseChange φ) := by
  classical
  have hinj (V : Opens (PrimeSpectrum R)) :=
    RationalSection.baseChange_injective_of_nilpotent (F := F) φ hφ hI hspec hM hN V
  refine ⟨?_, ?_⟩
  · intro z w he
    apply LocalQuasiIsogeny.ext
    exact hinj U (congrArg LocalQuasiIsogeny.val he)
  intro z₀
  let c := algebraMap O F π
  have hlocal : ∀ x ∈ U, ∃ (r : R) (i : PrimeSpectrum.basicOpen r ⟶ U)
      (w : RationalSection F M N (PrimeSpectrum.basicOpen r)),
        x ∈ PrimeSpectrum.basicOpen r ∧ RationalSection.IsLocallyScalarIsogeny π w ∧
          RationalSection.baseChange φ (PrimeSpectrum.basicOpen r) w =
            RationalSection.restrict ((coefficientOpenMap φ).map i) z₀.val := by
    intro x hx
    obtain ⟨y, rfl⟩ := hspec x
    obtain ⟨W, hyW, i, n, g₀, hg₀, hnum⟩ := z₀.isLocal y hx
    obtain ⟨r, hyB, hBW⟩ := exists_basicOpen_preimage_le φ hφ hyW
    let B := PrimeSpectrum.basicOpen r
    let B' := (coefficientOpenMap φ).obj B
    let j : B' ⟶ W := homOfLE hBW
    let iB : B ⟶ U := homOfLE (coefficientOpenMap_le_of_le φ hspec (hBW.trans i.le))
    let f₀ : OpenIntegralHom (M.map φ) (N.map φ) B' :=
      Hom.algebraMapLinear ((coefficientStructurePresheaf S).map j.op) g₀
    have hf₀ : f₀.IsIsogeny := hg₀.algebraMapLinear _
    have hnumB : c ^ n • RationalSection.restrict ((coefficientOpenMap φ).map iB) z₀.val =
        RationalSection.ofIntegral B' f₀ := by
      have he := congrArg (RationalSection.restrict j) hnum
      have hi : j ≫ i = (coefficientOpenMap φ).map iB := Subsingleton.elim _ _
      simpa only [map_smul, RationalSection.restrict_ofIntegral,
        ← RationalSection.restrict_comp, hi] using he
    obtain ⟨k, f, hf, hred⟩ := hf₀.exists_openBaseChange_eq_smul_basicOpen φ hφ hI hM hN r
    let w : RationalSection F M N B := (c ^ (n + k))⁻¹ • RationalSection.ofIntegral B f
    refine ⟨r, iB, w, hyB,
      RationalSection.IsLocallyScalarIsogeny.inv_pow_smul_ofIntegral π hc (n + k) f hf, ?_⟩
    change RationalSection.baseChange φ B ((c ^ (n + k))⁻¹ • RationalSection.ofIntegral B f) = _
    rw [map_smul, RationalSection.baseChange_ofIntegral, hred, RationalSection.ofIntegral_smul,
      map_pow, ← hnumB, smul_smul (c ^ k), ← pow_add, Nat.add_comm k n,
      smul_smul, inv_mul_cancel₀ (pow_ne_zero (n + k) hc), one_smul]
  choose r i w hxV hloc hw using fun x : U => hlocal x.val x.property
  let V (x : U) := PrimeSpectrum.basicOpen (r x)
  have hcover : U ≤ iSup V := fun x hx => (le_iSup V ⟨x, hx⟩) (hxV ⟨x, hx⟩)
  have hcompat : TopCat.Presheaf.IsCompatible (rationalHomTypeSheaf F M N).obj V w := by
    intro a b
    let ia : V a ⊓ V b ⟶ V a := homOfLE inf_le_left
    let ib : V a ⊓ V b ⟶ V b := homOfLE inf_le_right
    change RationalSection.restrict ia (w a) = RationalSection.restrict ib (w b)
    apply hinj (V a ⊓ V b)
    rw [← RationalSection.restrict_baseChange, ← RationalSection.restrict_baseChange,
      hw a, hw b, ← RationalSection.restrict_comp, ← RationalSection.restrict_comp]
    rfl
  obtain ⟨z, hz, -⟩ := (rationalHomTypeSheaf F M N).existsUnique_gluing' V U i hcover w hcompat
  change RationalSection F M N U at z
  change ∀ a, RationalSection.restrict (i a) z = w a at hz
  have hzlocal : RationalSection.IsLocallyScalarIsogeny π z := by
    apply RationalSection.IsLocallyScalarIsogeny.of_cover V i
      (fun x hx => ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
    intro a
    rw [hz a]
    exact hloc a
  refine ⟨⟨hc, hM, hN, z, hzlocal⟩, ?_⟩
  apply LocalQuasiIsogeny.ext
  change RationalSection.baseChange φ U z = z₀.val
  let V' (a : U) := (coefficientOpenMap φ).obj (V a)
  have hcover' : (coefficientOpenMap φ).obj U ≤ iSup V' := by
    intro y hy
    let a : U := ⟨coefficientSpectrumMap φ y, hy⟩
    exact (le_iSup V' a) (hxV a)
  apply (rationalHomTypeSheaf F (M.map φ) (N.map φ)).eq_of_locally_eq' V' _
    (fun a => (coefficientOpenMap φ).map (i a)) hcover'
  intro a
  change RationalSection.restrict ((coefficientOpenMap φ).map (i a))
      (RationalSection.baseChange φ U z) =
    RationalSection.restrict ((coefficientOpenMap φ).map (i a)) z₀.val
  rw [RationalSection.restrict_baseChange, hz a, hw a]

end

/-- The exact arbitrary-open rigidity statement for nilpotent quotients. -/
theorem localQuasiIsogenyNilpotentRigidity :
    LocalQuasiIsogenyNilpotentRigidityStatement.{v} := by
  intro R _ p hp σ τ _ _ M N I hI hM hN U
  let φ := Ideal.Quotient.mkₐ ℤ I
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker φ.toRingHom) := by
    change IsNilpotent (RingHom.ker (Ideal.Quotient.mk I))
    rwa [Ideal.mk_ker]
  have hspec : Function.Surjective (coefficientSpectrumMap φ) := by
    apply (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical ?_).2
    intro x hx
    obtain ⟨d, hd⟩ := hI
    exact mem_nilradical.mpr ⟨d, by
      have hxd := Ideal.pow_mem_pow hx (n := d)
      rwa [show I ^ d = ⊥ from hd, Ideal.mem_bot] at hxd⟩
  have hc : algebraMap ℤ (ULift.{v} ℚ) (p : ℤ) ≠ 0 := by
    intro he
    have hq : ((p : ℤ) : ℚ) = 0 := congrArg ULift.down he
    exact hp.ne_zero (by exact_mod_cast hq)
  exact LocalQuasiIsogeny.baseChange_bijective_of_nilpotent φ hφ hker hspec hM hN hc U

end Langlands.FormalGroup.ModuleLaw
