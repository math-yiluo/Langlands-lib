import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageStatement
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.CentralIsogeny.PowerLift
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Torus.ImageProof
import Langlands.GroupScheme.ImageGenerationDominant
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Proof: central isogenies carry maximal tori onto maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- If a nonzero multiple of a homomorphism from a torus factors through a closed subgroup, the
homomorphism itself factors through it. -/
theorem exists_factor_of_multiplication_comp {P : CommGroupScheme (Spec (CommRingCat.of k))}
    {G Z : GroupScheme (Spec (CommRingCat.of k))} (hP : IsTorus P.toGrp) {n : ℤ} (hn : n ≠ 0)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (φ : P.toGrp ⟶ G) (ψ : P.toGrp ⟶ Z)
    (h : multiplication P.toGrp n ≫ φ = ψ ≫ z) : ∃ φ' : P.toGrp ⟶ Z, φ' ≫ z = φ := by
  have : IsClosedImmersion z.hom.hom.left := hz
  have : IsIntegral P.X.left := hP.isIntegral
  have : Surjective (multiplication P.toGrp n).hom.hom.left :=
    (hP.flat_and_surjective_multiplication hn).2
  have : IsSchemeTheoreticallyDominant (multiplication P.toGrp n).hom.hom.left :=
    .of_isDominant _
  have h' : (multiplication P.toGrp n).hom.hom ≫ φ.hom.hom = ψ.hom.hom ≫ z.hom.hom :=
    congrArg (fun m => m.hom.hom) h
  obtain ⟨a, ha⟩ := exists_over_factor_of_schematic_precomp z.hom.hom
    (multiplication P.toGrp n).hom.hom φ.hom.hom ψ.hom.hom h'
  have hrep : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range φ ≤ SubgroupFunctor.range z := by
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ a, by rw [Category.assoc, ha]⟩
  exact ⟨hrep.factorHom φ hle, hrep.factorHom_comp φ hle⟩

/-- A central isogeny of connected reductive groups carries a maximal torus onto a maximal
torus. -/
theorem centralIsogenyMaximalTorusImage : CentralIsogenyMaximalTorusImageStatement.{u} := by
  intro k _ G H hG hH π hπ T S i j f hi hS hj hf hsq
  refine ⟨hS, hj, ?_⟩
  intro S' j' g hS' hj' hg
  have := hG.smooth
  have := hG.isAffineHom
  have : IsFinite π.hom.hom.left := hπ.isFinite
  have : Flat π.hom.hom.left := hπ.flat
  have : Surjective π.hom.hom.left := hπ.surjective
  -- A uniform exponent of the central kernel.
  obtain ⟨N, hNpos, hNker⟩ := hπ.exists_pow_eq_one_kernel
  have hc : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X), x ≫ π.hom.hom = 1 →
      x ∈ (center G).carrier U := fun U x hx => hπ.mem_center_of_comp_eq_one hx
  have hN : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X), x ≫ π.hom.hom = 1 →
      x ^ N = 1 := by
    intro U x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff π x).mpr hx)
    rw [← hy, ← MonObj.pow_comp, hNker U y, MonObj.one_comp]
  -- A homomorphic lift of a multiple of `j'`, and its closed torus image in `G`.
  obtain ⟨Φ, hΦ⟩ := CentralPowerLift.exists_comp_eq_multiplication_comp (π := π) j' hc hN
  obtain ⟨Z, z, e, hZ, hz, hez⟩ := torusImageClosedTorusStatement k G S'.toGrp hS' Φ
  -- A multiple of `i` factors through the closed torus `Z`.
  have key : multiplication T.toGrp (N : ℤ) ≫ (CommGroupScheme.groupHom f ≫ g ≫ Φ) =
      multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i := by
    -- `c` and `[2N] ≫ i` agree after `π`.
    have hcπ : (CommGroupScheme.groupHom f ≫ g ≫ Φ) ≫ π =
        (multiplication T.toGrp ((2 * N : ℕ) : ℤ) ≫ i) ≫ π := by
      rw [Category.assoc, Category.assoc, hΦ, ← Category.assoc g,
        ← multiplication_naturality g, Category.assoc, hg, ← Category.assoc,
        ← multiplication_naturality (CommGroupScheme.groupHom f), Category.assoc,
        Category.assoc, ← hsq]
    apply Grp.hom_ext
    rw [← Category.id_comp ((multiplication T.toGrp (N : ℤ) ≫ _).hom.hom),
      ← Category.id_comp ((multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i).hom.hom)]
    set x := 𝟙 T.toGrp.X
    let a := x ≫ (CommGroupScheme.groupHom f ≫ g ≫ Φ).hom.hom
    let b := x ≫ (multiplication T.toGrp ((2 * N : ℕ) : ℤ) ≫ i).hom.hom
    have hab : a ≫ π.hom.hom = b ≫ π.hom.hom := by
      simp only [a, b, Category.assoc, ← Grp.comp_hom_hom, hcπ]
    -- Their difference lies in the central kernel, which `N` kills.
    have hd : (a * b⁻¹) ≫ π.hom.hom = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hab, mul_inv_cancel]
    have hcomm : Commute (a * b⁻¹) b := commute_of_mem_center (hc _ _ hd) b
    have hpow : a ^ N = b ^ N := by
      have ha : a = (a * b⁻¹) * b := by rw [inv_mul_cancel_right]
      rw [ha, hcomm.mul_pow, hN _ _ hd, one_mul]
    have hL : x ≫ (multiplication T.toGrp (N : ℤ) ≫
        (CommGroupScheme.groupHom f ≫ g ≫ Φ)).hom.hom = a ^ N := by
      rw [Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast,
        MonObj.pow_comp]
    have hR : x ≫ (multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i).hom.hom = b ^ N := by
      simp only [b, Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast,
        MonObj.pow_comp]
      rw [← pow_mul]
    rw [hL, hR, hpow]
  have hN0 : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have h2N0 : ((2 * N * N : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨i', hi'⟩ := exists_factor_of_multiplication_comp hi.1 h2N0 z hz i
    (multiplication T.toGrp (N : ℤ) ≫ CommGroupScheme.groupHom f ≫ g ≫ e)
    (by rw [← key, ← hez]; simp only [Category.assoc])
  have : IsIso i' := hi.2.2 Z z i' hZ hz hi'
  -- Hence a multiple of `j'` factors through `j`.
  have hΦi : Φ = (e ≫ inv i') ≫ i := by
    rw [← hez, ← hi', Category.assoc, IsIso.inv_hom_id_assoc]
  have h2 : multiplication S'.toGrp ((2 * N : ℕ) : ℤ) ≫ j' =
      (e ≫ inv i' ≫ CommGroupScheme.groupHom f) ≫ j := by
    rw [← hΦ, hΦi, Category.assoc, Category.assoc, hsq]
    simp only [Category.assoc]
  have h2N0' : ((2 * N : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨h', hh'⟩ := exists_factor_of_multiplication_comp hS' h2N0' j hj j'
    (e ≫ inv i' ≫ CommGroupScheme.groupHom f) h2
  -- `g` is an isomorphism with inverse `h'`.
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have hjm : Mono j.hom.hom := Over.mono_of_mono_left _
  have hj'm : Mono j'.hom.hom := Over.mono_of_mono_left _
  refine ⟨h', ?_, ?_⟩
  · apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hh', hg, Category.id_comp]
  · apply Grp.hom_ext
    apply (cancel_mono j'.hom.hom).mp
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc, hg, hh', Category.id_comp]

end Langlands.GroupScheme
