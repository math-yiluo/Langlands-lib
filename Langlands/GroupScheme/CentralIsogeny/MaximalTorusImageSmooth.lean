import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageProof
import Langlands.GroupScheme.Torus.FiniteImage

/-! # Maximal-torus images under central isogenies of smooth affine groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))} {π : G ⟶ H}

namespace IsCentralIsogeny

/-- A central isogeny from a smooth affine group carries a maximal torus `i : T ⟶ G` to a
maximal torus: every closed torus `j : S ⟶ H` with `i ≫ π = f ≫ j` is maximal. Neither group
needs to be reductive or connected, and `f` need not be surjective. -/
theorem isMaximalTorus_of_comp_eq [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hπ : IsCentralIsogeny π) {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {j : S.toGrp ⟶ H} (f : T.toGrp ⟶ S.toGrp) (hi : IsMaximalTorus i)
    (hS : IsTorus S.toGrp) (hj : IsClosedSubgroup j) (hsq : i ≫ π = f ≫ j) :
    IsMaximalTorus j := by
  refine ⟨hS, hj, ?_⟩
  intro S' j' g hS' hj' hg
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
  have key : multiplication T.toGrp (N : ℤ) ≫ (f ≫ g ≫ Φ) =
      multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i := by
    -- `c` and `[2N] ≫ i` agree after `π`.
    have hcπ : (f ≫ g ≫ Φ) ≫ π = (multiplication T.toGrp ((2 * N : ℕ) : ℤ) ≫ i) ≫ π := by
      rw [Category.assoc, Category.assoc, hΦ, ← Category.assoc g,
        ← multiplication_naturality g, Category.assoc, hg, ← Category.assoc,
        ← multiplication_naturality f, Category.assoc, Category.assoc, ← hsq]
    apply Grp.hom_ext
    rw [← Category.id_comp ((multiplication T.toGrp (N : ℤ) ≫ _).hom.hom),
      ← Category.id_comp ((multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i).hom.hom)]
    set x := 𝟙 T.toGrp.X
    let a := x ≫ (f ≫ g ≫ Φ).hom.hom
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
    have hL : x ≫ (multiplication T.toGrp (N : ℤ) ≫ (f ≫ g ≫ Φ)).hom.hom = a ^ N := by
      rw [Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast,
        MonObj.pow_comp]
    have hR : x ≫ (multiplication T.toGrp ((2 * N * N : ℕ) : ℤ) ≫ i).hom.hom = b ^ N := by
      simp only [b, Grp.comp_hom_hom, ← Category.assoc, points_multiplication, zpow_natCast,
        MonObj.pow_comp]
      rw [← pow_mul]
    rw [hL, hR, hpow]
  have h2N0 : ((2 * N * N : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨i', hi'⟩ := exists_factor_of_multiplication_comp hi.1 h2N0 z hz i
    (multiplication T.toGrp (N : ℤ) ≫ f ≫ g ≫ e)
    (by rw [← key, ← hez]; simp only [Category.assoc])
  have : IsIso i' := hi.2.2 Z z i' hZ hz hi'
  -- Hence a multiple of `j'` factors through `j`.
  have hΦi : Φ = (e ≫ inv i') ≫ i := by
    rw [← hez, ← hi', Category.assoc, IsIso.inv_hom_id_assoc]
  have h2 : multiplication S'.toGrp ((2 * N : ℕ) : ℤ) ≫ j' = (e ≫ inv i' ≫ f) ≫ j := by
    rw [← hΦ, hΦi, Category.assoc, Category.assoc, hsq]
    simp only [Category.assoc]
  have h2N0' : ((2 * N : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨h', hh'⟩ := exists_factor_of_multiplication_comp hS' h2N0' j hj j' (e ≫ inv i' ≫ f) h2
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

/-- A central isogeny `π : G ⟶ H` from a smooth affine group carries each maximal torus
`i : T ⟶ G` onto a maximal torus `j : S ⟶ H` of `H`: the actual schematic image of `i ≫ π`.
The induced map `f : T ⟶ S` is an isogeny, hence flat, surjective and quasi-compact. -/
theorem exists_isMaximalTorus_image [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] (hπ : IsCentralIsogeny π)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (j : S.toGrp ⟶ H)
      (f : T.toGrp ⟶ S.toGrp),
      IsMaximalTorus j ∧ i ≫ π = f ≫ j ∧ IsIsogeny f ∧ Flat f.hom.hom.left ∧
        Surjective f.hom.hom.left ∧ QuasiCompact f.hom.hom.left := by
  have : IsFinite π.hom.hom.left := hπ.isFinite
  obtain ⟨S, j, f, hS, hj, hf, hfj, -⟩ := hi.1.exists_isogeny_finiteHomImage i hi.2.1 π
  have : IsFinite f.hom.hom.left := hf.1
  exact ⟨S, j, f, hπ.isMaximalTorus_of_comp_eq f hi hS hj hfj.symm, hfj.symm, hf, hf.2.1,
    hf.2.2, inferInstance⟩

end IsCentralIsogeny

/-- Statement form of this module. Let `π : G ⟶ H` be a central isogeny of group schemes over a
field `k`, with `G` smooth and affine. (1) If `i : T ⟶ G` is a maximal torus, `j : S ⟶ H` a closed
subgroup with `S` a torus, and `f : T ⟶ S` a homomorphism with `i ≫ π = f ≫ j`, then `j` is a
maximal torus. (2) If `H` is also affine and locally of finite type, every maximal torus
`i : T ⟶ G` has such a maximal torus `j : S ⟶ H` and homomorphism `f`, where `f` is an isogeny
whose underlying morphism is flat, surjective and quasi-compact. -/
def CentralIsogenySmoothMaximalTorusImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))) (π : G ⟶ H)
    [Smooth G.X.hom] [IsAffineHom G.X.hom], IsCentralIsogeny π →
    (∀ (T S : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (j : S.toGrp ⟶ H)
        (f : T.toGrp ⟶ S.toGrp), IsMaximalTorus i → IsTorus S.toGrp → IsClosedSubgroup j →
          i ≫ π = f ≫ j → IsMaximalTorus j) ∧
      (∀ [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
        (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
          ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (j : S.toGrp ⟶ H)
            (f : T.toGrp ⟶ S.toGrp), IsMaximalTorus j ∧ i ≫ π = f ≫ j ∧ IsIsogeny f ∧
              Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧ QuasiCompact f.hom.hom.left)

/-- Proof of `CentralIsogenySmoothMaximalTorusImageStatement`. -/
theorem centralIsogenySmoothMaximalTorusImage :
    CentralIsogenySmoothMaximalTorusImageStatement.{u} :=
  fun _ _ _ _ _ _ _ hπ =>
    ⟨fun _ _ _ _ f hi hS hj hsq => hπ.isMaximalTorus_of_comp_eq f hi hS hj hsq,
      fun _ _ hi => hπ.exists_isMaximalTorus_image hi⟩

end Langlands.GroupScheme
