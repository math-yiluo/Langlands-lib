/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero

/-! # A projective-line cohomology generator with finite constant coefficients

Source: the proper-curve cohomology calculation and the structure theorem for finite
abelian groups, blueprint lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem p1_h2_reduction_surjective
    (k : Type u) [Field k] [IsAlgClosed k]
    {A B : AddCommGrpCat.{u + 1}} (r : A ⟶ B) [Epi r]
    (n : ℕ) (hn : 0 < n) (hA : n • 𝟙 A = 0) :
    Function.Surjective (Sheaf.H.map
      ((constantSheaf (ProjectiveLine (Spec (.of k))).smallEtaleTopology
        AddCommGrpCat.{u + 1}).map r) 2) := by
  let P := ProjectiveLine (Spec (.of k))
  let S := ShortComplex.mk (kernel.ι r) r (kernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel r) }
  have hS' := hS.map_of_exact (constantSheaf P.smallEtaleTopology AddCommGrpCat.{u + 1})
  have hK : n • 𝟙 (kernel r) = 0 := by
    rw [← cancel_mono (kernel.ι r), Preadditive.nsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id (kernel.ι r), ← Preadditive.comp_nsmul, hA, comp_zero]
  obtain ⟨hcurve, -, -, -, -⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have hz := IsCurve.subsingleton_sheafH_of_three_le (P ↘ Spec (.of k))
    ((constantSheaf P.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (kernel r))
    (isTorsion_constantSheaf' P (kernel r) hn hK) 3 le_rfl
  intro y
  exact (Sheaf.H.exact_map_δSucc hS' 2 y).1 (@Subsingleton.elim _ hz _ _)

private theorem p1_constant_cyclic_h2
    (k : Type u) [Field k] [IsAlgClosed k] (m : ℕ) (hm : (m : k) ≠ 0) :
    Nonempty (Sheaf.H ((ProjectiveLine (Spec (.of k))).constantZMod m) 2 ≃+ ZMod m) := by
  obtain ⟨hcurve, hsmooth, hproper, -, -⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have := hsmooth
  have := hproper
  exact (IsConnectedCurve.sheafH_constantZMod_of_isProper
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) m hm).2.2.1

private theorem p1_generator_cyclic
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : (n : k) ≠ 0)
    (θ : Sheaf.H ((ProjectiveLine (Spec (.of k))).constantZMod n) 2)
    (hθ : ∀ y, ∃ c : ℕ, y = c • θ) (m : ℕ) (hm : m ∣ n) :
    Function.Bijective ((sheafHConstantSheafNatTrans
      (ProjectiveLine (Spec (.of k))) n 2 θ).app
        (.of (ULift.{u + 1} (ZMod m)))) := by
  have : NeZero n := ⟨fun h ↦ hn (by simp [h])⟩
  have hm' := AffineSpace.natCast_ne_zero_of_dvd hm hn
  have : NeZero m := ⟨fun h ↦ hm' (by simp [h])⟩
  let P := ProjectiveLine (Spec (.of k))
  let η := sheafHConstantSheafNatTrans P n 2 θ
  let r := AffineSpace.zmodReduction.{u} hm
  have hr : Epi r := by
    rw [AddCommGrpCat.epi_iff_surjective]
    rintro ⟨b⟩
    obtain ⟨a, rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom hm (ZMod m)) b
    exact ⟨ULift.up a, rfl⟩
  have hg : ∀ y : Sheaf.H (P.constantZMod m) 2,
      ∃ c : ℕ, y = c • (η.app _).hom r := by
    intro y
    obtain ⟨x, rfl⟩ := p1_h2_reduction_surjective k r n
      (AffineSpace.pos_of_natCast_ne_zero hn) (AffineSpace.nsmul_id_zmod n) y
    obtain ⟨c, rfl⟩ := hθ x
    exact ⟨c, by rw [map_nsmul]; rfl⟩
  obtain ⟨e⟩ := p1_constant_cyclic_h2 k m hm'
  obtain ⟨c₀, hc₀⟩ := hg (e.symm 1)
  have h2 : e (c₀ • (η.app _).hom r) = 1 := by
    rw [← hc₀, AddEquiv.apply_symm_apply]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro φ hφ0
    rw [AffineSpace.eq_nsmul_zmodReduction hm φ] at hφ0 ⊢
    set c := (φ.hom (ULift.up 1)).down.val
    rw [map_nsmul] at hφ0
    have h1 : (c : ZMod m) = 0 := by
      calc (c : ZMod m) = c • e (c₀ • (η.app _).hom r) := by
            rw [h2, nsmul_eq_mul, mul_one]
           _ = e (c₀ • (c • (η.app _).hom r)) := by rw [← map_nsmul, smul_comm]
           _ = 0 := by rw [hφ0, smul_zero, map_zero]
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun ⟨a⟩ ↦ ULift.ext ?_)
    change c • (ZMod.castHom hm (ZMod m) a) = (0 : ZMod m)
    rw [nsmul_eq_mul, h1, zero_mul]
  · intro y
    obtain ⟨c, rfl⟩ := hg y
    exact ⟨c • r, by rw [map_nsmul]⟩

/-- A generator of H²(P¹,Z/n) induces the canonical coefficient classification
Hom(Z/n,A) ≃ H²(P¹,A) for every finite abelian group A killed by n.
Source: proper-curve cohomology and finite abelian group decomposition, blueprint
lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).

Proof: for m dividing n, the coefficient reduction Z/n -> Z/m induces a surjection
on H² because H³ of its torsion kernel vanishes on a curve. Thus the image of θ
generates H²(P¹,Z/m). This latter group is cyclic of order m, so multiplication
by this generator identifies Hom(Z/n,Z/m) with it. Naturality and additivity
extend this identification over the finite direct-sum decomposition of A into
cyclic groups whose orders divide n. The argument includes m=1 and A=0. -/
theorem projectiveLine_constant_coefficient_generator
    (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : (n : k) ≠ 0)
    (θ : Sheaf.H ((ProjectiveLine (Spec (.of k))).constantZMod n) 2)
    (hθ : ∀ y, ∃ c : ℕ, y = c • θ)
    (A : AddCommGrpCat.{u + 1}) [Finite A] (hA : ∀ a : A, n • a = 0) :
    Function.Bijective ((sheafHConstantSheafNatTrans
      (ProjectiveLine (Spec (.of k))) n 2 θ).app A) :=
  NatTrans.bijective_app_of_zmod _ n
    (fun m hm ↦ p1_generator_cyclic k n hn θ hθ m hm) A hA

end AlgebraicGeometry.Etale
