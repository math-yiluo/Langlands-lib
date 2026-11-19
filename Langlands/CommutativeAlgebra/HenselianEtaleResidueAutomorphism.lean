import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Etale

/-! # Lifting residue automorphisms of finite étale local algebras -/

noncomputable section

namespace Langlands.HenselianEtale

open IsLocalRing Polynomial

variable {O C : Type*} [CommRing O] [CommRing C] [IsLocalRing O] [HenselianLocalRing C]
  [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [Algebra.Etale O C]
  [IsLocalHom (algebraMap O C)]

private theorem exists_liftResidueAut (σ : ResidueField C ≃ₐ[ResidueField O] ResidueField C) :
    ∃ e : C ≃ₐ[O] C, ∀ x, residue C (e x) = σ (residue C x) := by
  let : Module.Free O C := Module.free_of_flat_of_isLocalRing
  obtain ⟨x, hx⟩ := IsLocalRing.exists_adjoin_eq_top (R := O) (S := C)
  let f := minpoly O x
  let y := σ (residue C x)
  have hcoeff : σ.toRingHom.comp ((algebraMap (ResidueField O) (ResidueField C)).comp
      (residue O)) = (residue C).comp (algebraMap O C) := by
    ext a
    change σ (algebraMap (ResidueField O) (ResidueField C) (residue O a)) =
      residue C (algebraMap O C a)
    rw [σ.commutes]
    rfl
  have heval (P : O[X]) :
      (P.map (algebraMap O C)).eval₂ (residue C) y =
        σ (aeval (residue C x) (P.map (residue O))) := by
    rw [Polynomial.eval₂_map, Polynomial.aeval_def, Polynomial.eval₂_map]
    change _ = σ.toRingHom _
    rw [Polynomial.hom_eval₂, hcoeff]
    rfl
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hfres : f.map (residue O) = minpoly (ResidueField O) (residue C x) :=
    IsLocalRing.minpoly_map_residue hx
  have hroot : (f.map (algebraMap O C)).eval₂ (residue C) y = 0 := by
    rw [heval, hfres, minpoly.aeval, map_zero]
  have hder : (f.map (algebraMap O C)).derivative.eval₂ (residue C) y ≠ 0 := by
    rw [Polynomial.derivative_map, heval, ← Polynomial.derivative_map, hfres, map_ne_zero_iff σ σ.injective]
    exact (Algebra.IsSeparable.isSeparable (ResidueField O) (residue C x)).aeval_derivative_ne_zero
      (minpoly.aeval (ResidueField O) (residue C x))
  have hiff := (HenselianLocalRing.TFAE C).out 1 3
  obtain ⟨z, hz, hzr⟩ := hiff.mp (inferInstance : HenselianLocalRing C)
    (residue C) residue_surjective (f.map (algebraMap O C)) (hf.map _) y hroot hder
  have hz' : aeval z f = 0 := by
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hz
  let presentation := IsAdjoinRootMonic.mkOfAdjoinEqTop' hx
  let b := presentation.toIsAdjoinRoot.liftHom z hz'
  have hb : b x = z := by
    calc
      b x = b presentation.toIsAdjoinRoot.root :=
        congrArg b (IsAdjoinRootMonic.mkOfAdjoinEqTop'_root hx).symm
      _ = z := presentation.toIsAdjoinRoot.liftHom_root hz'
  have hxres := (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top x).mpr hx
  have hzres : Algebra.adjoin (ResidueField O) {residue C z} = ⊤ := by
    rw [hzr, show y = σ.toAlgHom (residue C x) from rfl, ← Set.image_singleton,
      ← AlgHom.map_adjoin, hxres, Algebra.map_top]
    rw [AlgHom.range_eq_top]
    exact σ.surjective
  have hzgen := (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top z).mp hzres
  have hsurj : Function.Surjective b := by
    rw [← AlgHom.range_eq_top]
    calc
      b.range = (⊤ : Subalgebra O C).map b := by rw [Algebra.map_top]
      _ = (Algebra.adjoin O {x}).map b := congrArg (fun S : Subalgebra O C => S.map b) hx.symm
      _ = ⊤ := by rw [AlgHom.map_adjoin, Set.image_singleton, hb, hzgen]
  let e := AlgEquiv.ofBijective b (OrzechProperty.bijective_of_surjective_endomorphism b.toLinearMap hsurj)
  let q := IsScalarTower.toAlgHom O C (ResidueField C)
  have he : q.comp b = (σ.restrictScalars O).toAlgHom.comp q := by
    apply AlgHom.ext_of_adjoin_eq_top hx
    intro a ha
    have ha' : a = x := Set.mem_singleton_iff.mp ha
    subst a
    change residue C (b x) = σ (residue C x)
    rw [hb, hzr]
  exact ⟨e, fun a => DFunLike.congr_fun he a⟩

/-- An actual residue automorphism of a finite étale Henselian local algebra lifts to the algebra. -/
def liftResidueAut (σ : ResidueField C ≃ₐ[ResidueField O] ResidueField C) : C ≃ₐ[O] C :=
  (exists_liftResidueAut σ).choose

@[simp]
theorem residue_liftResidueAut (σ : ResidueField C ≃ₐ[ResidueField O] ResidueField C) (x : C) :
    residue C (liftResidueAut σ x) = σ (residue C x) :=
  (exists_liftResidueAut σ).choose_spec x

end Langlands.HenselianEtale
