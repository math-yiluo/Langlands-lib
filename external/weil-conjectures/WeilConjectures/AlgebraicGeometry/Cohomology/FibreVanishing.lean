/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexExact

/-!
# Vanishing of cohomology near a fibre with vanishing cohomology

Let `f : X ⟶ T` be proper of finite presentation and let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `T`. If `H^q(X_t, ℱ_t) = 0` for a point `t` of `T`, then
`H^q(f⁻¹ V, ℱ) = 0` for every affine open `V` in a neighbourhood of `t`.

Near `t` the higher direct images are computed, compatibly with base change, by a bounded
complex `P` of finite free modules
(`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`). Since
`H^q(P ⊗ κ(t)) = 0`, the ranks of the matrices of `d^{q-1}` and `d^q` at `t` add up to the rank
of `P^q`, so these matrices have invertible minors of complementary sizes near `t`, and `P` is
exact in degree `q` there (`isZero_homology_of_isUnit_det_submatrix`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_preimage_of_hFiber_eq_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X T : Scheme.{u}}

/-- **Vanishing of cohomology near a fibre with vanishing cohomology.** Let `f : X ⟶ T` be
proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation, flat over `T`. If
the fibre cohomology `H^q(X_t, ℱ_t)` vanishes, then `t` has an open neighbourhood `U` such that
`H^q(f⁻¹ V, ℱ) = 0` for every affine open `V ⊆ U`. -/
theorem exists_subsingleton_H_preimage_of_hFiber_eq_zero (f : X ⟶ T) [IsProper f]
    [LocallyOfFinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ : ℱ.IsFlatOver f) (q : ℕ) (t : T) (ht : ℱ.hFiber f q t = 0) :
    ∃ U : T.Opens, t ∈ U ∧ ∀ V : T.Opens, IsAffineOpen V → V ≤ U →
      Subsingleton (((Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ).H q) := by
  classical
  have := isGrothendieckAbelian X
  obtain ⟨U₀, P, d, htU₀, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ t
  choose r e using hP.exists_iso_free
  let e (n : ℤ) := (e n).some
  -- the matrices of the differentials of `P`
  let D (n : ℤ) := (e n).inv ≫ P.d n (n + 1) ≫ (e (n + 1)).hom
  -- at `t`, their ranks add up to the rank of `P^q`
  obtain ⟨g₀, hg₀⟩ := exists_comp_ι_eq_fromSpecResidueField htU₀
  have hR : IsField (T.residueField t) := Field.toIsField _
  have hrank := finrank_homology_pullback_add_rank_add_rank e hR g₀ q
  rw [← hFiber_eq_finrank_homology f ℱ hbc g₀ hg₀ q, ht, zero_add] at hrank
  obtain ⟨x⟩ : Nonempty (Spec (T.residueField t)) := inferInstance
  have hRΓ : IsField Γ(Spec (T.residueField t), ⊤) := isField_Γ_Spec hR
  obtain ⟨b₁, b₂, hb⟩ := (le_rank_map_appTop_iff hRΓ g₀ x (freeMatrix (D q)) _).mp le_rfl
  have hq : (q : ℤ) - 1 + 1 = q := by ring
  obtain ⟨a₁, a₂, ha⟩ := (le_rank_map_appTop_iff hRΓ g₀ x
    (freeMatrix ((e ((q : ℤ) - 1)).inv ≫ P.d ((q : ℤ) - 1) q ≫ (e q).hom)) _).mp le_rfl
  set δa := ((freeMatrix ((e ((q : ℤ) - 1)).inv ≫ P.d ((q : ℤ) - 1) q ≫ (e q).hom)).submatrix
    a₁ a₂).det
  set δb := ((freeMatrix (D q)).submatrix b₁ b₂).det
  refine ⟨U₀.ι ''ᵁ (U₀.toScheme.basicOpen δa ⊓ U₀.toScheme.basicOpen δb), ?_, fun V hV hVU ↦ ?_⟩
  · refine ⟨g₀.base x, ⟨ha, hb⟩, ?_⟩
    change (g₀ ≫ U₀.ι).base x = t
    rw [hg₀]
    exact Scheme.fromSpecResidueField_apply t x
  -- restrict to an affine open `V` inside the locus where the two minors are units
  have hVU₀ : V ≤ U₀ := fun v hv ↦ by
    obtain ⟨w, -, hw⟩ := hVU hv
    rw [← hw]
    exact w.2
  set g := T.homOfLE hVU₀
  have hrange : Set.range g.base ⊆ U₀.toScheme.basicOpen δa ⊓ U₀.toScheme.basicOpen δb := by
    rintro _ ⟨v, rfl⟩
    have hv : (V.ι v) ∈ U₀.ι ''ᵁ (U₀.toScheme.basicOpen δa ⊓ U₀.toScheme.basicOpen δb) :=
      hVU v.2
    obtain ⟨w, hw, hwv⟩ := hv
    have : w = g.base v := U₀.ι.isOpenEmbedding.injective (hwv.trans (by
      change V.ι.base v = (g ≫ U₀.ι).base v
      rw [Scheme.homOfLE_ι]))
    exact this ▸ hw
  have hunit (δ : Γ(U₀.toScheme, ⊤)) (hδ : Set.range g.base ⊆ U₀.toScheme.basicOpen δ) :
      IsUnit (g.appTop δ) := by
    refine Scheme.isUnit_of_basicOpen_eq_top _ ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact eq_top_iff.mpr fun v _ ↦ hδ ⟨v, rfl⟩
  -- the pulled-back complex is exact in degree `q`
  let Q := ((Modules.pullback g).mapHomologicalComplex _).obj P
  let e' (n : ℤ) : Q.X n ≅ SheafOfModules.free (ULift.{u} (Fin (r n))) :=
    (Modules.pullback g).mapIso (e n) ≪≫ pullbackFreeIso g _
  have hD (n m : ℤ) : (e' n).inv ≫ Q.d n m ≫ (e' m).hom = (pullbackFreeIso g _).inv ≫
      (Modules.pullback g).map ((e n).inv ≫ P.d n m ≫ (e m).hom) ≫ (pullbackFreeIso g _).hom := by
    simp [e', Q]
  have hQ : IsZero (Q.homology q) := by
    refine isZero_homology_of_isUnit_det_submatrix Q e' q a₁ a₂ ?_ b₁ b₂ ?_ ?_
    · have h := hunit _ (hrange.trans inf_le_left)
      rw [RingHom.map_det] at h
      convert h using 3
      rw [hD, freeMatrix_pullback]
      rfl
    · have h := hunit _ (hrange.trans inf_le_right)
      rw [RingHom.map_det] at h
      convert h using 3
      rw [hD, freeMatrix_pullback]
      rfl
    · simp only [Fintype.card_fin]
      exact (add_comm _ _).trans hrank
  -- hence the higher direct image over `V` and the cohomology over `f⁻¹ V` vanish
  have := isGrothendieckAbelian (f ⁻¹ᵁ V).toScheme
  have sq : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f (g ≫ U₀.ι) := by
    rw [Scheme.homOfLE_ι]
    exact (isPullback_morphismRestrict f V).flip
  obtain ⟨iso⟩ := hbc g (f ⁻¹ᵁ V).ι (f ∣_ V) sq q
  have : IsAffine V.toScheme := hV
  have : SheafOfModules.IsQuasicoherent (R := (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
      ((Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ) := by
    have : ℱ.IsQuasicoherent := inferInstance
    infer_instance
  obtain ⟨e₂⟩ := nonempty_sections_higherDirectImage_iso_H (f ∣_ V)
    ((Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ) q
  have hz : IsZero ((higherDirectImage (f ∣_ V) q).obj ((Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ)) :=
    hQ.of_iso iso.symm
  refine ⟨fun a b ↦ e₂.symm.injective ?_⟩
  have : Subsingleton Γ((higherDirectImage (f ∣_ V) q).obj
      ((Modules.pullback (f ⁻¹ᵁ V).ι).obj ℱ), ⊤) :=
    ModuleCat.subsingleton_of_isZero ((SheafOfModules.evaluation _ _).map_isZero hz)
  exact Subsingleton.elim _ _

end Scheme.Modules

end AlgebraicGeometry
