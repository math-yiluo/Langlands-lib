/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Coordinates for base change on compatible affine charts

Source: Stacks Project, Tags 02KG and 01I9.
(blueprint: lem-weil-pbc-affine-base-change-chart-coordinates).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem source_chart_unit_comparison {S S' : Scheme.{u}}
    (g : S' ⟶ S) (G : S.Modules) [G.IsQuasicoherent]
    (U : S.Opens) (hU : IsAffineOpen U)
    (W : S'.Opens) (hW : IsAffineOpen W) (hWU : W ≤ g ⁻¹ᵁ U) :
    letI : Algebra Γ(S, U) Γ(S', W) := (g.appLE U W hWU).hom.toAlgebra
    ∃ a : Γ((tensorPullback g).obj G, W) ≃ₗ[Γ(S', W)]
        Γ(S', W) ⊗[Γ(S, U)] Γ(G, U),
      ∀ m : Γ(G, U), a.symm ((1 : Γ(S', W)) ⊗ₜ[Γ(S, U)] m) =
        ((tensorPullback g).obj G).presheaf.map (homOfLE hWU).op
          (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app G).app U m) := by
  classical
  let : Algebra Γ(S, U) Γ(S', W) := (g.appLE U W hWU).hom.toAlgebra
  obtain ⟨c, hc, hs, ht, _⟩ := exists_tensorPullback_affine_sections
    g ⟨U, hU⟩ ⟨W, hW⟩ hWU
  let d := TensorProduct.comm Γ(S, U) Γ(S', W) Γ(G, U)
  let e : Γ(S', W) ⊗[Γ(S, U)] Γ(G, U) →ₗ[Γ(S', W)]
      Γ((tensorPullback g).obj G, W) :=
    { toFun := fun t ↦ c G inferInstance (d t)
      map_add' := by intros; simp only [map_add]
      map_smul' := by
        intro r t
        have h := hs G inferInstance r (d t)
        simpa only [d, TensorProduct.comm_comm, TensorProduct.comm_symm,
          RingHom.id_apply] using h }
  let j := LinearEquiv.ofBijective e ((hc G inferInstance).comp d.bijective)
  refine ⟨j.symm, ?_⟩
  intro m
  change c G inferInstance (m ⊗ₜ[Γ(S, U)] (1 : Γ(S', W))) = _
  have h := ht G inferInstance m (1 : Γ(S', W))
  simp only [one_smul] at h
  with_unfolding_all exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Target chart tensor coordinates normalized by the pullback unit of g'.
Source: Stacks Project, Tags 02KG (reduction to spectra), 01I9 (1),(2),
01I4 (affine fibre products), and 08HY (pushforward composition identifications).

Proof: Put V = f⁻¹U and V' = f'⁻¹W. The square implies V' ≤ g'⁻¹V.
Affineness of f and its base change makes V and V' affine. Restrict the square
and use the canonical spectrum presentations of U, V and W. The fibre-product
spectrum isomorphism identifies Γ(X',V') with D = R' tensor_R B, respecting
the maps from R' and B. Apply exists_tensorPullback_affine_sections to g',
V, V' and F. Swap its tensor factors and transport the first factor through
the section-ring isomorphism to obtain the required equivalence from sections
to D tensor_B M. Its linearity over Γ(X',V') implies R'-linearity after
restriction of scalars along f'. On ((1 tensor z) tensor m), the balancing
relation gives ((1 tensor 1) tensor (z*m)). The pure-tensor unit formula of
the affine-sections theorem identifies its image with eta_g'(z*m) restricted
to V'. On the other hand, k.app U is eta_g' on V, followed by the identity
pushforward composition maps and the restriction along the equality of
inverse-image opens from sq.w. Functoriality of restriction identifies its
restriction to W with that same section on V', proving the normalization.
This constructs only the target coordinates; it makes no assertion about
the source coordinates or beta. Empty V' has zero section ring and zero
sections, and the spectrum/tensor argument applies unchanged. If F is zero,
all section maps and both tensor modules are zero as required. -/
private theorem exists_affineBaseChange_target_chart_unit_comparison {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsAffineOpen U)
    (W : S'.Opens) (hW : IsAffineOpen W) (hWU : W ≤ g ⁻¹ᵁ U) :
    let R := Γ(S, U)
    let B := Γ(X, f ⁻¹ᵁ U)
    let R' := Γ(S', W)
    let M := Γ(F, f ⁻¹ᵁ U)
    letI : Algebra R B := (f.app U).hom.toAlgebra
    letI : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    let Q := (pushforward f').obj ((tensorPullback g').obj F)
    let k := (pushforward f).map
      ((Classical.choose (exists_tensorPullbackAdjunction g')).unit.app F) ≫
      (pushforwardComp g' f).hom.app ((tensorPullback g').obj F) ≫
      (pushforwardCongr sq.w).hom.app ((tensorPullback g').obj F) ≫
      (pushforwardComp f' g).inv.app ((tensorPullback g').obj F)
    ∃ b : Γ(Q, W) ≃ₗ[R'] (R' ⊗[R] B) ⊗[B] M,
      ∀ (z : B) (m : M), b.symm (((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m) =
        Q.presheaf.map (homOfLE hWU).op (k.app U (z • m)) := by
  classical
  let R := Γ(S, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let R' := Γ(S', W)
  let M := Γ(F, f ⁻¹ᵁ U)
  let : Algebra R B := (f.app U).hom.toAlgebra
  let : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
  let : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let V := f ⁻¹ᵁ U
  let V' := f' ⁻¹ᵁ W
  have hV : IsAffineOpen V := hU.preimage f
  have : IsAffineHom f' := MorphismProperty.of_isPullback sq inferInstance
  have hV' : IsAffineOpen V' := hW.preimage f'
  have hsub : V' ≤ g' ⁻¹ᵁ V := by
    dsimp only [V', V]
    rw [← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage]
    exact f'.preimage_mono hWU
  have hinf : V' = g' ⁻¹ᵁ V ⊓ f' ⁻¹ᵁ W := (inf_eq_right.mpr hsub).symm
  have hiso := isIso_pushoutSection_of_isAffineOpen sq hWU (le_rfl : V ≤ f ⁻¹ᵁ U)
    hinf hU hW hV
  have hp := (isIso_pushoutSection_iff sq hWU (le_rfl : V ≤ f ⁻¹ᵁ U) hinf).mp hiso
  simp only [V, V', ← Scheme.Hom.app_eq_appLE] at hp
  let C := Γ(X', V')
  let p := g'.appLE V V' hsub
  let q := f'.app W
  let : Algebra B C := p.hom.toAlgebra
  let : Algebra R' C := q.hom.toAlgebra
  let : Algebra R C := (q.hom.comp (g.appLE U W hWU).hom).toAlgebra
  have : IsScalarTower R R' C := IsScalarTower.of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change q.hom ((g.appLE U W hWU).hom r) = p.hom ((f.app U).hom r)
    have h := congr($(hp.w).hom r)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, p, q, V, V'] using h.symm
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R' C)) (CommRingCat.ofHom (algebraMap B C)) := by
    with_unfolding_all exact hp.flip
  have : Algebra.IsPushout R R' B C := CommRingCat.isPushout_iff_isPushout.mp hpush
  let e := Algebra.IsPushout.equiv R R' B C
  have he (z : B) : e ((1 : R') ⊗ₜ[R] z) = p.hom z := by
    have h := Algebra.IsPushout.equiv_tmul R R' B C 1 z
    simp only [map_one, one_mul] at h
    with_unfolding_all exact h
  let eb : (R' ⊗[R] B) ≃ₐ[B] C :=
    { e.toRingEquiv with
      commutes' := fun z ↦ he z }
  obtain ⟨aC, haC⟩ := source_chart_unit_comparison g' F V hV V' hV' hsub
  let a₁ : Γ((tensorPullback g').obj F, V') ≃ₗ[C] C ⊗[B] M := aC
  let t := TensorProduct.congr eb.toLinearEquiv (LinearEquiv.refl B M)
  let j := t.toAddEquiv.trans a₁.symm.toAddEquiv
  let : Module R' Γ((tensorPullback g').obj F, V') :=
    Module.compHom _ q.hom
  let c : (R' ⊗[R] B) ⊗[B] M ≃ₗ[R']
      Γ((pushforward f').obj ((tensorPullback g').obj F), W) :=
    j.toLinearEquiv (by
      intro r x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul d m =>
        change a₁.symm (e (r • d) ⊗ₜ[B] m) = r • a₁.symm (e d ⊗ₜ[B] m)
        have hs : e (r • d) = q.hom r • e d := by
          with_unfolding_all exact e.toLinearEquiv.map_smul r d
        rw [hs]
        change a₁.symm ((q.hom r • e d) ⊗ₜ[B] m) =
          q.hom r • a₁.symm (e d ⊗ₜ[B] m)
        rw [← TensorProduct.smul_tmul', a₁.symm.map_smul])
  refine ⟨c.symm, ?_⟩
  intro z m
  change a₁.symm (e ((1 : R') ⊗ₜ[R] z) ⊗ₜ[B] m) = _
  rw [he]
  have hbalance : p.hom z ⊗ₜ[B] m = (1 : C) ⊗ₜ[B] (z • m) := by
    have h := TensorProduct.smul_tmul (R := B) z (1 : C) m
    simp only [Algebra.smul_def, mul_one] at h
    with_unfolding_all exact h
  rw [hbalance]
  have hn := haC (z • m)
  change a₁.symm ((1 : C) ⊗ₜ[B] (z • m)) = _ at hn
  rw [hn]
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app,
    Category.comp_id]
  change ((tensorPullback g').obj F).presheaf.map (homOfLE hsub).op
      (((Classical.choose (exists_tensorPullbackAdjunction g')).unit.app F).app V
        (z • m)) =
    ((tensorPullback g').obj F).presheaf.map _
      (((tensorPullback g').obj F).presheaf.map _
        (((Classical.choose (exists_tensorPullbackAdjunction g')).unit.app F).app V
          (z • m)))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two section modules on a compatible pair of affine charts have tensor coordinates,
and the canonical base change map sends `r ⊗ m` to `(r ⊗ 1) ⊗ m` in these coordinates.
Source: Stacks Project, Tag 02KG, proof's reduction to spectra; Tag 01I9 (1), (2).
(blueprint: lem-weil-pbc-affine-base-change-chart-coordinates)

Proof: Quasi-coherence of the affine pushforward and the affine pullback section
formula give the source coordinates, normalized by eta_g followed by restriction to W.
The section-ring pushout theorem for the cartesian square identifies the ring on
f'⁻¹W with R' tensor_R B, compatibly with both ring maps. The same affine pullback
section formula for g' gives the target coordinates. Tensor balancing identifies
((1 tensor z) tensor m) with the unit image of z*m; composing restriction maps
identifies this with the defining adjoint k of beta on W. Apply the adjunction
identity homEquiv(homEquiv.symm(k)) = k and naturality of beta with restriction
from g⁻¹U to W. This proves the formula at 1 tensor m. Finally R'-linearity
of a.symm, beta and b extends it to every r tensor m. No invertibility of beta
is assumed. All constructions apply also to empty opens, zero rings and zero modules. -/
theorem exists_affineBaseChange_chart_coordinates {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsAffineOpen U)
    (W : S'.Opens) (hW : IsAffineOpen W) (hWU : W ≤ g ⁻¹ᵁ U) :
    let R := Γ(S, U)
    let B := Γ(X, f ⁻¹ᵁ U)
    let R' := Γ(S', W)
    let M := Γ(F, f ⁻¹ᵁ U)
    letI : Algebra R B := (f.app U).hom.toAlgebra
    letI : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
    letI : Module R M := Module.compHom M (f.app U).hom
    letI : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ∃ (a : Γ((tensorPullback g).obj ((pushforward f).obj F), W) ≃ₗ[R'] R' ⊗[R] M)
      (b : Γ((pushforward f').obj ((tensorPullback g').obj F), W) ≃ₗ[R']
        (R' ⊗[R] B) ⊗[B] M),
      ∀ (r : R') (m : M),
        b ((moduleBaseChangeMap f f' g g' sq.w F).app W (a.symm (r ⊗ₜ[R] m))) =
          (r ⊗ₜ[R] (1 : B)) ⊗ₜ[B] m := by
  classical
  let R := Γ(S, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let R' := Γ(S', W)
  let M := Γ(F, f ⁻¹ᵁ U)
  let : Algebra R B := (f.app U).hom.toAlgebra
  let : Algebra R R' := (g.appLE U W hWU).hom.toAlgebra
  let : Module R M := Module.compHom M (f.app U).hom
  let : Algebra B (R' ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let P := (tensorPullback g).obj ((pushforward f).obj F)
  let Q := (pushforward f').obj ((tensorPullback g').obj F)
  let k := (pushforward f).map
    ((Classical.choose (exists_tensorPullbackAdjunction g')).unit.app F) ≫
    (pushforwardComp g' f).hom.app ((tensorPullback g').obj F) ≫
    (pushforwardCongr sq.w).hom.app ((tensorPullback g').obj F) ≫
    (pushforwardComp f' g).inv.app ((tensorPullback g').obj F)
  let beta := moduleBaseChangeMap f f' g g' sq.w F
  have : ((pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f F
  obtain ⟨a₀, ha⟩ := source_chart_unit_comparison
    g ((pushforward f).obj F) U hU W hW hWU
  let a : Γ(P, W) ≃ₗ[R'] R' ⊗[R] M := a₀
  have ha' (m : M) : a.symm ((1 : R') ⊗ₜ[R] m) =
      P.presheaf.map (homOfLE hWU).op
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          ((pushforward f).obj F)).app U m) := ha m
  obtain ⟨b, hb⟩ := exists_affineBaseChange_target_chart_unit_comparison
    f f' g g' sq F U hU W hW hWU
  have hadj : (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
      ((pushforward f).obj F) ≫ (pushforward g).map beta = k := by
    have h := (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _
      |>.apply_symm_apply k
    rw [Adjunction.homEquiv_unit] at h
    exact h
  have hunit (m : M) : beta.app W (a.symm ((1 : R') ⊗ₜ[R] m)) =
      b.symm (((1 : R') ⊗ₜ[R] (1 : B)) ⊗ₜ[B] m) := by
    rw [ha', hb]
    simp only [one_smul]
    have hn := congr($(beta.mapPresheaf.naturality (homOfLE hWU).op)
      (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        ((pushforward f).obj F)).app U m))
    have he := congr($(hadj).app U m)
    simp only [mapPresheaf_app, Hom.comp_app, pushforward_map_app,
      ConcreteCategory.comp_apply] at hn he
    exact hn.trans (congrArg (Q.presheaf.map (homOfLE hWU).op) he)
  refine ⟨a, b, ?_⟩
  intro r m
  have hr : r ⊗ₜ[R] m = r • ((1 : R') ⊗ₜ[R] m) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  with_unfolding_all
    rw [hr, a.symm.map_smul, Hom.app_smul, b.map_smul, hunit, b.apply_symm_apply]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl


end
end AlgebraicGeometry.Scheme.Modules
