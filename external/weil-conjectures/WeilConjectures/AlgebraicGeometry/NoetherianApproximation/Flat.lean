/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOverLocal
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.RingTheory.Flat.NoetherianApproximation

/-!
# Flatness over the base descends to a finite stage

Let `V` be an affine scheme, written as the limit of the spectra of the finitely generated
subrings of `Γ(V, ⊤)` (`AlgebraicGeometry.Scheme.NoetherianApproximation.ofIsAffine`). Let
`p : Y ⟶ Spec Aᵢ` be quasi-compact and of finite presentation over one of the stages and `𝒢` a
module of finite presentation on `Y`. If the pullback of `𝒢` to `Y ×_{Spec Aᵢ} V` is flat over
`V`, then the pullback of `𝒢` to `Y ×_{Spec Aᵢ} Spec Aⱼ` is flat over `Spec Aⱼ` for all
sufficiently large stages `Aⱼ` (EGA IV₃, 11.2.6; Stacks, Tag 00R6).

The algebraic input is `Module.exists_fg_forall_flat_baseChange`, applied to the global sections
of `𝒢` over the members of a finite affine open cover of `Y`.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace Module

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- For an `R₀`-algebra `S₀`, an `S₀`-module `M₀` and an `R₀`-algebra `B`, the module
`(B ⊗[R₀] S₀) ⊗[S₀] M₀` is flat over `B` if and only if `B ⊗[R₀] M₀` is. -/
theorem flat_baseChange_tensorProduct_iff {R₀ S₀ M₀ B : Type*} [CommRing R₀] [CommRing S₀]
    [CommRing B] [Algebra R₀ S₀] [Algebra R₀ B] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀]
    [IsScalarTower R₀ S₀ M₀] :
    Flat B ((B ⊗[R₀] S₀) ⊗[S₀] M₀) ↔ Flat B (B ⊗[R₀] M₀) :=
  Flat.equiv_iff (Algebra.IsPushout.cancelBaseChange R₀ B S₀ (B ⊗[R₀] S₀) M₀)

/-- Flatness of base changes is transported along algebra maps: if `B ⊗[R] M` is flat over `B`
and `B ⟶ B'` is an `R`-algebra map, then `B' ⊗[R] M` is flat over `B'`. -/
theorem Flat.baseChange_of_algHom {R B B' M : Type*} [CommRing R] [CommRing B] [CommRing B']
    [Algebra R B] [Algebra R B'] [AddCommGroup M] [Module R M] (φ : B →ₐ[R] B')
    (h : Flat B (B ⊗[R] M)) : Flat B' (B' ⊗[R] M) := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  exact Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B' B' M).symm

end Module

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

/-- On global sections, the projection from an affine scheme `V` to the stage `Spec A` of its
Noetherian approximation is the inclusion `A ⟶ Γ(V, ⊤)`. -/
lemma Scheme.NoetherianApproximation.ofIsAffine_π_app_appTop_apply (V : Scheme.{u}) [IsAffine V]
    (k : (ofIsAffine V).I) (x : Γ(Spec (.of k.unop.1), ⊤)) :
    ((ofIsAffine V).π.app k).appTop x = ((Scheme.ΓSpecIso (.of k.unop.1)).hom x).1 := by
  simp [ofIsAffine, Scheme.isoSpec, Scheme.toSpecΓ_appTop]
  rfl

end AlgebraicGeometry

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.NoetherianApproximation

/-- **Flatness of the sections over an affine open descends to a finite stage.** In the
situation of `Scheme.Modules.exists_isFlatOver_pullback_ofIsAffine`, let `W` be an affine open
of `Y` and `R₀ = Γ(Spec Aᵢ, ⊤)`. There is a finite set `t ⊆ Γ(V, ⊤)` such that for every stage
`k ⟶ i` with `t ⊆ Aₖ` and every affine open `V'` of `Spec Aₖ`, the module
`Γ(Spec Aₖ, V') ⊗[R₀] Γ(𝒢, W)` is flat over `Γ(Spec Aₖ, V')`. -/
theorem Scheme.Modules.exists_finset_forall_flat_baseChange_sections (V : Scheme.{u}) [IsAffine V]
    {i : (ofIsAffine V).I} {Y : Scheme.{u}} (p : Y ⟶ (ofIsAffine V).D.obj i)
    [LocallyOfFiniteType p] (𝒢 : Y.Modules) [𝒢.IsFinitePresentation]
    (h𝒢 : ((Modules.pullback (pullback.fst p ((ofIsAffine V).π.app i))).obj 𝒢).IsFlatOver
      (pullback.snd p ((ofIsAffine V).π.app i))) (W : Y.affineOpens) :
    ∃ t : Finset Γ(V, ⊤), ∀ (k : (ofIsAffine V).I) (g : k ⟶ i),
      (t : Set Γ(V, ⊤)) ⊆ k.unop.1 → ∀ V' : ((ofIsAffine V).D.obj k).affineOpens,
        letI := (((ofIsAffine V).D.map g).appLE ⊤ V'.1 le_top).hom.toAlgebra
        letI : Module Γ((ofIsAffine V).D.obj i, ⊤) Γ(𝒢, W.1) :=
          Module.compHom _ (p.appLE ⊤ W.1 le_top).hom
        Module.Flat Γ((ofIsAffine V).D.obj k, V'.1)
          (Γ((ofIsAffine V).D.obj k, V'.1) ⊗[Γ((ofIsAffine V).D.obj i, ⊤)] Γ(𝒢, W.1)) := by
  have : IsAffine ((ofIsAffine V).D.obj i) := inferInstanceAs (IsAffine (Spec _))
  have : IsNoetherianRing Γ((ofIsAffine V).D.obj i, ⊤) := by
    have : Algebra.FiniteType ℤ i.unop.1 := (Subalgebra.fg_iff_finiteType _).mp i.unop.2
    have : IsNoetherianRing i.unop.1 := Algebra.FiniteType.isNoetherianRing ℤ _
    exact isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of i.unop.1)).commRingCatIsoToRingEquiv.symm
  let : Algebra Γ((ofIsAffine V).D.obj i, ⊤) Γ(Y, W.1) := (p.appLE ⊤ W.1 le_top).hom.toAlgebra
  let : Module Γ((ofIsAffine V).D.obj i, ⊤) Γ(𝒢, W.1) := Module.compHom _ (p.appLE ⊤ W.1 le_top).hom
  have : IsScalarTower Γ((ofIsAffine V).D.obj i, ⊤) Γ(Y, W.1) Γ(𝒢, W.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have : Algebra.FiniteType Γ((ofIsAffine V).D.obj i, ⊤) Γ(Y, W.1) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ W le_top
  have := finitePresentation_sections_of_isFinitePresentation 𝒢 W.2
  let : Algebra Γ((ofIsAffine V).D.obj i, ⊤) Γ(V, ⊤) :=
    (((ofIsAffine V).π.app i).appLE ⊤ ⊤ le_top).hom.toAlgebra
  have hA := (Module.flat_baseChange_tensorProduct_iff (S₀ := Γ(Y, W.1))).mpr
    (flat_baseChange_of_flat_sections_pullback_fst (Z := V) p ((ofIsAffine V).π.app i) 𝒢 W.2
      (isAffineOpen_top V)
      (h𝒢 ⟨⊤, isAffineOpen_top V⟩ ⟨_, isAffineOpen_preimage_inf_preimage_pullback p
        ((ofIsAffine V).π.app i) W.2 (isAffineOpen_top V)⟩ inf_le_right))
  obtain ⟨R₁, ⟨t, rfl⟩, hR₁⟩ := Module.exists_fg_forall_flat_baseChange (M₀ := Γ(𝒢, W.1)) hA
  refine ⟨t, fun k g ht V' ↦ ?_⟩
  let : Algebra Γ((ofIsAffine V).D.obj i, ⊤) Γ((ofIsAffine V).D.obj k, ⊤) :=
    (((ofIsAffine V).D.map g).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Algebra Γ((ofIsAffine V).D.obj i, ⊤) Γ((ofIsAffine V).D.obj k, V'.1) :=
    (((ofIsAffine V).D.map g).appLE ⊤ V'.1 le_top).hom.toAlgebra
  have hw : (ofIsAffine V).π.app k ≫ (ofIsAffine V).D.map g = (ofIsAffine V).π.app i := by
    simpa using ((ofIsAffine V).π.naturality g).symm
  -- the inclusion `Aₖ ⟶ Γ(V, ⊤)` as an algebra map over `R₀ = Γ(Spec Aᵢ, ⊤)`
  let ρ : Γ((ofIsAffine V).D.obj k, ⊤) →ₐ[Γ((ofIsAffine V).D.obj i, ⊤)] Γ(V, ⊤) :=
    { ((ofIsAffine V).π.app k).appTop.hom with
      commutes' r := by
        change ((ofIsAffine V).π.app k).app ⊤ (((ofIsAffine V).D.map g).appLE ⊤ ⊤ le_top r) =
          ((ofIsAffine V).π.app i).appLE ⊤ ⊤ le_top r
        rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
        simp only [hw]
        rfl }
  have hρ (x : Γ((ofIsAffine V).D.obj k, ⊤)) : ρ x = ((Scheme.ΓSpecIso (.of k.unop.1)).hom x).1 :=
    ofIsAffine_π_app_appTop_apply V k x
  have hinj : Function.Injective ρ := fun x y hxy ↦ by
    rw [hρ, hρ] at hxy
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k.unop.1)).hom).1
      (Subtype.ext hxy)
  have hle : Algebra.adjoin Γ((ofIsAffine V).D.obj i, ⊤) (t : Set Γ(V, ⊤)) ≤ ρ.range := by
    refine Algebra.adjoin_le fun a ha ↦ ⟨(Scheme.ΓSpecIso (.of k.unop.1)).inv ⟨a, ht ha⟩, ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρ, ← CommRingCat.comp_apply,
      Iso.inv_hom_id, CommRingCat.id_apply]
  -- the restriction `Γ(Spec Aₖ, ⊤) ⟶ Γ(Spec Aₖ, V')` as an algebra map over `R₀`
  let res : Γ((ofIsAffine V).D.obj k, ⊤) →ₐ[Γ((ofIsAffine V).D.obj i, ⊤)]
      Γ((ofIsAffine V).D.obj k, V'.1) :=
    { (((ofIsAffine V).D.obj k).presheaf.map (homOfLE le_top).op).hom with
      commutes' r := by
        change (((ofIsAffine V).D.obj k).presheaf.map (homOfLE le_top).op)
            (((ofIsAffine V).D.map g).appLE ⊤ ⊤ le_top r) =
          ((ofIsAffine V).D.map g).appLE ⊤ V'.1 le_top r
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] }
  exact Module.Flat.baseChange_of_algHom
    (res.comp ((AlgEquiv.ofInjective ρ hinj).symm.toAlgHom))
    (Module.flat_baseChange_tensorProduct_iff.mp (hR₁ ρ.range hle))

/-- **Flatness over the base descends to a finite stage** (EGA IV₃, 11.2.6). Let `V` be affine,
`p : Y ⟶ Spec Aᵢ` quasi-compact, quasi-separated and locally of finite presentation over a stage
of the Noetherian approximation `ofIsAffine V` of `V`, and `𝒢` a module of finite presentation on
`Y` whose pullback to `Y ×_{Spec Aᵢ} V` is flat over `V`. Then for some stage `j ⟶ i`, and every
later stage `k`, the pullback of `𝒢` to `Y ×_{Spec Aᵢ} Spec Aₖ` is flat over `Spec Aₖ`. -/
theorem Scheme.Modules.exists_isFlatOver_pullback_ofIsAffine (V : Scheme.{u}) [IsAffine V]
    {i : (ofIsAffine V).I} {Y : Scheme.{u}} (p : Y ⟶ (ofIsAffine V).D.obj i)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p] (𝒢 : Y.Modules)
    [𝒢.IsFinitePresentation]
    (h𝒢 : ((Modules.pullback (pullback.fst p ((ofIsAffine V).π.app i))).obj 𝒢).IsFlatOver
      (pullback.snd p ((ofIsAffine V).π.app i))) :
    ∃ (j : (ofIsAffine V).I) (f : j ⟶ i), ∀ (k : (ofIsAffine V).I) (g : k ⟶ j),
      ((Modules.pullback (pullback.fst p ((ofIsAffine V).D.map (g ≫ f)))).obj 𝒢).IsFlatOver
        (pullback.snd p ((ofIsAffine V).D.map (g ≫ f))) := by
  classical
  have : IsAffine ((ofIsAffine V).D.obj i) := inferInstanceAs (IsAffine (Spec _))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨s, hs, hY⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : Y.Opens))).mp
    (by simpa using isCompact_univ)
  choose t ht using exists_finset_forall_flat_baseChange_sections V p 𝒢 h𝒢
  obtain ⟨tᵢ, htᵢ⟩ := i.unop.2
  set T : Finset Γ(V, ⊤) := tᵢ ∪ hs.toFinset.biUnion t
  have hij : i.unop.1 ≤ Algebra.adjoin ℤ (T : Set Γ(V, ⊤)) := by
    rw [← htᵢ]
    exact Algebra.adjoin_mono (by simp [T])
  let f : (Opposite.op ⟨_, Subalgebra.fg_adjoin_finset T⟩ : (ofIsAffine V).I) ⟶ i :=
    (homOfLE (Subtype.coe_le_coe.mp hij : i.unop ≤ ⟨_, Subalgebra.fg_adjoin_finset T⟩)).op
  refine ⟨_, f, fun k g ↦ ?_⟩
  have hjk : Algebra.adjoin ℤ (T : Set Γ(V, ⊤)) ≤ k.unop.1 := leOfHom g.unop
  refine isFlatOver_of_forall_exists_nhds _ _ fun V' x _ ↦ ?_
  have hx : pullback.fst p ((ofIsAffine V).D.map (g ≫ f)) x ∈ ⨆ W ∈ s, (W : Y.Opens) := hY ▸ trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨W, hW, hxW⟩ := hx
  refine ⟨_, hxW, fun U e hUN ↦ flat_sections_pullback_fst_of_flat_baseChange _ _ 𝒢 W.2 V'.2
    U.2 (le_inf hUN e) (ht W k _ (fun a ha ↦ hjk (Algebra.subset_adjoin ?_)) V')⟩
  simp only [T, Finset.coe_union, Finset.coe_biUnion, Set.Finite.coe_toFinset, Set.mem_union,
    Set.mem_iUnion, Finset.mem_coe]
  exact Or.inr ⟨W, hW, ha⟩

end AlgebraicGeometry
