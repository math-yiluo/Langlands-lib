/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.SplitSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Second cohomology of a generic extension on an affine curve

Let `C` be a smooth affine connected curve over an algebraically closed field `k`, with generic
point `η : Spec k(C) ⟶ C`. We show `H²(C, η_* M) = 0` for every torsion étale sheaf `M` on
`Spec k(C)` (blueprint `theorem-cohomology-curves--2`).

For a sheaf `N` split by a finite Galois extension `L` of `k(C)` whose Galois group is an
`ℓ`-group, with finite `ℓ`-primary sections over `Spec L`, `N` is filtered by constant sheaves
`ℤ/ℓ` (`AlgebraicGeometry.Scheme.IsSplitBy.induction`). For a monomorphism `ℤ/ℓ ⟶ N` with
cokernel `Q`, the sequence `0 ⟶ η_* ℤ/ℓ ⟶ η_* N ⟶ η_* Q` is exact, and the cokernel of the last
map has zero generic restriction since `η^* η_* = id`, hence no cohomology in positive degrees.
So `H²(C, η_* N) = 0` follows from `H²(C, η_* ℤ/ℓ) = H²(C, ℤ/ℓ) = 0`.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy`:
  `H²(C, η_* N) = 0` for `N` split by an `ℓ`-group extension.
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_finite`:
  `H²(C, η_* N) = 0` for `N` split by a finite Galois extension, with finite sections over it
  (Sylow reduction and trace).
- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar`: `H²(C, η_* M) = 0` for
  every torsion sheaf `M` on the generic point.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Module

namespace AlgebraicGeometry

open Etale

/-- A zero sheaf has no cohomology. -/
lemma _root_.CategoryTheory.Sheaf.H.subsingleton_of_isZero {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] {G : Sheaf J AddCommGrpCat.{u + 1}}
    (hG : IsZero G) (n : ℕ) : Subsingleton (Sheaf.H G n) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  rw [← Sheaf.H.map_id_apply x, hG.eq_of_src (𝟙 G) 0, Sheaf.H.map_apply, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]

include f in
/-- `H²(C, η_* ℤ/ℓ) = 0` for the generic point `η` of a smooth affine connected curve: it is
`H²(C, ℤ/ℓ)` by generic replacement. -/
theorem subsingleton_sheafH_two_lowerStar_constantZMod (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((Spec C.functionField).constantZMod ℓ)) 2) := by
  have hb := IsCurve.bijective_H_map_unit_fromSpecFunctionField f (C.constantZMod ℓ) 0
  have := subsingleton_sheafH_two_constantZMod f ℓ
  have h : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((C.fromSpecFunctionField)^*[AddCommGrpCat.{u + 1}].obj (C.constantZMod ℓ))) 2) :=
    ⟨fun x y ↦ by
      obtain ⟨x, rfl⟩ := hb.2 x
      obtain ⟨y, rfl⟩ := hb.2 y
      exact congrArg _ (Subsingleton.elim (α := Sheaf.H (C.constantZMod ℓ) 2) x y)⟩
  let e := ((Sheaf.functorH _ 2).mapIso ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].mapIso
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} C.fromSpecFunctionField).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.symm.injective (@Subsingleton.elim _ h _ _)⟩

omit [Smooth f] in
include f in
/-- **Extensions on the generic point.** Let `ι : A ⟶ N` be a monomorphism of sheaves on the
generic point `η` of a smooth affine connected curve `C`. If `H²(C, η_* A) = 0` and
`H²(C, η_* coker ι) = 0`, then `H²(C, η_* N) = 0`. The pushforward `η_*` is only left exact, but
the cokernel of `η_* N ⟶ η_* coker ι` has zero generic restriction, since `η^* η_* = id`
(`AlgebraicGeometry.Scheme.isIso_counit_app_fromSpecFunctionField`), hence no cohomology in
positive degrees. -/
theorem subsingleton_sheafH_two_lowerStar_of_mono
    {A N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : A ⟶ N)
    [Mono ι] (hA : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      A) 2))
    (hQ : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      (cokernel ι)) 2)) :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) := by
  set η := C.fromSpecFunctionField
  set R := (η)_*[AddCommGrpCat.{u + 1}]
  set φ := R.map (cokernel.π ι)
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} η
  -- the generic restriction of `coker φ` vanishes
  have hε (M) : IsIso (adj.counit.app M) := Scheme.isIso_counit_app_fromSpecFunctionField M
  have hepi : Epi ((η)^*[AddCommGrpCat.{u + 1}].map φ) := by
    have h := adj.counit.naturality (cokernel.π ι)
    have : (η)^*[AddCommGrpCat.{u + 1}].map φ =
        adj.counit.app N ≫ cokernel.π ι ≫ inv (adj.counit.app (cokernel ι)) := by
      rw [← Category.assoc]
      exact (IsIso.eq_comp_inv _).2 h
    rw [this]
    infer_instance
  have hz : IsZero ((η)^*[AddCommGrpCat.{u + 1}].obj (cokernel φ)) :=
    (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ φ)
  have hG (V : C.Etale) (s : (cokernel φ).obj.obj (op V)) :
      C.genericVanishingSieve (cokernel φ) s ∈ C.smallEtaleTopology V := by
    refine Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_
    let x := (cokernel φ).obj.map g.op s
    have hP := Scheme.fromSpecFunctionField_eq_functionFieldCone_comp C
    have hτ (U : C.NonemptyAffineOpens) := Etale.unit_app_comp_unitComparison
      (C.functionFieldCone.π.app U) (C.affineOpensDiagramι.app U) η (hP U) (cokernel φ)
    have hx : (adj.unit.app (cokernel φ)).hom.app (op W) x = 0 := by
      rw [(R.map_isZero hz).eq_of_tgt (adj.unit.app (cokernel φ)) 0]
      rfl
    let U₀ : C.NonemptyAffineOpens := Classical.arbitrary _
    have h₀ : (Etale.unitComparison (C.functionFieldCone.π.app U₀) (C.affineOpensDiagramι.app U₀)
        η (hP U₀) (cokernel φ)).hom.app (op W)
          ((C.affineOpenUnit U₀ (cokernel φ)).hom.app (op W) x) = 0 := by
      rw [← hτ U₀] at hx
      exact hx
    have : CompactSpace W.left := inferInstance
    obtain ⟨U, f', hU⟩ := Etale.exists_unitComparison_app_eq_zero_of_isLimit C.affineOpensDiagram
      C.affineOpensDiagramι C.functionFieldCone η hP C.isLimitFunctionFieldCone (cokernel φ) W
      U₀ _ h₀
    refine ⟨U, ?_⟩
    rw [← C.affineOpenUnit_comp_transition f' (cokernel φ)]
    exact hU
  have hH₁ := IsCurve.subsingleton_H_of_genericVanishing f (cokernel φ) hG 0
  -- the two short exact sequences
  let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (by simp)
  have hS₂ : S₂.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance inferInstance
  have hI : Subsingleton (Sheaf.H (Abelian.image φ) 2) :=
    have : Subsingleton (Sheaf.H S₂.X₃ 1) := hH₁
    have : Subsingleton (Sheaf.H S₂.X₂ (1 + 1)) := hQ
    Sheaf.H.subsingleton_X₁_of_shortExact hS₂ 1
  have hker : IsLimit (KernelFork.ofι (R.map ι) (show R.map ι ≫ φ = 0 by
      rw [← R.map_comp, cokernel.condition, R.map_zero])) :=
    isLimitForkMapOfIsLimit' R _ (Abelian.monoIsKernelOfCokernel _
      (colimit.isColimit (parallelPair ι 0)))
  let S₁ := ShortComplex.mk (R.map ι) (Abelian.factorThruImage φ)
    (by rw [← cancel_mono (Abelian.image.ι φ), Category.assoc, Abelian.image.fac,
      ← R.map_comp, cokernel.condition, R.map_zero, zero_comp])
  have hS₁ : S₁.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    refine ShortComplex.exact_of_f_is_kernel _ ?_
    refine KernelFork.IsLimit.ofι' _ _ fun {B} k hk ↦ ⟨hker.lift (KernelFork.ofι k ?_), ?_⟩
    · change k ≫ Abelian.factorThruImage φ = 0 at hk
      rw [← Abelian.image.fac φ, ← Category.assoc, hk, zero_comp]
    · exact hker.fac _ WalkingParallelPair.zero
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (Sheaf.H.exact_map_map hS₁ 2 x).1 (Subsingleton.elim (h := hI) _ _)
  rw [Subsingleton.elim (h := hA) y 0, map_zero]

include f in
/-- **`H²` of a split `ℓ`-primary sheaf on the generic point.** Let `L` be a finite Galois
extension of the function field of a smooth affine connected curve `C` with Galois group an
`ℓ`-group, and `N` a sheaf on the generic point `η` split by `L`, with finite `ℓ`-primary sections
over `Spec L`. Then `H²(C, η_* N) = 0`: `N` is filtered by constant sheaves `ℤ/ℓ`
(`AlgebraicGeometry.Scheme.IsSplitBy.induction`). -/
theorem subsingleton_sheafH_two_lowerStar_of_isSplitBy (L : Type u) [Field L]
    [Algebra C.functionField L] [Algebra.Etale C.functionField L] [IsGalois C.functionField L]
    (ℓ : ℕ) [Fact ℓ.Prime] (hP : IsPGroup ℓ (L ≃ₐ[C.functionField] L))
    (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : Scheme.IsSplitBy N L) [Finite (N.obj.obj (op (Scheme.etaleSpec C.functionField L)))]
    (hNℓ : ∀ x : N.obj.obj (op (Scheme.etaleSpec C.functionField L)), ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) :=
  Scheme.IsSplitBy.induction ℓ hP
    (fun N ↦ Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2))
    (fun _ hN ↦ Sheaf.H.subsingleton_of_isZero (Functor.map_isZero _ hN) 2)
    (fun _ _ hz hzℓ hQ ↦
      have := Scheme.mono_constantZModHom ℓ hz hzℓ
      subsingleton_sheafH_two_lowerStar_of_mono f (Scheme.constantZModHom ℓ hz)
        (subsingleton_sheafH_two_lowerStar_constantZMod f ℓ) hQ) hN hNℓ

include f in
/-- **`H²` of a split `ℓ`-primary sheaf.** Let `L` be a finite Galois extension of the function
field `K` of a smooth affine connected curve `C`, and `N` a sheaf on the generic point `η` split by
`L`, with finite `ℓ`-primary sections over `Spec L`. Then `H²(C, η_* N) = 0`.

Let `K₀ ⊆ L` be the fixed field of a Sylow `ℓ`-subgroup, of degree `d` prime to `ℓ` over `K`, and
`h : C' ⟶ C` the normalization of `C` in `K₀`, whose function field is `K₀`. The unit and the
trace of `Spec K₀ ⟶ Spec K` compose to `d`, so `d` kills `H²(C, η_* N)`, as this class factors
through `H²(C, h_* η'_* N|_{K₀}) = H²(C', η'_* N|_{K₀}) = 0`
(`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy`); and a
power of `ℓ` kills it too. -/
theorem subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_isGalois (L : Type u) [Field L]
    [Algebra C.functionField L] [Algebra.Etale C.functionField L] [IsGalois C.functionField L]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : Scheme.IsSplitBy N L) [Finite (N.obj.obj (op (Scheme.etaleSpec C.functionField L)))]
    (hNℓ : ∀ x : N.obj.obj (op (Scheme.etaleSpec C.functionField L)), ∃ k : ℕ, ℓ ^ k • x = 0) :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) := by
  classical
  have hℓ := Fact.out (p := ℓ.Prime)
  have : FiniteDimensional C.functionField L :=
    Algebra.FormallyUnramified.finite_of_free C.functionField L
  -- a Sylow subgroup and its fixed field
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (L ≃ₐ[C.functionField] L)) := inferInstance
  let K₀ := IntermediateField.fixedField (P : Subgroup (L ≃ₐ[C.functionField] L))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have h₁ : finrank K₀ L = ℓ ^ n := (IntermediateField.finrank_fixedField_eq_card _).trans hn
  have h₂ : finrank C.functionField K₀ * finrank K₀ L = finrank C.functionField L :=
    finrank_mul_finrank C.functionField K₀ L
  have hd : ¬ ℓ ∣ finrank C.functionField K₀ := by
    have h₃ := (P : Subgroup (L ≃ₐ[C.functionField] L)).index_mul_card
    rw [IsGalois.card_aut_eq_finrank, ← h₂, hn, h₁] at h₃
    have h₄ : finrank C.functionField K₀ = (P : Subgroup (L ≃ₐ[C.functionField] L)).index :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hℓ.pos n) h₃.symm
    rw [h₄]
    exact P.not_dvd_index
  -- the normalization of `C` in `K₀`
  obtain ⟨hfin, haff, hcc, hsm, e, he⟩ := normalizationIn f K₀
  let C' := C.normalizationIn K₀
  let h := C.fromNormalizationIn K₀
  -- transport the algebra structures from `K₀` to the function field `K''` of `C'`
  let ψ : C'.functionField ≅ CommRingCat.of K₀ := (Scheme.Spec.preimageIso e).unop
  have hψ : Spec.map ψ.hom = e.hom := Scheme.Spec.map_preimage e.hom
  let : Algebra C.functionField C'.functionField :=
    (ψ.inv.hom.comp (algebraMap C.functionField K₀)).toAlgebra
  let : Algebra C'.functionField L := ((algebraMap K₀ L).comp ψ.hom.hom).toAlgebra
  have : IsScalarTower C.functionField C'.functionField L := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change _ = algebraMap K₀ L (ψ.hom (ψ.inv (algebraMap C.functionField K₀ x)))
    rw [Iso.inv_hom_id_apply, ← IsScalarTower.algebraMap_apply]
  let ψa : K₀ ≃ₐ[C.functionField] C'.functionField :=
    { toRingEquiv := ψ.symm.commRingCatIsoToRingEquiv
      commutes' _ := rfl }
  have : Algebra.IsSeparable C.functionField K₀ :=
    Algebra.isSeparable_tower_bot_of_isSeparable C.functionField K₀ L
  have : Algebra.FormallyEtale C.functionField K₀ := Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.Etale C.functionField K₀ :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : Algebra.Etale C.functionField C'.functionField := Algebra.Etale.of_equiv ψa
  have hd' : finrank C.functionField C'.functionField = finrank C.functionField K₀ :=
    ψa.toLinearEquiv.finrank_eq.symm
  have : IsGalois C'.functionField L :=
    IsGalois.of_equiv_equiv (f := ψ.symm.commRingCatIsoToRingEquiv) (g := RingEquiv.refl L)
      (by ext x; change algebraMap K₀ L (ψ.hom (ψ.inv x)) = _; rw [Iso.inv_hom_id_apply]; rfl)
  have : Module.Finite C'.functionField L :=
    Module.Finite.of_restrictScalars_finite C.functionField C'.functionField L
  have : Algebra.FormallyEtale C'.functionField L := Algebra.FormallyEtale.of_isSeparable _ _
  have : Algebra.Etale C'.functionField L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hPG : IsPGroup ℓ (L ≃ₐ[C'.functionField] L) := by
    refine IsPGroup.of_card (n := n) ?_
    rw [IsGalois.card_aut_eq_finrank, ← h₁]
    have h₅ := finrank_mul_finrank C.functionField C'.functionField L
    rw [hd', ← h₂] at h₅
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero fun h0 ↦ hd (by rw [h0]; exact dvd_zero ℓ))
      h₅
  -- the generic points
  have hgen : C'.fromSpecFunctionField ≫ h =
      Scheme.FieldTrace.f C.functionField C'.functionField ≫ C.fromSpecFunctionField := by
    have h₆ : Scheme.FieldTrace.f C.functionField C'.functionField =
        e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap C.functionField K₀)) := by
      rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc, ← hψ, Scheme.FieldTrace.f, ← Spec.map_comp]
      congr 1
      ext x
      exact congrArg Subtype.val (Iso.inv_hom_id_apply ψ (algebraMap C.functionField K₀ x))
    rw [h₆, Category.assoc, ← Scheme.fromSpecOfAlgebraFunctionField, Iso.eq_inv_comp,
      ← Category.assoc, he,
      Scheme.Hom.toNormalization_fromNormalization]
  -- the restriction of `N` to `K''`
  let N'' := Scheme.FieldTrace.res C.functionField C'.functionField N
  have hN'' : Scheme.IsSplitBy N'' L := hN.res
  have hb := Scheme.bijective_map_overMapEtaleSpecIso_inv (N := N) (L := L)
    (F' := C'.functionField)
  have : Finite (N''.obj.obj (op (Scheme.etaleSpec C'.functionField L))) :=
    Finite.of_injective _ hb.1
  have hNℓ'' (x : N''.obj.obj (op (Scheme.etaleSpec C'.functionField L))) :
      ∃ k : ℕ, ℓ ^ k • x = 0 := by
    obtain ⟨k, hk⟩ := hNℓ (N.obj.map (Scheme.overMapEtaleSpecIso L C'.functionField).inv.op x)
    exact ⟨k, hb.1 (by rw [map_nsmul, hk, map_zero])⟩
  have hA := subsingleton_sheafH_two_lowerStar_of_isSplitBy (h ≫ f) L ℓ hPG N'' hN'' hNℓ''
  -- `H²(C, η_* a_* N'') = H²(C', η'_* N'') = 0`
  have hB : Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((Scheme.FieldTrace.f C.functionField C'.functionField)_*[AddCommGrpCat.{u + 1}].obj
        N'')) 2) := by
    have h₇ : Subsingleton (Sheaf.H ((h)_*[AddCommGrpCat.{u + 1}].obj
        ((C'.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N'')) 2) :=
      ⟨fun x y ↦ (bijective_edgeMap_of_isFinite h _ 2).1 (Subsingleton.elim (h := hA) _ _)⟩
    let i := (lowerStarComp AddCommGrpCat.{u + 1} (Scheme.FieldTrace.f C.functionField
      C'.functionField) C.fromSpecFunctionField (C'.fromSpecFunctionField ≫ h) hgen).app N'' ≪≫
      ((lowerStarComp AddCommGrpCat.{u + 1} C'.fromSpecFunctionField h).app N'').symm
    let e := ((Sheaf.functorH _ 2).mapIso i).addCommGroupIsoToAddEquiv
    exact ⟨fun x y ↦ e.injective (Subsingleton.elim (h := h₇) _ _)⟩
  -- the trace argument
  set η := C.fromSpecFunctionField
  set d := finrank C.functionField C'.functionField
  have hH (φ : N ⟶ N) (c : Sheaf.H ((η)_*[AddCommGrpCat.{u + 1}].obj N) 2) :
      ((Sheaf.functorH _ 2).map ((η)_*[AddCommGrpCat.{u + 1}].map φ)) c =
        Sheaf.H.map ((η)_*[AddCommGrpCat.{u + 1}].map φ) 2 c := rfl
  -- an exponent of the sections over `Spec L`
  have : Fintype (N.obj.obj (op (Scheme.etaleSpec C.functionField L))) := Fintype.ofFinite _
  choose kx hkx using hNℓ
  let k := Finset.univ.sup kx
  have hk : ℓ ^ k • 𝟙 N = 0 := Scheme.nsmul_id_eq_zero_of_isSplitBy hN _ fun x ↦ by
    obtain ⟨m, hm⟩ : ∃ m, k = kx x + m :=
      Nat.exists_eq_add_of_le (Finset.le_sup (f := kx) (Finset.mem_univ x))
    rw [hm, pow_add, mul_comm, ← smul_smul, hkx, smul_zero]
  have hcop : Nat.Coprime d (ℓ ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2
      (hd' ▸ hd))))
  have key (m : ℕ) (x : Sheaf.H ((η)_*[AddCommGrpCat.{u + 1}].obj N) 2) :
      Sheaf.H.map (m • 𝟙 ((η)_*[AddCommGrpCat.{u + 1}].obj N)) 2 x = m • x := by
    induction m with
    | zero => simp [Sheaf.H.map_apply, Abelian.Ext.mk₀_zero]
    | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply, succ_nsmul]
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  have hc₁ : d • c = 0 := by
    have h₈ := congrArg (fun φ ↦ ((Sheaf.functorH _ 2).map ((η)_*[AddCommGrpCat.{u + 1}].map φ)) c)
      (Scheme.FieldTrace.unit_comp_trace C.functionField C'.functionField N)
    have hL : ((Sheaf.functorH _ 2).map ((η)_*[AddCommGrpCat.{u + 1}].map
        (Scheme.FieldTrace.unit C.functionField C'.functionField N ≫
          Scheme.FieldTrace.trace C.functionField C'.functionField N))) c = 0 := by
      rw [Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        Subsingleton.elim (h := hB) (((Sheaf.functorH _ 2).map ((η)_*[AddCommGrpCat.{u + 1}].map
          (Scheme.FieldTrace.unit C.functionField C'.functionField N))) c) 0, map_zero]
    rw [← natCast_zsmul, ← hL]
    refine Eq.trans ?_ h₈.symm
    simp only [natCast_zsmul] at h₈ ⊢
    exact (key d c).symm
  have hc₂ : ℓ ^ k • c = 0 := by
    have h₉ : Sheaf.H.map ((η)_*[AddCommGrpCat.{u + 1}].map (ℓ ^ k • 𝟙 N)) 2 c =
        Sheaf.H.map ((η)_*[AddCommGrpCat.{u + 1}].map 0) 2 c := by rw [hk]
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, key, Functor.map_zero] at h₉
    rw [h₉]
    simp [Sheaf.H.map_apply, Abelian.Ext.mk₀_zero]
  have : addOrderOf c = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd
    (addOrderOf_dvd_of_nsmul_eq_zero hc₁) (addOrderOf_dvd_of_nsmul_eq_zero hc₂))
  exact AddMonoid.addOrderOf_eq_one_iff.1 this

end IsConnectedCurve

end AlgebraicGeometry
/-- Multiples of a morphism of abelian sheaves act on sections by multiplication. -/
lemma CategoryTheory.Sheaf.nsmul_hom_app_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {G G' : Sheaf J AddCommGrpCat.{u + 1}} (n : ℕ) (φ : G ⟶ G')
    (W : Cᵒᵖ) (x : G.obj.obj W) : (n • φ).hom.app W x = n • φ.hom.app W x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul, ← ih]
    rfl

namespace AlgebraicGeometry.Scheme

variable {F : Type u} [Field F]
  {N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}}
  {L : Type u} [Field L] [Algebra F L] [Algebra.Etale F L]

/-- The kernel of multiplication by `n` on a split sheaf is split. -/
lemma IsSplitBy.kernel (hN : IsSplitBy N L) (n : ℕ) : IsSplitBy (kernel (n • 𝟙 N)) L := by
  intro Z _ _ t
  have hι (W) : Function.Injective ((kernel.ι (n • 𝟙 N)).hom.app (op W)) :=
    Etale.injective_app_of_mono _ W
  have hk {W} (x : N.obj.obj (op W)) (hx : n • x = 0) :
      ∃ y, (kernel.ι (n • 𝟙 N)).hom.app (op W) y = x :=
    Etale.exists_kernel_ι_app_eq _ x (by rw [Sheaf.nsmul_hom_app_apply]; exact hx)
  have hn {W} (y) : n • (kernel.ι (n • 𝟙 N)).hom.app (op W) y = 0 := by
    have := congrArg (fun φ ↦ φ.hom.app (op W) y) (kernel.condition (n • 𝟙 N))
    have h1 : (n • 𝟙 N).hom.app (op W) ((kernel.ι (n • 𝟙 N)).hom.app (op W) y) = 0 := this
    rwa [Sheaf.nsmul_hom_app_apply] at h1
  refine ⟨fun y y' h ↦ hι _ ((hN Z t).1 ?_), fun y ↦ ?_⟩
  · rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]
  · obtain ⟨m, hm⟩ := (hN Z t).2 ((kernel.ι (n • 𝟙 N)).hom.app _ y)
    have hm0 : n • m = 0 := (hN Z t).1 (by rw [map_nsmul, hm, hn, map_zero])
    obtain ⟨y', rfl⟩ := hk m hm0
    refine ⟨y', hι _ ?_⟩
    rw [NatTrans.naturality_apply, hm]

end AlgebraicGeometry.Scheme

/-- Multiplication by `m` on a sheaf induces multiplication by `m` on cohomology. -/
lemma CategoryTheory.Sheaf.H.map_nsmul_id_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] (G : Sheaf J AddCommGrpCat.{u + 1})
    (m n : ℕ) (x : Sheaf.H G n) : Sheaf.H.map (m • 𝟙 G) n x = m • x := by
  induction m with
  | zero => simp [Sheaf.H.map_apply, Abelian.Ext.mk₀_zero]
  | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply, succ_nsmul]

namespace AlgebraicGeometry.IsConnectedCurve

open Etale

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
  [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]

include f in
/-- **`H²` of a finite split sheaf.** Let `N` be a sheaf on the generic point `η` of a smooth
affine connected curve `C`, split by a finite Galois extension `L` of the function field, with
finite sections over `Spec L`. Then `H²(C, η_* N) = 0`: decompose by the primes dividing an
exponent of `N`, using
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_isGalois`.
-/
theorem subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_finite (L : Type u) [Field L]
    [Algebra C.functionField L] [Algebra.Etale C.functionField L] [IsGalois C.functionField L]
    (N : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hN : Scheme.IsSplitBy N L) [Finite (N.obj.obj (op (Scheme.etaleSpec C.functionField L)))] :
    Subsingleton (Sheaf.H ((C.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj N) 2) := by
  set η := C.fromSpecFunctionField
  suffices H : ∀ m, 0 < m → ∀ (N : Sheaf (Spec C.functionField).smallEtaleTopology
      AddCommGrpCat.{u + 1}), Scheme.IsSplitBy N L →
      Finite (N.obj.obj (op (Scheme.etaleSpec C.functionField L))) →
      (∀ x : N.obj.obj (op (Scheme.etaleSpec C.functionField L)), m • x = 0) →
        Subsingleton (Sheaf.H ((η)_*[AddCommGrpCat.{u + 1}].obj N) 2) from
    H _ Nat.card_pos N hN inferInstance fun x ↦ card_nsmul_eq_zero'
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm N hN _ hNm
  by_cases h1 : m = 1
  · subst h1
    exact Sheaf.H.subsingleton_of_isZero ((η)_*[AddCommGrpCat.{u + 1}].map_isZero
      (Scheme.isZero_of_isSplitBy hN fun x ↦ by simpa using hNm x)) 2
  set ℓ := m.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨e, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hmeq
    exact hm' (hmeq ▸ Nat.minFac_dvd m)
  have hm'lt : m' < m := by
    rw [hmeq]
    have : 0 < m' := Nat.pos_of_ne_zero (fun h ↦ hm.ne' (by rw [hmeq, h, mul_zero]))
    exact lt_mul_left this (Nat.one_lt_pow he hℓ.one_lt)
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h ↦ hm.ne' (by rw [hmeq, h, mul_zero]))
  have hmN : m • 𝟙 N = 0 := Scheme.nsmul_id_eq_zero_of_isSplitBy hN m hNm
  have hfin (a : ℕ) :
      Finite ((kernel (a • 𝟙 N)).obj.obj (op (Scheme.etaleSpec C.functionField L))) :=
    Finite.of_injective _ (Etale.injective_app_of_mono (kernel.ι (a • 𝟙 N)) _)
  have hker (a : ℕ) (x : (kernel (a • 𝟙 N)).obj.obj (op (Scheme.etaleSpec C.functionField L))) :
      a • x = 0 := by
    refine Etale.injective_app_of_mono (kernel.ι (a • 𝟙 N)) _ ?_
    have := congrArg (fun φ ↦ φ.hom.app (op (Scheme.etaleSpec C.functionField L)) x)
      (kernel.condition (a • 𝟙 N))
    have h1 : (a • 𝟙 N).hom.app _ ((kernel.ι (a • 𝟙 N)).hom.app _ x) = 0 := this
    rw [Sheaf.nsmul_hom_app_apply] at h1
    rw [map_nsmul, map_zero]
    exact h1
  have hA₁ := subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_isGalois f L ℓ
    (kernel (ℓ ^ e • 𝟙 N)) (hN.kernel _) (fun x ↦ ⟨e, hker _ x⟩)
  have hA₂ := ih m' hm'lt hm'pos (kernel (m' • 𝟙 N)) (hN.kernel _) (hfin _) (hker _)
  have hfac (a b : ℕ) (hab : a * b = m) (A : Subsingleton (Sheaf.H ((η)_*[AddCommGrpCat.{u + 1}].obj
      (kernel (a • 𝟙 N))) 2)) (c : Sheaf.H ((η)_*[AddCommGrpCat.{u + 1}].obj N) 2) :
      b • c = 0 := by
    have hw : (b • 𝟙 N) ≫ (a • 𝟙 N) = 0 := by
      rw [Preadditive.comp_nsmul, Category.comp_id, smul_smul, hab, hmN]
    rw [← Sheaf.H.map_nsmul_id_apply, ← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
      ← kernel.lift_ι (a • 𝟙 N) (b • 𝟙 N) hw, Functor.map_comp, Sheaf.H.map_comp_apply,
      Subsingleton.elim (h := A) (Sheaf.H.map _ 2 c) 0, map_zero]
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  have hc₁ := hfac _ _ hmeq.symm hA₁ c
  have hc₂ := hfac _ _ ((mul_comm _ _).trans hmeq.symm) hA₂ c
  have hcop : Nat.Coprime m' (ℓ ^ e) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hm'))
  have : addOrderOf c = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd
    (addOrderOf_dvd_of_nsmul_eq_zero hc₁) (addOrderOf_dvd_of_nsmul_eq_zero hc₂))
  exact AddMonoid.addOrderOf_eq_one_iff.1 this

end AlgebraicGeometry.IsConnectedCurve

namespace AlgebraicGeometry

open Etale

variable {X : Scheme.{u}}

-- the colimits of shape `J` in the category of sheaves are found by a long instance search
/-- **Filtered unions of subsheaves, indexed by a large category.** The variant of
`AlgebraicGeometry.Etale.isColimitOfMonoOfLocallySurjective` for filtered diagrams indexed by a
category of the universe of the sheaf values. -/
noncomputable def Etale.isColimitOfMonoOfLocallySurjective' {J : Type (u + 1)} [SmallCategory J]
    [IsFiltered J] {D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cocone D)
    [∀ j, Mono (c.ι.app j)]
    (h : ∀ (V : X.Etale) (s : c.pt.obj.obj (op V)), ∃ R ∈ X.smallEtaleTopology V,
      ∀ ⦃W : X.Etale⦄ (g : W ⟶ V), R g →
        ∃ (j : J) (t : (D.obj j).obj.obj (op W)),
          (c.ι.app j).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : IsConnected J := IsFiltered.isConnected _
  have : HasColimitsOfShape J (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app j := c.ι.app j }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const J).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone J c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun j ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine X.smallEtaleTopology.superset_covering ?_ hR
      intro W g hg
      obtain ⟨j, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D j).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- The generic fibre of an affine étale scheme over an affine integral scheme is affine. -/
lemma isAffine_fromSpecFunctionField_etale_obj [IsAffine C] [IsIntegral C] (W : C.Etale)
    [IsAffine W.left] :
    IsAffine ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
      C.fromSpecFunctionField).obj W).left := by
  change IsAffine (pullback W.hom C.fromSpecFunctionField)
  have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
  have : IsAffine ((Functor.fromPUnit C).obj W.right) := ‹IsAffine C›
  have : IsAffineHom W.hom := isAffineHom_of_isAffine _
  exact isAffine_of_isAffineHom (pullback.snd W.hom C.fromSpecFunctionField)

/-- **Second cohomology of a generic extension on an affine curve.** Let `C` be a smooth integral
affine connected curve over an algebraically closed field `k`, with generic point
`η : Spec k(C) ⟶ C`. Then `H²(C_ét, η_* M) = 0` for every torsion étale sheaf `M` on
`Spec k(C)`.

The sheaf `M` is the filtered union of its subsheaves split by a finite Galois extension of
`k(C)` with finite sections over it (`AlgebraicGeometry.Scheme.SplitFamily`), so `η_* M` is the
filtered union of their pushforwards, and cohomology commutes with filtered colimits on the
quasi-compact quasi-separated scheme `C`. For each of them
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_finite`
applies.
(blueprint: `theorem-cohomology-curves--2`) -/
theorem subsingleton_sheafH_two_lowerStar (f : C ⟶ Spec (.of k)) [IsConnectedCurve f]
    [Smooth f] [IsAffine C] [IsIntegral C]
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    Subsingleton
      (Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2) := by
  classical
  set η := C.fromSpecFunctionField
  let R := (η)_*[AddCommGrpCat.{u + 1}]
  let D := Scheme.SplitFamily.diagram M ⋙ R
  let c := R.mapCocone (Scheme.SplitFamily.cocone M)
  have : ∀ j, Mono (c.ι.app j) := fun j ↦
    have := Scheme.SplitFamily.mono_cocone_ι M j
    R.map_mono ((Scheme.SplitFamily.cocone M).ι.app j)
  have hc : IsColimit c := Etale.isColimitOfMonoOfLocallySurjective' c fun V s ↦ by
    let S : Sieve V :=
      { arrows W g := ∃ (j : Scheme.SplitFamily M) (t : (D.obj j).obj.obj (op W)),
          (c.ι.app j).hom.app (op W) t = c.pt.obj.map g.op s
        downward_closed := by
          rintro W W' g ⟨j, t, ht⟩ h
          refine ⟨j, (D.obj j).obj.map h.op t, ?_⟩
          rw [NatTrans.naturality_apply, ht]
          exact Scheme.FieldTrace.map_map_apply c.pt.obj h g s }
    refine ⟨S, Etale.mem_smallEtaleTopology_of_forall_isAffine _ fun W g hW ↦ ?_, fun _ _ h ↦ h⟩
    let Y := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ η).obj W
    let x : M.obj.obj (op Y) := c.pt.obj.map g.op s
    have : IsAffine Y.left := isAffine_fromSpecFunctionField_etale_obj W
    have : DiscreteTopology Y.left := inferInstanceAs (DiscreteTopology
      (Y : (Spec (CommRingCat.of C.functionField)).Etale).left)
    have : Finite Y.left := finite_of_compact_of_discrete
    have := Fintype.ofFinite Y.left
    have hy (y : Y.left) : ∃ j : Scheme.SplitFamily M,
        M.obj.map (Scheme.pointι Y y).op x ∈ j.1 (Scheme.pointObj Y y) := by
      obtain ⟨L, _, _, _, _, B, hB, ht, hmem⟩ := Scheme.exists_mem_splitSubgroup hM
        (M.obj.map (Scheme.pointι Y y).op x)
      exact ⟨⟨_, L, inferInstance, inferInstance, inferInstance, inferInstance, B, hB, ht, rfl⟩,
        hmem⟩
    choose jy hjy using hy
    obtain ⟨j, hj⟩ := Finset.exists_le (Finset.univ.image jy)
    have hjy' (y : Y.left) := hj (jy y) (Finset.mem_image_of_mem _ (Finset.mem_univ y))
    have hxdef : x = c.pt.obj.map g.op s := rfl
    clear_value x
    rcases j with ⟨_, L, _, _, _, _, B, hB, ht, rfl⟩
    have hx : x ∈ Scheme.splitSubgroup M L (Scheme.orbitClosure M L B) Y :=
      Scheme.mem_splitSubgroup_of_pointι fun y ↦ hjy' y _ (hjy y)
    exact ⟨⟨_, L, inferInstance, inferInstance, inferInstance, inferInstance, B, hB, ht, rfl⟩,
      ⟨x, hx⟩, hxdef⟩
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have := essentiallySmallSelf.{u + 1} (Scheme.SplitFamily M)
  obtain ⟨j, y, rfl⟩ := (Scheme.H_map_isColimit_of_isFiltered_of_large C hc 2).1 x
  obtain ⟨L, _, _, _, _, hL, hfin⟩ := Scheme.SplitFamily.exists_isSplitBy j
  have := subsingleton_sheafH_two_lowerStar_of_isSplitBy_of_finite f L _ hL
  rw [Subsingleton.elim (h := this) y 0, map_zero]

end IsConnectedCurve

end AlgebraicGeometry
