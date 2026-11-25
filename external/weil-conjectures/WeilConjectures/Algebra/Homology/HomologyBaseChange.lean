/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The base change map on homology

For a short complex `S : X₁ ⟶ X₂ ⟶ X₃` of `A`-modules and an `A`-algebra `B`, the classes
`[z] ↦ [1 ⊗ z]` of cycles define the **base change map** on homology
`B ⊗[A] H(S) ⟶ H(B ⊗[A] S)` (`CategoryTheory.ShortComplex.homologyBaseChange`). It is natural in
`S` (`CategoryTheory.ShortComplex.homologyBaseChange_naturality`), and it is bijective as soon as
tensoring with `B` preserves the left exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ X₃`
(`CategoryTheory.ShortComplex.bijective_homologyBaseChange_of_exact`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (S : ShortComplex (ModuleCat.{u} A))

/-- The base change `S_B = B ⊗[A] S` of a short complex of `A`-modules. -/
noncomputable abbrev baseChange : ShortComplex (ModuleCat.{u} B) :=
  S.map (ModuleCat.baseChange A B)

/-- The cycles `ker (1 ⊗ g)` of the base change, as a submodule of `B ⊗[A] X₂`. -/
noncomputable abbrev cyclesBaseChange : Submodule B (B ⊗[A] S.X₂) :=
  LinearMap.ker (S.g.hom.baseChange B)

/-- The boundaries of the base change, as a submodule of its cycles. -/
noncomputable abbrev boundariesBaseChange : Submodule B (S.cyclesBaseChange B) :=
  LinearMap.range ((S.f.hom.baseChange B).codRestrict (S.cyclesBaseChange B) fun x ↦
    congr($((S.baseChange B).zero).hom x))

/-- The map `z ↦ 1 ⊗ z` from the cycles of `S` to the cycles of `B ⊗[A] S`. -/
noncomputable def baseChangeCycles :
    LinearMap.ker S.g.hom →ₗ[A] S.cyclesBaseChange B where
  toFun z := ⟨(1 : B) ⊗ₜ (z : S.X₂), by
    rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.1 z.2, tmul_zero]⟩
  map_add' x y := Subtype.ext (tmul_add _ _ _)
  map_smul' a x := Subtype.ext (tmul_smul a (1 : B) (x : S.X₂))

@[simp]
lemma baseChangeCycles_apply_coe (z : LinearMap.ker S.g.hom) :
    (S.baseChangeCycles B z : B ⊗[A] S.X₂) = (1 : B) ⊗ₜ (z : S.X₂) :=
  rfl

lemma baseChangeCycles_mem (x : S.X₁) :
    S.baseChangeCycles B (S.moduleCatToCycles x) ∈ S.boundariesBaseChange B :=
  ⟨(1 : B) ⊗ₜ x, Subtype.ext rfl⟩

/-- The base change map on the explicit homology `ker g ⧸ im f`. -/
noncomputable def homologyBaseChangeAux :
    B ⊗[A] (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[B]
      (S.cyclesBaseChange B ⧸ S.boundariesBaseChange B) :=
  LinearMap.liftBaseChange B ((LinearMap.range S.moduleCatToCycles).liftQ
    (((S.boundariesBaseChange B).mkQ.restrictScalars A) ∘ₗ S.baseChangeCycles B) (by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact S.baseChangeCycles_mem B x))

lemma homologyBaseChangeAux_tmul (b : B) (z : LinearMap.ker S.g.hom) :
    S.homologyBaseChangeAux B (b ⊗ₜ Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (b • S.baseChangeCycles B z) := by
  rw [homologyBaseChangeAux, LinearMap.liftBaseChange_tmul, Submodule.liftQ_apply,
    Submodule.Quotient.mk_smul]
  rfl
/-- **The base change map on homology** `B ⊗[A] H(S) ⟶ H(B ⊗[A] S)`, `b ⊗ [z] ↦ [b ⊗ z]`. -/
noncomputable def homologyBaseChange :
    B ⊗[A] S.homology →ₗ[B] (S.baseChange B).homology :=
  (S.baseChange B).moduleCatHomologyIso.inv.hom ∘ₗ S.homologyBaseChangeAux B ∘ₗ
    S.moduleCatHomologyIso.hom.hom.baseChange B

lemma bijective_homologyBaseChange_iff :
    Function.Bijective (S.homologyBaseChange B) ↔
      Function.Bijective (S.homologyBaseChangeAux B) := by
  let e₁ : B ⊗[A] S.homology ≃ₗ[B]
      B ⊗[A] (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.baseChange A B _ _
  let e₂ := (S.baseChange B).moduleCatHomologyIso.toLinearEquiv
  have h : S.homologyBaseChange B = e₂.symm.toLinearMap ∘ₗ S.homologyBaseChangeAux B ∘ₗ
      e₁.toLinearMap := rfl
  rw [h, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e₂.symm.bijective.of_comp_iff', e₁.bijective.of_comp_iff]
  exact Iff.rfl

/-- The comparison map `B ⊗[A] ker g ⟶ ker (1 ⊗ g)`. -/
noncomputable def cyclesBaseChangeMap :
    B ⊗[A] LinearMap.ker S.g.hom →ₗ[B] S.cyclesBaseChange B :=
  LinearMap.liftBaseChange B (S.baseChangeCycles B)

lemma coe_cyclesBaseChangeMap (x : B ⊗[A] LinearMap.ker S.g.hom) :
    (S.cyclesBaseChangeMap B x : B ⊗[A] S.X₂) =
      (LinearMap.ker S.g.hom).subtype.lTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b z =>
    rw [cyclesBaseChangeMap, LinearMap.liftBaseChange_tmul, Submodule.coe_smul,
      baseChangeCycles_apply_coe, LinearMap.lTensor_tmul, smul_tmul', smul_eq_mul, mul_one]
    rfl
  | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy]

lemma homologyBaseChangeAux_lTensor_mkQ (x : B ⊗[A] LinearMap.ker S.g.hom) :
    S.homologyBaseChangeAux B ((LinearMap.range S.moduleCatToCycles).mkQ.lTensor B x) =
      Submodule.Quotient.mk (S.cyclesBaseChangeMap B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b z =>
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply, homologyBaseChangeAux_tmul,
      cyclesBaseChangeMap, LinearMap.liftBaseChange_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Submodule.Quotient.mk_add]

lemma cyclesBaseChangeMap_lTensor_toCycles (y : B ⊗[A] S.X₁) :
    S.cyclesBaseChangeMap B (S.moduleCatToCycles.lTensor B y) =
      (S.f.hom.baseChange B).codRestrict (S.cyclesBaseChange B) (fun x ↦
        congr($((S.baseChange B).zero).hom x)) y := by
  refine Subtype.ext ?_
  rw [coe_cyclesBaseChangeMap, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    LinearMap.codRestrict_apply, LinearMap.baseChange_eq_lTensor]
  rfl

/-- **Criterion for the base change map to be bijective.** If tensoring with `B` preserves the
left exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ X₃`, the base change map on homology is bijective. -/
theorem bijective_homologyBaseChangeAux_of_exact
    (hinj : Function.Injective ((LinearMap.ker S.g.hom).subtype.lTensor B))
    (hex : Function.Exact ((LinearMap.ker S.g.hom).subtype.lTensor B) (S.g.hom.lTensor B)) :
    Function.Bijective (S.homologyBaseChangeAux B) := by
  have hj (x y : B ⊗[A] LinearMap.ker S.g.hom)
      (h : S.cyclesBaseChangeMap B x = S.cyclesBaseChangeMap B y) : x = y := by
    refine hinj ?_
    rw [← coe_cyclesBaseChangeMap, ← coe_cyclesBaseChangeMap, h]
  have hj' (y : S.cyclesBaseChange B) : ∃ x, S.cyclesBaseChangeMap B x = y := by
    have hy : S.g.hom.lTensor B (y : B ⊗[A] S.X₂) = 0 := by
      rw [← LinearMap.baseChange_eq_lTensor]
      exact y.2
    obtain ⟨x, hx⟩ := (hex _).1 hy
    exact ⟨x, Subtype.ext ((coe_cyclesBaseChangeMap _ _ _).trans hx)⟩
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective B
      (Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles)) w
    rw [LinearMap.mem_ker, homologyBaseChangeAux_lTensor_mkQ,
      Submodule.Quotient.mk_eq_zero] at hw
    obtain ⟨y, hy⟩ := hw
    have hxy : x = S.moduleCatToCycles.lTensor B y :=
      hj _ _ (by rw [cyclesBaseChangeMap_lTensor_toCycles]; exact hy.symm)
    rw [hxy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.mem_bot]
    have : (LinearMap.range S.moduleCatToCycles).mkQ ∘ₗ S.moduleCatToCycles = 0 := by
      ext x
      simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  · intro h
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ h
    obtain ⟨x, rfl⟩ := hj' y
    exact ⟨_, S.homologyBaseChangeAux_lTensor_mkQ B x⟩

section Naturality

variable {R : Type u} [Ring R]

lemma moduleCatHomologyIso_inv_mk (T : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker T.g.hom) :
    T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) =
      T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom z) :=
  (T.moduleCatCyclesIso_inv_π_apply z).symm

lemma iCycles_moduleCatCyclesIso_inv (T : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker T.g.hom) : T.iCycles.hom (T.moduleCatCyclesIso.inv.hom z) = z.1 :=
  T.moduleCatCyclesIso_inv_iCycles_apply z

lemma mem_ker_τ₂ {T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (ψ : T₁ ⟶ T₂)
    (z : LinearMap.ker T₁.g.hom) : ψ.τ₂.hom z.1 ∈ LinearMap.ker T₂.g.hom := by
  have h := congr($(ψ.comm₂₃).hom z.1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.1 z.2,
    map_zero] at h
  exact LinearMap.mem_ker.2 h

/-- The map induced on homology by a morphism of short complexes of modules sends the class of a
cycle `z` to the class of its image. -/
lemma homologyMap_moduleCatHomologyIso_inv_mk {T₁ T₂ : ShortComplex (ModuleCat.{u} R)}
    (ψ : T₁ ⟶ T₂) (z : LinearMap.ker T₁.g.hom) :
    (homologyMap ψ).hom (T₁.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      T₂.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk ⟨ψ.τ₂.hom z, mem_ker_τ₂ ψ z⟩) := by
  rw [moduleCatHomologyIso_inv_mk, moduleCatHomologyIso_inv_mk]
  have h := congr($(homologyπ_naturality ψ).hom (T₁.moduleCatCyclesIso.inv.hom z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  congr 1
  refine (ModuleCat.mono_iff_injective T₂.iCycles).1 inferInstance ?_
  have h' := congr($(cyclesMap_i ψ).hom (T₁.moduleCatCyclesIso.inv.hom z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  change T₂.iCycles.hom _ = T₂.iCycles.hom _
  rw [h', iCycles_moduleCatCyclesIso_inv, iCycles_moduleCatCyclesIso_inv]

end Naturality

lemma homologyBaseChange_tmul_mk (b : B) (z : LinearMap.ker S.g.hom) :
    S.homologyBaseChange B (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      (S.baseChange B).moduleCatHomologyIso.inv.hom
        (Submodule.Quotient.mk (b • S.baseChangeCycles B z)) := by
  have h := congr($(S.moduleCatHomologyIso.inv_hom_id).hom (Submodule.Quotient.mk z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  have h1 : (S.moduleCatHomologyIso.hom.hom.baseChange B)
      (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
        b ⊗ₜ Submodule.Quotient.mk z := by
    rw [LinearMap.baseChange_tmul, h]
  calc S.homologyBaseChange B (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z))
      = (S.baseChange B).moduleCatHomologyIso.inv.hom (S.homologyBaseChangeAux B
          ((S.moduleCatHomologyIso.hom.hom.baseChange B)
            (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)))) := rfl
    _ = (S.baseChange B).moduleCatHomologyIso.inv.hom
          (S.homologyBaseChangeAux B (b ⊗ₜ Submodule.Quotient.mk z)) := by rw [h1]
    _ = _ := by rw [homologyBaseChangeAux_tmul]

/-- **Naturality of the base change map on homology.** -/
theorem homologyBaseChange_naturality {S₁ S₂ : ShortComplex (ModuleCat.{u} A)} (φ : S₁ ⟶ S₂)
    (x : B ⊗[A] S₁.homology) :
    S₂.homologyBaseChange B ((homologyMap φ).hom.baseChange B x) =
      (homologyMap ((ModuleCat.baseChange A B).mapShortComplex.map φ)).hom
        (S₁.homologyBaseChange B x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b h =>
    obtain ⟨z, rfl⟩ : ∃ z, S₁.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) = h := by
      obtain ⟨w, hw⟩ := Submodule.mkQ_surjective _ (S₁.moduleCatHomologyIso.hom.hom h)
      refine ⟨w, ?_⟩
      have e := congr($(S₁.moduleCatHomologyIso.hom_inv_id).hom h)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] at e
      rw [← e, ← hw]
      rfl
    rw [LinearMap.baseChange_tmul, homologyMap_moduleCatHomologyIso_inv_mk,
      homologyBaseChange_tmul_mk, homologyBaseChange_tmul_mk]
    erw [homologyMap_moduleCatHomologyIso_inv_mk]
    congr 2

/-- **Flat base change commutes with homology**: for `B` flat over `A`, the base change map on
homology is bijective. -/
theorem bijective_homologyBaseChange_of_flat [Module.Flat A B] :
    Function.Bijective (S.homologyBaseChange B) := by
  rw [bijective_homologyBaseChange_iff]
  refine S.bijective_homologyBaseChangeAux_of_exact B
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
    (Module.Flat.lTensor_exact B fun x ↦ ?_)
  simp

section FieldExtension

variable (L L' : Type u) [Field L] [Field L'] [Algebra A L] [Algebra A L'] [Algebra L L']
  [IsScalarTower A L L']

/-- Base change in two steps `A ⟶ L ⟶ L'` is base change along `A ⟶ L'`. -/
noncomputable def baseChangeBaseChangeIso :
    (S.baseChange L).baseChange L' ≅ S.baseChange L' :=
  ShortComplex.isoMk (AlgebraTensorModule.cancelBaseChange A L L' L' S.X₁).toModuleIso
    (AlgebraTensorModule.cancelBaseChange A L L' L' S.X₂).toModuleIso
    (AlgebraTensorModule.cancelBaseChange A L L' L' S.X₃).toModuleIso
    (by
      ext : 1
      refine LinearMap.ext fun x ↦ ?_
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul l y =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' =>
          simp only [tmul_add, map_add] at hy hy' ⊢
          rw [hy, hy']
        | tmul a x =>
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
            ModuleCat.hom_ofHom]
          erw [AlgebraTensorModule.cancelBaseChange_tmul])
    (by
      ext : 1
      refine LinearMap.ext fun x ↦ ?_
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul l y =>
        induction y using TensorProduct.inductionOn with
        | add y y' hy hy' =>
          simp only [tmul_add, map_add] at hy hy' ⊢
          rw [hy, hy']
        | tmul a x =>
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
            ModuleCat.hom_ofHom]
          erw [AlgebraTensorModule.cancelBaseChange_tmul])

/-- **The dimension of the homology after base change to a field does not change under a field
extension.** -/
theorem finrank_homology_baseChange_eq_of_isScalarTower :
    Module.finrank L' (S.baseChange L').homology = Module.finrank L (S.baseChange L).homology := by
  rw [← (homologyMapIso (S.baseChangeBaseChangeIso L L')).toLinearEquiv.finrank_eq,
    ← (LinearEquiv.ofBijective _
      ((S.baseChange L).bijective_homologyBaseChange_of_flat L')).finrank_eq,
    Module.finrank_baseChange]

end FieldExtension

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B] {ι : Type*}
  {c : ComplexShape ι} {P C : HomologicalComplex (ModuleCat.{u} A) c} (φ : P ⟶ C) (i : ι)

/-- A morphism of complexes inducing isomorphisms in homology in degree `i`, before and after base
change to `B`, identifies the base change maps on the homology in degree `i`. -/
theorem bijective_homologyBaseChange_iff_of_quasiIsoAt [QuasiIsoAt φ i]
    [QuasiIsoAt (((ModuleCat.baseChange A B).mapHomologicalComplex c).map φ) i] :
    Function.Bijective ((P.sc i).homologyBaseChange B) ↔
      Function.Bijective ((C.sc i).homologyBaseChange B) := by
  let ψ := (shortComplexFunctor _ c i).map φ
  have h₁ : IsIso (ShortComplex.homologyMap ψ) := inferInstanceAs (IsIso (homologyMap φ i))
  have h₂ : IsIso (ShortComplex.homologyMap ((ModuleCat.baseChange A B).mapShortComplex.map ψ)) :=
    inferInstanceAs
      (IsIso (homologyMap (((ModuleCat.baseChange A B).mapHomologicalComplex c).map φ) i))
  let e₁ := (asIso (ShortComplex.homologyMap ψ)).toLinearEquiv.baseChange A B _ _
  let e₂ := (asIso (ShortComplex.homologyMap
    ((ModuleCat.baseChange A B).mapShortComplex.map ψ))).toLinearEquiv
  have hc : ⇑((C.sc i).homologyBaseChange B) ∘ ⇑e₁ =
      ⇑e₂ ∘ ⇑((P.sc i).homologyBaseChange B) :=
    funext fun x ↦ ShortComplex.homologyBaseChange_naturality B ψ x
  constructor
  · intro h
    have := e₂.bijective.comp h
    rw [← hc] at this
    exact (Function.Bijective.of_comp_iff _ e₁.bijective).1 this
  · intro h
    have := h.comp e₁.bijective
    rw [hc] at this
    exact (Function.Bijective.of_comp_iff' e₂.bijective _).1 this

/-- A quasi-isomorphism in degree `i` after base change to a field `L` does not change the
dimension of the homology. -/
theorem finrank_homology_baseChange_eq_of_quasiIsoAt (L : Type u) [Field L] [Algebra A L]
    [QuasiIsoAt (((ModuleCat.baseChange A L).mapHomologicalComplex c).map φ) i] :
    Module.finrank L ((C.sc i).baseChange L).homology =
      Module.finrank L ((P.sc i).baseChange L).homology := by
  let ψ := (shortComplexFunctor _ c i).map φ
  have h₂ : IsIso (ShortComplex.homologyMap ((ModuleCat.baseChange A L).mapShortComplex.map ψ)) :=
    inferInstanceAs
      (IsIso (homologyMap (((ModuleCat.baseChange A L).mapHomologicalComplex c).map φ) i))
  exact (asIso (ShortComplex.homologyMap
    ((ModuleCat.baseChange A L).mapShortComplex.map ψ))).toLinearEquiv.finrank_eq.symm

end HomologicalComplex
