/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import WeilConjectures.CategoryTheory.Sites.TorsionSheafConstantModule
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The structure sheaf, `𝔾ₘ` and `μ_N` on the small pro-étale site

Let `S` be a scheme and `S_proét` its small pro-étale site (`AlgebraicGeometry.Scheme.ProEt`).

* The structure sheaf `𝒪_S` on `S_proét` sends a weakly étale `U ⟶ S` to `Γ(U, 𝒪_U)`; it is a
  sheaf since `Γ` is a sheaf for the big pro-étale topology, which is subcanonical.
* The multiplicative group `𝔾_{m,S} = 𝒪_S^×` sends `U` to `Γ(U, 𝒪_U)ˣ`, written additively and
  lifted a universe; it is a sheaf since the functor of units preserves limits.
* The sheaf `μ_{N,S}` of `N`-th roots of unity is the kernel of the `N`-th power map
  `N • 𝟙 : 𝔾_{m,S} ⟶ 𝔾_{m,S}`; its sections over `U` are the `N`-th roots of unity of
  `Γ(U, 𝒪_U)`. It is killed by `N`, hence a sheaf of `(ℤ/N)_S`-modules
  (`CategoryTheory.Sheaf.torsionSheaf_constantModule`). For `N ∣ N'` the map
  `u ↦ u ^ (N' / N)` is a morphism `μ_{N'} ⟶ μ_N`, and for a prime `ℓ` the `μ_{ℓ^r}` form an
  inverse system.

The étale versions are `AlgebraicGeometry.Scheme.gmSheaf` and
`AlgebraicGeometry.Scheme.rootsOfUnitySheaf`.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.structureSheaf`: the structure sheaf `𝒪_S` on `S_proét`.
- `AlgebraicGeometry.Scheme.ProEt.gmSheaf`: the multiplicative group `𝔾_{m,S}`.
- `AlgebraicGeometry.Scheme.ProEt.rootsOfUnitySheaf`: the sheaf `μ_{N,S}`.
- `AlgebraicGeometry.Scheme.ProEt.rootsOfUnityModule`: `μ_{N,S}` as a sheaf of
  `(ℤ/M)_S`-modules, for `N ∣ M`.
- `AlgebraicGeometry.Scheme.ProEt.rootsOfUnityTransition`: `μ_{N d} ⟶ μ_N`, `u ↦ u ^ d`.
- `AlgebraicGeometry.Scheme.ProEt.rootsOfUnityTower`: the inverse system `(μ_{ℓ^r})_r`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable (S : Scheme.{u})

/-- The structure presheaf `U ↦ Γ(U, 𝒪_U)` on the small pro-étale site of `S`, with
restriction along `h : V ⟶ U` the ring map `h^♯` on global sections. -/
noncomputable def structurePresheaf : S.ProEtᵒᵖ ⥤ CommRingCat.{u} :=
  (ProEt.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ

lemma structurePresheaf_obj (U : S.ProEt) : (structurePresheaf S).obj (op U) = Γ(U.left, ⊤) :=
  rfl

lemma structurePresheaf_map {U V : S.ProEt} (h : V ⟶ U) :
    (structurePresheaf S).map h.op = h.left.appTop :=
  rfl

/-- The structure presheaf is a sheaf for the pro-étale topology. -/
theorem isSheaf_structurePresheaf : Presheaf.IsSheaf (ProEt.topology S) (structurePresheaf S) :=
  Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ (isSheaf_Γ proetaleTopology)

/-- The structure sheaf `𝒪_S` on the small pro-étale site `S_proét`: the sheaf of commutative
rings `U ↦ Γ(U, 𝒪_U)`, whose restriction along `h: V ⟶ U` is `h^♯` on global sections. -/
noncomputable def structureSheaf : Sheaf (ProEt.topology S) CommRingCat.{u} :=
  ⟨structurePresheaf S, isSheaf_structurePresheaf S⟩

/-- The presheaf `𝔾ₘ` on the small pro-étale site of `S`: `U ↦ Γ(U, 𝒪_U)ˣ`, written additively
and lifted to the next universe. -/
noncomputable def gmPresheaf : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  structurePresheaf S ⋙ CommRingCat.unitsAddCommGrpULift.{u + 1, u}

lemma gmPresheaf_obj (U : S.ProEt) :
    (gmPresheaf S).obj (op U) = AddCommGrpCat.of (ULift.{u + 1} (Additive Γ(U.left, ⊤)ˣ)) :=
  rfl

/-- Restriction in `𝔾ₘ` along `h : V ⟶ U` is pullback of functions along `h`. -/
lemma gmPresheaf_map_apply {U V : S.ProEt} (h : V ⟶ U) (x : (gmPresheaf S).obj (op U)) :
    (((Additive.toMul ((gmPresheaf S).map h.op x).down : Γ(V.left, ⊤)ˣ)) : Γ(V.left, ⊤)) =
      h.left.appTop ((Additive.toMul x.down : Γ(U.left, ⊤)ˣ) : Γ(U.left, ⊤)) :=
  rfl

/-- The multiplicative group `𝔾_{m,S} = 𝒪_S^×` on `S_proét`: the sheaf of abelian groups
`U ↦ Γ(U, 𝒪_U)ˣ` with the restriction maps of `𝒪_S`. The group of units is written
additively, as `Additive Γ(U, 𝒪_U)ˣ`, and lifted to the universe of the pro-étale sheaves of
abelian groups. -/
noncomputable def gmSheaf : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  ⟨gmPresheaf S, Presheaf.isSheaf_comp_of_isSheaf _ _ _ (isSheaf_structurePresheaf S)⟩

variable (N : ℕ)

/-- The sheaf `μ_{N,S}` of `N`-th roots of unity on the small pro-étale site: the kernel of the
`N`-th power map `[N] = N • 𝟙: 𝔾_{m,S} ⟶ 𝔾_{m,S}` (written additively). Its sections over `U`
are the `N`-th roots of unity of `Γ(U, 𝒪_U)`
(`AlgebraicGeometry.Scheme.ProEt.rootsOfUnitySheafSectionsEquiv`). -/
noncomputable def rootsOfUnitySheaf : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  kernel (N • 𝟙 (gmSheaf S))

/-- The sheaf `μ_N` is killed by `N`. -/
lemma nsmul_id_rootsOfUnitySheaf : N • 𝟙 (rootsOfUnitySheaf S N) = 0 := by
  rw [← cancel_mono (kernel.ι (N • 𝟙 (gmSheaf S))), Preadditive.nsmul_comp, Category.id_comp,
    zero_comp, ← Category.comp_id (kernel.ι _), ← Preadditive.comp_nsmul, kernel.condition]

/-- The sections of `μ_N` are killed by `N`. -/
lemma nsmul_rootsOfUnitySheaf_eq_zero (U : S.ProEtᵒᵖ)
    (x : (rootsOfUnitySheaf S N).obj.obj U) : N • x = 0 := by
  have h := congrArg (fun f : rootsOfUnitySheaf S N ⟶ rootsOfUnitySheaf S N ↦ f.hom.app U x)
    (nsmul_id_rootsOfUnitySheaf S N)
  exact h

/-- The `N`-th power map `N • 𝟙` of `𝔾ₘ` on sections is `x ↦ N • x`, i.e. `u ↦ u ^ N`. -/
lemma nsmul_id_gmSheaf_app_apply (U : S.ProEtᵒᵖ) (x : (gmSheaf S).obj.obj U) :
    (N • 𝟙 (gmSheaf S)).hom.app U x = N • x :=
  rfl

section Sections

variable (U : S.ProEt)

/-- Evaluation of the underlying presheaf at `U`. -/
noncomputable abbrev evalAt :
    Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op U)

/-- The sections of `μ_N` over `U` are the kernel of `N` on `𝔾ₘ(U)`. -/
noncomputable def sectionsIsoKer :
    (rootsOfUnitySheaf S N).obj.obj (op U) ≅
      AddCommGrpCat.of ((N • 𝟙 (gmSheaf S)).hom.app (op U)).hom.ker :=
  PreservesKernel.iso (evalAt S U) (N • 𝟙 (gmSheaf S)) ≪≫
    AddCommGrpCat.kernelIsoKer ((evalAt S U).map (N • 𝟙 (gmSheaf S)))

lemma sectionsIsoKer_hom_apply (x : (rootsOfUnitySheaf S N).obj.obj (op U)) :
    (((sectionsIsoKer S N U).hom x : ((N • 𝟙 (gmSheaf S)).hom.app (op U)).hom.ker) :
      (gmSheaf S).obj.obj (op U)) = (kernel.ι (N • 𝟙 (gmSheaf S))).hom.app (op U) x := by
  have h : (sectionsIsoKer S N U).hom ≫
      AddCommGrpCat.ofHom (AddSubgroup.subtype ((evalAt S U).map (N • 𝟙 (gmSheaf S))).hom.ker) =
        (evalAt S U).map (kernel.ι (N • 𝟙 (gmSheaf S))) := by
    rw [sectionsIsoKer, Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h x

/-- The `N`-torsion of `𝔾ₘ(U)` is the group of `N`-th roots of unity of `Γ(U, 𝒪_U)`. -/
def kerEquivRootsOfUnity :
    ((N • 𝟙 (gmSheaf S)).hom.app (op U)).hom.ker ≃+ Additive (rootsOfUnity N Γ(U.left, ⊤)) where
  toFun x := Additive.ofMul ⟨Additive.toMul x.1.down, by
    rw [mem_rootsOfUnity, ← toMul_nsmul]
    have := x.2
    rw [AddMonoidHom.mem_ker, nsmul_id_gmSheaf_app_apply] at this
    rw [show N • x.1.down = (N • x.1).down from rfl, this]
    rfl⟩
  invFun ζ := ⟨⟨Additive.ofMul (Additive.toMul ζ).1⟩, by
    rw [AddMonoidHom.mem_ker, nsmul_id_gmSheaf_app_apply]
    refine ULift.ext ?_
    change Additive.ofMul ((Additive.toMul ζ).1 ^ N) = 0
    rw [(mem_rootsOfUnity _ _).1 (Additive.toMul ζ).2]
    rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The sections of `μ_{N,S}` over `U` are the `N`-th roots of unity of `Γ(U, 𝒪_U)`. -/
noncomputable def rootsOfUnitySheafSectionsEquiv :
    (rootsOfUnitySheaf S N).obj.obj (op U) ≃+ Additive (rootsOfUnity N Γ(U.left, ⊤)) :=
  (sectionsIsoKer S N U).addCommGroupIsoToAddEquiv.trans (kerEquivRootsOfUnity S N U)

/-- Under `AlgebraicGeometry.Scheme.ProEt.rootsOfUnitySheafSectionsEquiv`, a section of `μ_N`
is the unit given by its image in `𝔾ₘ`. -/
lemma rootsOfUnitySheafSectionsEquiv_apply (x : (rootsOfUnitySheaf S N).obj.obj (op U)) :
    ((Additive.toMul (rootsOfUnitySheafSectionsEquiv S N U x) :
      rootsOfUnity N Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) =
      Additive.toMul ((kernel.ι (N • 𝟙 (gmSheaf S))).hom.app (op U) x).down := by
  rw [← sectionsIsoKer_hom_apply]
  simp only [rootsOfUnitySheafSectionsEquiv, AddEquiv.trans_apply,
]
  rfl

end Sections

/-- The `N`-th roots of unity form a sheaf of `(ℤ/M)_S`-modules for every multiple `M` of
`N`. -/
noncomputable def rootsOfUnityModule (M : ℕ) (h : N ∣ M) :
    SheafOfModules.{u + 1} (Sheaf.constantZModSheaf.{u + 1} (ProEt.topology S) M) :=
  Sheaf.constantZModModuleOfNsmul (rootsOfUnitySheaf S N) fun U x ↦ by
    obtain ⟨d, rfl⟩ := h
    rw [mul_comm, mul_nsmul, nsmul_rootsOfUnitySheaf_eq_zero]

/-- The underlying abelian sheaf of `AlgebraicGeometry.Scheme.ProEt.rootsOfUnityModule` is
`μ_N`. -/
noncomputable def toSheafRootsOfUnityModuleIso (M : ℕ) (h : N ∣ M) :
    (SheafOfModules.toSheaf _).obj (rootsOfUnityModule S N M h) ≅ rootsOfUnitySheaf S N :=
  Sheaf.toSheafConstantZModModuleOfNsmulIso _ _

/-- The transition map `μ_{N d} ⟶ μ_N`, `u ↦ u ^ d`: it is well defined since
`(u ^ d) ^ N = u ^ {N d} = 1`. -/
noncomputable def rootsOfUnityTransition (d : ℕ) :
    rootsOfUnitySheaf S (N * d) ⟶ rootsOfUnitySheaf S N :=
  kernel.lift _ (kernel.ι ((N * d) • 𝟙 (gmSheaf S)) ≫ (d • 𝟙 (gmSheaf S))) (by
    have h := kernel.condition ((N * d) • 𝟙 (gmSheaf S))
    rw [Preadditive.comp_nsmul, Category.comp_id] at h
    simp only [Preadditive.comp_nsmul, Category.comp_id, smul_smul]
    exact h)

@[reassoc (attr := simp)]
lemma rootsOfUnityTransition_ι (d : ℕ) :
    rootsOfUnityTransition S N d ≫ kernel.ι (N • 𝟙 (gmSheaf S)) =
      kernel.ι ((N * d) • 𝟙 (gmSheaf S)) ≫ (d • 𝟙 (gmSheaf S)) :=
  kernel.lift_ι _ _ _

/-- On sections, the transition map is `u ↦ u ^ d`. -/
lemma rootsOfUnityTransition_apply (d : ℕ) (U : S.ProEt)
    (x : (rootsOfUnitySheaf S (N * d)).obj.obj (op U)) :
    ((Additive.toMul (rootsOfUnitySheafSectionsEquiv S N U
      ((rootsOfUnityTransition S N d).hom.app (op U) x)) :
        rootsOfUnity N Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) =
      ((Additive.toMul (rootsOfUnitySheafSectionsEquiv S (N * d) U x) :
        rootsOfUnity (N * d) Γ(U.left, ⊤)) : Γ(U.left, ⊤)ˣ) ^ d := by
  rw [rootsOfUnitySheafSectionsEquiv_apply, rootsOfUnitySheafSectionsEquiv_apply,
  ]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op U)) (rootsOfUnityTransition_ι S N d)) x
  exact (congrArg (fun y ↦ (Additive.toMul (ULift.down y) : Γ(U.left, ⊤)ˣ)) h).trans rfl

/-- The transition map `μ_{N d} ⟶ μ_N` as a morphism of sheaves of `(ℤ/(N d))_S`-modules. -/
noncomputable def rootsOfUnityModuleTransition (d : ℕ) [NeZero (N * d)] :
    rootsOfUnityModule S (N * d) (N * d) dvd_rfl ⟶
      rootsOfUnityModule S N (N * d) (dvd_mul_right N d) :=
  Sheaf.fullyFaithfulToSheafConstantZMod.preimage
    ((toSheafRootsOfUnityModuleIso S _ _ _).hom ≫ rootsOfUnityTransition S N d ≫
      (toSheafRootsOfUnityModuleIso S _ _ _).inv)

lemma toSheaf_map_rootsOfUnityModuleTransition (d : ℕ) [NeZero (N * d)] :
    (SheafOfModules.toSheaf _).map (rootsOfUnityModuleTransition S N d) =
      (toSheafRootsOfUnityModuleIso S _ _ _).hom ≫ rootsOfUnityTransition S N d ≫
        (toSheafRootsOfUnityModuleIso S _ _ _).inv :=
  Sheaf.fullyFaithfulToSheafConstantZMod.map_preimage _

/-- For a prime `ℓ`, the inverse system `(μ_{ℓ^r, S})_r` with the transition maps
`μ_{ℓ^{r+1}} ⟶ μ_{ℓ^r}`, `u ↦ u ^ ℓ`. -/
noncomputable def rootsOfUnityTower (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun r ↦ rootsOfUnitySheaf S (ℓ ^ r))
    fun r ↦ rootsOfUnityTransition S (ℓ ^ r) ℓ

lemma rootsOfUnityTower_obj (ℓ r : ℕ) :
    (rootsOfUnityTower S ℓ).obj (op r) = rootsOfUnitySheaf S (ℓ ^ r) :=
  rfl

lemma rootsOfUnityTower_map (ℓ r : ℕ) :
    (rootsOfUnityTower S ℓ).map (homOfLE (Nat.le_succ r)).op =
      rootsOfUnityTransition S (ℓ ^ r) ℓ :=
  Functor.ofOpSequence_map_homOfLE_succ _ r

end AlgebraicGeometry.Scheme.ProEt
