/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Gluing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Extending finite étale schemes along a morphism inducing a surjection on `π₁`

Let `f : U ⟶ V` be a morphism of connected schemes for which the induced map
`ρ : π₁(U, s) → π₁(V, t)` (along a path `τ`) is surjective. A finite étale `U`-scheme `Z` on
whose geometric fibre the kernel of `ρ` acts trivially is the base change of a finite étale
`V`-scheme (`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_iso_of_ker_smul`): the action of
`π₁(U, s)` on the fibre of `Z` descends to `π₁(V, t)`, and the corresponding finite étale
`V`-scheme pulls back to `Z` by the Galois correspondence.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {U V : Scheme.{u}} [ConnectedSpace U] [ConnectedSpace V] {f : U ⟶ V}
  {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  {s : Spec (.of Ω) ⟶ U} {t : Spec (.of Ω') ⟶ V} (τ : pullback f ⋙ fiber s ≅ fiber t)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber s).obj P)] [IsFundamentalGroup (fiber s) GU]
  (GV : Type u) [Group GV] [TopologicalSpace GV] [IsTopologicalGroup GV] [CompactSpace GV]
  [∀ P, MulAction GV ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GV]

open scoped FintypeCatDiscrete in
/-- **Extension of finite étale schemes**: if `ρ : π₁(U, s) → π₁(V, t)` is surjective and its
kernel acts trivially on the geometric fibre of a finite étale `U`-scheme `Z`, then `Z` is the
base change of a finite étale `V`-scheme. -/
theorem exists_pullback_iso_of_ker_smul (hρ : Function.Surjective (fundamentalGroupMap τ GU GV))
    (Z : U.FiniteEtale)
    (hZ : ∀ g ∈ (fundamentalGroupMap τ GU GV).ker, ∀ x : (fiber s).obj Z, g • x = x) :
    ∃ ZV : V.FiniteEtale, Nonempty ((pullback f).obj ZV ≅ Z) := by
  classical
  let ρ := fundamentalGroupMap τ GU GV
  have : T2Space GV := (toAutHomeo (fiber t) GV).isEmbedding.t2Space
  have hcU : ∀ P, ContinuousSMul GU ((fiber s).obj P) := fun P ↦
    IsFundamentalGroup.continuous_smul P
  have hρc : Continuous ρ := continuous_fundamentalGroupMap τ GU GV
  let σ := Function.surjInv hρ
  have hσ (h : GV) : ρ (σ h) = h := Function.surjInv_eq hρ h
  let X := (fiber s).obj Z
  -- elements with the same image act in the same way
  have hsame {g g' : GU} (h : ρ g = ρ g') (x : X) : g • x = g' • x := by
    have hk : g'⁻¹ * g ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    calc g • x = g' • (g'⁻¹ * g) • x := by rw [smul_smul, mul_inv_cancel_left]
      _ = g' • x := by rw [hZ _ hk x]
  let act : MulAction GV X :=
    { smul h x := σ h • x
      one_smul x := by
        change σ 1 • x = x
        rw [hsame (g' := 1) (by rw [hσ, map_one]), one_smul]
      mul_smul h₁ h₂ x := by
        change σ (h₁ * h₂) • x = σ h₁ • σ h₂ • x
        rw [← mul_smul]
        exact hsame (by rw [hσ, map_mul, hσ, hσ]) x }
  have hact (g : GU) (x : X) : (ρ g • x : X) = g • x := hsame (hσ _) x
  -- the action of `GV` is continuous
  have hcont : ContinuousSMul GV X := by
    refine ⟨continuous_prod_of_discrete_right.mpr fun x ↦ continuous_discrete_rng.mpr fun y ↦ ?_⟩
    have hpre : (fun h : GV ↦ (h • x : X)) ⁻¹' {y} = ρ '' {g : GU | g • x = y} := by
      ext h
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
      refine ⟨fun hh ↦ ⟨σ h, hh, hσ h⟩, ?_⟩
      rintro ⟨g, hg, rfl⟩
      rw [hact, hg]
    have hcompl : ((fun h : GV ↦ (h • x : X)) ⁻¹' {y})ᶜ = ρ '' {g : GU | g • x ≠ y} := by
      ext h
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
        Set.mem_ofPred_eq]
      refine ⟨fun hh ↦ ⟨σ h, hh, hσ h⟩, ?_⟩
      rintro ⟨g, hg, rfl⟩
      rwa [hact]
    have hcl₂ : IsClosed {g : GU | g • x ≠ y} :=
      (isOpen_discrete {y}).preimage (continuous_id.smul continuous_const) |>.isClosed_compl
    rw [← isClosed_compl_iff, hcompl]
    exact (hcl₂.isCompact.image hρc).isClosed
  -- the finite étale `V`-scheme attached to the `π₁(V, t)`-set `X`
  let Xc : ContAction FintypeCat.{u} GV :=
    ⟨Action.FintypeCat.ofMulAction GV ((fiber s).obj Z), by
      constructor
      exact hcont.continuous_smul⟩
  let EV := equivalenceContAction t GV
  let ZV := EV.inverse.obj Xc
  let c := EV.counitIso.app Xc
  let φ : (fiber s).obj ((pullback f).obj ZV) → X := fun y ↦ c.hom.hom.hom (τ.hom.app ZV y)
  have hφ : Function.Bijective φ :=
    (FintypeCat.equivEquivIso.symm
      ((ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso c)).bijective.comp
      (FintypeCat.equivEquivIso.symm (τ.app ZV)).bijective
  have hφg (g : GU) (y : (fiber s).obj ((pullback f).obj ZV)) : φ (g • y) = g • φ y := by
    have hc := congrArg (fun k ↦ k.hom (τ.hom.app ZV y)) (c.hom.hom.comm (ρ g))
    simp only [φ, ← fundamentalGroupMap_smul τ GU GV]
    refine hc.trans ?_
    exact hact g _
  let EU := equivalenceContAction s GU
  let I : EU.functor.obj ((pullback f).obj ZV) ≅ EU.functor.obj Z :=
    ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso (Equiv.ofBijective φ hφ))
      fun g ↦ FintypeCat.hom_ext _ _ fun y ↦ hφg g y)
  exact ⟨ZV, ⟨EU.fullyFaithfulFunctor.preimageIso I⟩⟩

section Fixing

variable {U Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)
  (k : U ⟶ Y) (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)]

/-- The elements of `π₁(U, s)` acting trivially on the geometric fibres of all base changes of
finite étale `Y`-schemes along `k : U ⟶ Y`: the kernel of `π₁(U, s) → π₁(Y)`. -/
def fixingSubgroup : Subgroup G where
  carrier := {g | ∀ (P : Y.FiniteEtale) (x : (fiber s).obj ((pullback k).obj P)), g • x = x}
  mul_mem' {g h} hg hh P x := by
    rw [mul_smul, hh, hg]
  one_mem' P x := one_smul G x
  inv_mem' {g} hg P x := by
    conv_lhs => rw [← hg P x]
    exact inv_smul_smul g x

lemma mem_fixingSubgroup_iff {g : G} :
    g ∈ fixingSubgroup s k G ↔
      ∀ (P : Y.FiniteEtale) (x : (fiber s).obj ((pullback k).obj P)), g • x = x :=
  Iff.rfl

instance : (fixingSubgroup s k G).Normal where
  conj_mem g hg h P x := by
    rw [mul_smul, mul_smul, hg, smul_inv_smul]

lemma isClosed_fixingSubgroup [TopologicalSpace G] [∀ P, ContinuousSMul G ((fiber s).obj P)] :
    IsClosed (fixingSubgroup s k G : Set G) := by
  have : (fixingSubgroup s k G : Set G) =
      ⋂ (P : Y.FiniteEtale) (x : (fiber s).obj ((pullback k).obj P)), {g : G | g • x = x} := by
    ext g
    simp [mem_fixingSubgroup_iff]
  rw [this]
  exact isClosed_iInter fun P ↦ isClosed_iInter fun x ↦
    isClosed_eq (continuous_id.smul continuous_const) continuous_const


variable [IsNaturalSMul (fiber s) G]

/-- An element fixing the geometric fibre of a finite étale scheme fixes that of any isomorphic
one. -/
lemma smul_eq_self_of_iso {P Q : U.FiniteEtale} (e : P ≅ Q) {g : G}
    (h : ∀ x : (fiber s).obj P, g • x = x) (y : (fiber s).obj Q) : g • y = y := by
  obtain ⟨x, rfl⟩ : ∃ x, (fiber s).map e.hom x = y :=
    ⟨(fiber s).map e.inv y, ConcreteCategory.congr_hom ((fiber s).mapIso e).inv_hom_id y⟩
  rw [← IsNaturalSMul.naturality, h]

lemma fixingSubgroup_le_comp (m : Y ⟶ Y') : fixingSubgroup s k G ≤ fixingSubgroup s (k ≫ m) G :=
  fun _ hg P ↦ smul_eq_self_of_iso s G (pullbackCompIso k m P).symm (hg _)

variable [ConnectedSpace Y] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {t : Spec (.of Ω') ⟶ Y}
  (τ : pullback k ⋙ fiber s ≅ fiber t)
  (GY : Type u) [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
  [∀ P, MulAction GY ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GY]

/-- The kernel of the map `π₁(U, s) → π₁(Y, t)` induced by `k` is the subgroup of elements acting
trivially on the base changes of finite étale `Y`-schemes. -/
lemma ker_fundamentalGroupMap : (fundamentalGroupMap τ G GY).ker = fixingSubgroup s k G := by
  ext g
  rw [MonoidHom.mem_ker, mem_fixingSubgroup_iff]
  constructor
  · intro hg P x
    apply ((ConcreteCategory.isIso_iff_bijective (τ.hom.app P)).1 inferInstance).1
    rw [← fundamentalGroupMap_smul τ G GY, hg, one_smul]
  · intro hg
    refine IsFundamentalGroup.non_trivial (F := fiber t) _ fun P y ↦ ?_
    obtain ⟨x, rfl⟩ : ∃ x, τ.hom.app P x = y :=
      ⟨τ.inv.app P y, ConcreteCategory.congr_hom (τ.inv_hom_id_app P) y⟩
    rw [fundamentalGroupMap_smul, hg]

end Fixing

end AlgebraicGeometry.Scheme.FiniteEtale
