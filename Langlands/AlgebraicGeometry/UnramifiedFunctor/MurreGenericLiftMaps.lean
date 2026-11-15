import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.KrullDimension.Zero

/-! # Lifting lemmas for Murre's Lemma 2, case (b)

Ring maps between affine test objects, and three ways to move the property "`ξ` lifts to no
larger closed subscheme" (`NoLargerLift`) between rings: along a change of the base ring
(`noLargerLift_restrictBase_iff`), from a quotient back to a local ring when the kernel is
small (`noLargerLift_of_surjective`, by Nakayama's lemma), and its proof for local artinian
rings at a point where `ξ` is infinitesimally étale (`noLargerLift_of_isArtinianRing`, using
that `Spec R' → Spec R` is formally unramified). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace GenericLift

variable {S : Scheme.{u}}

section RHom

variable {T₁ T₂ T₃ T₄ : Type u} [CommRing T₁] [CommRing T₂] [CommRing T₃] [CommRing T₄]

/-- A ring map `ψ : T₂ → T₁` as the morphism `Spec T₁ ⟶ Spec T₂` of `Over S`, for structure
morphisms `g₁`, `g₂` compatible with it. -/
def rhom {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    (ψ : T₂ →+* T₁) (h : Spec.map (CommRingCat.ofHom ψ) ≫ g₂ = g₁) :
    Over.mk g₁ ⟶ Over.mk g₂ :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ)) h

@[simp]
lemma rhom_left {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    (ψ : T₂ →+* T₁) (h : Spec.map (CommRingCat.ofHom ψ) ≫ g₂ = g₁) :
    (rhom ψ h).left = Spec.map (CommRingCat.ofHom ψ) := rfl

lemma spec_comp₁₁ {g : Spec (CommRingCat.of T₃) ⟶ S} {ψ : T₂ →+* T₁} {α : T₃ →+* T₂}
    {β : T₃ →+* T₁} (e : ψ.comp α = β) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom α) ≫ g =
      Spec.map (CommRingCat.ofHom β) ≫ g := by
  rw [← e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

lemma spec_comp₁₂ {g : Spec (CommRingCat.of T₄) ⟶ S} {ψ : T₂ →+* T₁} {α : T₄ →+* T₂}
    {β : T₃ →+* T₁} {γ : T₄ →+* T₃} (e : ψ.comp α = β.comp γ) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom α) ≫ g =
      Spec.map (CommRingCat.ofHom β) ≫ Spec.map (CommRingCat.ofHom γ) ≫ g := by
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]

lemma spec_comp₂₁ {g : Spec (CommRingCat.of T₄) ⟶ S}
    {ψ : T₂ →+* T₁} {α : T₃ →+* T₂} {β : T₄ →+* T₃} {γ : T₄ →+* T₁}
    (e : ψ.comp (α.comp β) = γ) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom α) ≫
      Spec.map (CommRingCat.ofHom β) ≫ g = Spec.map (CommRingCat.ofHom γ) ≫ g := by
  rw [← e, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]

lemma rhom_comp {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    {g₃ : Spec (CommRingCat.of T₃) ⟶ S} (ψ₁ : T₂ →+* T₁) (ψ₂ : T₃ →+* T₂)
    (h₁ : Spec.map (CommRingCat.ofHom ψ₁) ≫ g₂ = g₁)
    (h₂ : Spec.map (CommRingCat.ofHom ψ₂) ≫ g₃ = g₂) :
    rhom ψ₁ h₁ ≫ rhom ψ₂ h₂ = rhom (ψ₁.comp ψ₂) (by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, h₂, h₁]) := by
  ext1
  simp only [Over.comp_left, rhom_left, CommRingCat.ofHom_comp, Spec.map_comp]

lemma rhom_congr {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    {ψ ψ' : T₂ →+* T₁} (e : ψ = ψ') (h : Spec.map (CommRingCat.ofHom ψ) ≫ g₂ = g₁)
    (h' : Spec.map (CommRingCat.ofHom ψ') ≫ g₂ = g₁) : rhom ψ h = rhom ψ' h' := by
  subst e
  rfl

lemma rhom_id {g : Spec (CommRingCat.of T₁) ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (RingHom.id T₁)) ≫ g = g) :
    rhom (RingHom.id T₁) h = 𝟙 (Over.mk g) := by
  ext1
  simp

variable {F : (Over S)ᵒᵖ ⥤ Type v}

lemma map_rhom_map_rhom {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    {g₃ : Spec (CommRingCat.of T₃) ⟶ S} (ψ₁ : T₂ →+* T₁) (ψ₂ : T₃ →+* T₂)
    (h₁ : Spec.map (CommRingCat.ofHom ψ₁) ≫ g₂ = g₁)
    (h₂ : Spec.map (CommRingCat.ofHom ψ₂) ≫ g₃ = g₂) (x : F.obj (op (Over.mk g₃))) :
    F.map (rhom ψ₁ h₁).op (F.map (rhom ψ₂ h₂).op x) = F.map (rhom (ψ₁.comp ψ₂) (by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, h₂, h₁])).op x := by
  rw [← rhom_comp, op_comp, Functor.map_comp_apply]

lemma map_rhom_eq {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    {ψ ψ' : T₂ →+* T₁} (h : Spec.map (CommRingCat.ofHom ψ) ≫ g₂ = g₁)
    (h' : Spec.map (CommRingCat.ofHom ψ') ≫ g₂ = g₁) (e : ψ = ψ') (x : F.obj (op (Over.mk g₂))) :
    F.map (rhom ψ h).op x = F.map (rhom ψ' h').op x := by
  rw [rhom_congr e h h']

lemma map_rhom_eq' {g₁ : Spec (CommRingCat.of T₁) ⟶ S} {g₂ : Spec (CommRingCat.of T₂) ⟶ S}
    {ψ ψ' : T₂ →+* T₁} (e : ψ = ψ') (h : Spec.map (CommRingCat.ofHom ψ) ≫ g₂ = g₁)
    (x : F.obj (op (Over.mk g₂))) :
    F.map (rhom ψ h).op x = F.map (rhom ψ' (by subst e; exact h)).op x := by
  subst e
  rfl

end RHom

section Forms

variable {F : (Over S)ᵒᵖ ⥤ Type v} {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S)

lemma algebraOverBase_eq (B : Type u) [CommRing B] [Algebra A B] :
    algebraOverBase f B = rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)
      (g₂ := f) (algebraMap A B) rfl := rfl

lemma algHomOver_eq {B C : Type u} [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C) : algHomOver f φ = rhom (φ : B →+* C) (spec_comp₁₁ φ.comp_algebraMap) := rfl

lemma factor_comp_algebraMap {B : Type u} [CommRing B] [Algebra A B] {J J' : Ideal B}
    (hJ : J ≤ J') :
    (Ideal.Quotient.factor hJ).comp (algebraMap A (B ⧸ J)) = algebraMap A (B ⧸ J') := rfl

lemma quotientMap_comp_mk {B : Type u} [CommRing B] [Algebra A B] (I : Ideal A) :
    (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map).comp
      (algebraMap A (A ⧸ I)) = algebraMap A (B ⧸ I.map (algebraMap A B)) := rfl

/-- `NoLargerLift` with its maps written as `rhom`. -/
lemma noLargerLift_iff {I : Ideal A} (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : F.obj (op (algebraOver f (A ⧸ I)))) :
    NoLargerLift B ξ' ↔ ∀ (J : Ideal B) (hJ : J < I.map (algebraMap A B))
      (η : F.obj (op (algebraOver f (B ⧸ J)))),
      F.map (rhom (Ideal.Quotient.factor hJ.le) (spec_comp₁₁ (factor_comp_algebraMap hJ.le))).op η ≠
        F.map (rhom (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
          Ideal.le_comap_map) (spec_comp₁₁ (quotientMap_comp_mk I))).op ξ' := Iff.rfl

end Forms

section BaseChange

variable {F : (Over S)ᵒᵖ ⥤ Type v} {R' : Type u} [CommRing R'] (f : Spec (CommRingCat.of R') ⟶ S)
variable (A : Type u) [CommRing A] [Algebra R' A] (𝔍 : Ideal R')

/-- The structure morphism `Spec A ⟶ Spec R' ⟶ S` of an `R'`-algebra `A`. -/
abbrev baseOver : Spec (CommRingCat.of A) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap R' A)) ≫ f

lemma quotientMap_comp_algebraMap :
    (Ideal.quotientMap (𝔍.map (algebraMap R' A)) (algebraMap R' A) Ideal.le_comap_map).comp
      (algebraMap R' (R' ⧸ 𝔍)) =
      (algebraMap A (A ⧸ 𝔍.map (algebraMap R' A))).comp (algebraMap R' A) := rfl

/-- The restriction of `ξ ∈ F(Spec (R'/𝔍))` to `Spec (A/𝔍A)`, an object over `S` through
`Spec A ⟶ Spec R'`. -/
def restrictBase (ξ : F.obj (op (algebraOver f (R' ⧸ 𝔍)))) :
    F.obj (op (algebraOver (baseOver f A) (A ⧸ 𝔍.map (algebraMap R' A)))) :=
  F.map (rhom (Ideal.quotientMap (𝔍.map (algebraMap R' A)) (algebraMap R' A) Ideal.le_comap_map)
    (spec_comp₁₂ (quotientMap_comp_algebraMap A 𝔍))).op ξ

variable {A} in
lemma map_map_eq (C : Type u) [CommRing C] [Algebra A C] [Algebra R' C] [IsScalarTower R' A C] :
    (𝔍.map (algebraMap R' A)).map (algebraMap A C) = 𝔍.map (algebraMap R' C) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- `NoLargerLift` does not depend on whether `C` is viewed over `Spec A` or over `Spec R'`. -/
theorem noLargerLift_restrictBase_iff (C : Type u) [CommRing C] [Algebra A C] [Algebra R' C]
    [IsScalarTower R' A C] (ξ : F.obj (op (algebraOver f (R' ⧸ 𝔍)))) :
    NoLargerLift (f := baseOver f A) C (restrictBase f A 𝔍 ξ) ↔ NoLargerLift (f := f) C ξ := by
  have e := map_map_eq (A := A) 𝔍 C
  rw [noLargerLift_iff, noLargerLift_iff]
  constructor
  · intro H J hJ η heq
    have hJ' : J < (𝔍.map (algebraMap R' A)).map (algebraMap A C) := e ▸ hJ
    have hc : (RingHom.id (C ⧸ J)).comp (algebraMap R' (C ⧸ J)) =
        (algebraMap A (C ⧸ J)).comp (algebraMap R' A) := by
      rw [RingHom.id_comp, IsScalarTower.algebraMap_eq R' A (C ⧸ J)]
    apply H J hJ' (F.map (rhom (RingHom.id (C ⧸ J)) (spec_comp₁₂ hc)).op η)
    have hc₂ : (Ideal.Quotient.factor e.ge).comp (algebraMap R' (C ⧸ 𝔍.map (algebraMap R' C))) =
        (algebraMap A (C ⧸ (𝔍.map (algebraMap R' A)).map (algebraMap A C))).comp
          (algebraMap R' A) := by
      ext x
      rw [RingHom.comp_apply, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply R' A (C ⧸ 𝔍.map (algebraMap R' C)),
        ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.factor_mk]
    have := congrArg (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap A
      (C ⧸ (𝔍.map (algebraMap R' A)).map (algebraMap A C)))) ≫ baseOver f A)
      (Ideal.Quotient.factor e.ge) (spec_comp₁₂ hc₂)).op) heq
    rw [map_rhom_map_rhom, map_rhom_map_rhom] at this
    unfold restrictBase
    rw [map_rhom_map_rhom, map_rhom_map_rhom]
    have r1 : (Ideal.Quotient.factor hJ'.le).comp (RingHom.id (C ⧸ J)) =
        (Ideal.Quotient.factor e.ge).comp (Ideal.Quotient.factor hJ.le) := by
      ext x
      rfl
    rw [map_rhom_eq' r1, this]
    refine map_rhom_eq _ _ ?_ ξ
    ext x
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk,
      IsScalarTower.algebraMap_apply R' A C]
  · intro H J hJ η heq
    have hJ' : J < 𝔍.map (algebraMap R' C) := e ▸ hJ
    have hc : (RingHom.id (C ⧸ J)).comp ((algebraMap A (C ⧸ J)).comp (algebraMap R' A)) =
        algebraMap R' (C ⧸ J) := by
      rw [RingHom.id_comp, IsScalarTower.algebraMap_eq R' A (C ⧸ J)]
    apply H J hJ' (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap R' (C ⧸ J))) ≫ f)
      (RingHom.id (C ⧸ J)) (spec_comp₂₁ hc)).op η)
    have hc₂ : (Ideal.Quotient.factor e.le).comp
        ((algebraMap A (C ⧸ (𝔍.map (algebraMap R' A)).map (algebraMap A C))).comp
          (algebraMap R' A)) = algebraMap R' (C ⧸ 𝔍.map (algebraMap R' C)) := by
      ext x
      rw [RingHom.comp_apply, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply R' A (C ⧸ 𝔍.map (algebraMap R' C)),
        ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.factor_mk]
    have := congrArg (F.map (rhom (g₁ := Spec.map (CommRingCat.ofHom (algebraMap R'
      (C ⧸ 𝔍.map (algebraMap R' C)))) ≫ f) (Ideal.Quotient.factor e.le) (spec_comp₂₁ hc₂)).op) heq
    unfold restrictBase at this
    rw [map_rhom_map_rhom, map_rhom_map_rhom, map_rhom_map_rhom] at this
    rw [map_rhom_map_rhom]
    have r1 : (Ideal.Quotient.factor hJ'.le).comp (RingHom.id (C ⧸ J)) =
        (Ideal.Quotient.factor e.le).comp (Ideal.Quotient.factor hJ.le) := by
      ext x
      rfl
    rw [map_rhom_eq' r1, this]
    refine map_rhom_eq _ _ ?_ ξ
    ext x
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk,
      IsScalarTower.algebraMap_apply R' A C]

end BaseChange

section Nakayama

variable {F : (Over S)ᵒᵖ ⥤ Type v} {R' : Type u} [CommRing R'] {f : Spec (CommRingCat.of R') ⟶ S}
variable {𝔍 : Ideal R'}

/-- Lifts move forward along a surjection `π : B → C` of `R'`-algebras whose kernel lies in
`𝔪_B · 𝔍B`, `B` local noetherian: by Nakayama's lemma, `π` maps an ideal `J < 𝔍B` to an ideal
strictly smaller than `𝔍C`. -/
theorem noLargerLift_of_surjective {B C : Type u} [CommRing B] [Algebra R' B] [CommRing C]
    [Algebra R' C] [IsLocalRing B] [IsNoetherianRing B] (π : B →ₐ[R'] C)
    (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : B →+* C) ≤ IsLocalRing.maximalIdeal B * 𝔍.map (algebraMap R' B))
    {ξ : F.obj (op (algebraOver f (R' ⧸ 𝔍)))} (H : NoLargerLift C ξ) : NoLargerLift B ξ := by
  rw [noLargerLift_iff] at H ⊢
  intro J hJ η heq
  have e : (𝔍.map (algebraMap R' B)).map (π : B →+* C) = 𝔍.map (algebraMap R' C) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  have hJ' : J.map (π : B →+* C) < 𝔍.map (algebraMap R' C) := by
    refine lt_of_le_of_ne (e ▸ Ideal.map_mono hJ.le) fun hEq ↦ ?_
    have hle : 𝔍.map (algebraMap R' B) ≤ J := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge fun x hx ↦ ?_
      have hx' : π x ∈ J.map (π : B →+* C) := by
        rw [hEq, ← e]
        exact Ideal.mem_map_of_mem _ hx
      obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective _ hπ).1 hx'
      have hk : x - j ∈ IsLocalRing.maximalIdeal B • 𝔍.map (algebraMap R' B) := by
        rw [Ideal.smul_eq_mul]
        apply hker
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.2 hjx.symm
      have : x = j + (x - j) := by ring
      rw [this]
      exact Submodule.add_mem_sup hj hk
    exact lt_irrefl _ (lt_of_lt_of_le hJ hle)
  have hc : (Ideal.quotientMap (J.map (π : B →+* C)) (π : B →+* C) Ideal.le_comap_map).comp
      (algebraMap R' (B ⧸ J)) = algebraMap R' (C ⧸ J.map (π : B →+* C)) := by
    ext x
    simp [Ideal.Quotient.mk_algebraMap]
  apply H _ hJ' (F.map (rhom _ (spec_comp₁₁ hc)).op η)
  have hle : 𝔍.map (algebraMap R' B) ≤ (𝔍.map (algebraMap R' C)).comap (π : B →+* C) := by
    rw [← e]
    exact Ideal.le_comap_map
  have hc' : (Ideal.quotientMap _ (π : B →+* C) hle).comp (algebraMap R' (B ⧸ 𝔍.map (algebraMap R' B))) =
      algebraMap R' (C ⧸ 𝔍.map (algebraMap R' C)) := by
    ext x
    simp [Ideal.Quotient.mk_algebraMap]
  have := congrArg (F.map (rhom _ (spec_comp₁₁ hc')).op) heq
  rw [map_rhom_map_rhom, map_rhom_map_rhom] at this
  rw [map_rhom_map_rhom]
  refine (map_rhom_eq _ _ ?_ η).trans (this.trans (map_rhom_eq _ _ ?_ ξ))
  · ext x
    rfl
  · ext x
    simp [Ideal.Quotient.mk_algebraMap]

end Nakayama

section Infinitesimal

variable {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Infinitesimal étaleness at `y`, for an arbitrary surjection `π : L → D` with nilpotent
kernel in place of a quotient map `L → L/J`. -/
theorem exists_lift_of_surjective {U : Over S} {ξ : F.obj (op U)} {y : U.left}
    (hy : InfinitesimallyEtaleAt F ξ y) {L D : Type u} [CommRing L] [IsLocalRing L]
    [IsArtinianRing L] [CommRing D] {fL : Spec (CommRingCat.of L) ⟶ S}
    {g : Spec (CommRingCat.of D) ⟶ S} (π : L →+* D) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker π)) (hg : Spec.map (CommRingCat.ofHom π) ≫ fL = g)
    (u₀ : Over.mk g ⟶ U) (hu₀ : ∀ x, u₀.left x = y) (v : F.obj (op (Over.mk fL)))
    (hv : F.map u₀.op ξ = F.map (rhom π hg).op v) :
    ∃ u : Over.mk fL ⟶ U, rhom π hg ≫ u = u₀ ∧ F.map u.op ξ = v := by
  set e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : L ⧸ RingHom.ker π →+* D).comp (Ideal.Quotient.mk _) = π := by
    ext x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hπ x
  have he' : (e.symm : D →+* L ⧸ RingHom.ker π).comp π = algebraMap L (L ⧸ RingHom.ker π) := by
    ext x
    change e.symm (π x) = Ideal.Quotient.mk _ x
    rw [RingEquiv.symm_apply_eq]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hπ x).symm
  have hc : Spec.map (CommRingCat.ofHom (e.symm : D →+* L ⧸ RingHom.ker π)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap L (L ⧸ RingHom.ker π))) ≫ fL := by
    rw [← hg]
    exact spec_comp₁₁ he'
  have hc' : Spec.map (CommRingCat.ofHom (e : L ⧸ RingHom.ker π →+* D)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L (L ⧸ RingHom.ker π))) ≫ fL = g := by
    rw [← hg]
    exact spec_comp₁₁ he
  let u₀' : algebraOver fL (L ⧸ RingHom.ker π) ⟶ U := rhom _ hc ≫ u₀
  obtain ⟨u, ⟨hu₁, hu₂⟩, -⟩ := hy L fL (RingHom.ker π) hnil u₀' (fun x ↦ hu₀ _) v (by
    simp only [u₀', op_comp, Functor.map_comp_apply, hv]
    rw [algebraOverBase_eq, map_rhom_map_rhom]
    exact map_rhom_eq _ _ he' v)
  refine ⟨u, ?_, hu₂⟩
  have h1 : rhom π hg = rhom _ hc' ≫ algebraOverBase fL (L ⧸ RingHom.ker π) := by
    rw [algebraOverBase_eq, rhom_comp]
    exact rhom_congr he.symm _ _
  rw [h1, Category.assoc, hu₁]
  simp only [u₀', ← Category.assoc, rhom_comp]
  rw [rhom_congr (show (e : L ⧸ RingHom.ker π →+* D).comp (e.symm : D →+* L ⧸ RingHom.ker π) =
    RingHom.id D by ext x; simp) _ (by simp), rhom_id, Category.id_comp]

end Infinitesimal

section Artinian

variable (R : CommRingCat.{u}) {R' : Type u} [CommRing R'] [Algebra R R']
variable {F : (Over (Spec R))ᵒᵖ ⥤ Type v} {𝔍 : Ideal R'}

/-- For a local artinian `R'`-algebra `C` whose closed point lies over the point `y` of
`Spec (R'/𝔍)` at which `ξ` is infinitesimally étale, the restriction of `ξ` to
`Spec (C/𝔍C)` lifts to no `Spec (C/J)` with `J < 𝔍C`, when `R'` is formally unramified over
`R`: a lift would give an `R`-algebra map `R'/𝔍 → C/J`, which by formal unramifiedness agrees
with `R' → C/J`, so `𝔍` maps to zero in `C/J`. -/
theorem noLargerLift_of_isArtinianRing [Algebra.FormallyUnramified R R']
    {ξ : F.obj (op (algebraOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (R' ⧸ 𝔍)))}
    {y : PrimeSpectrum (R' ⧸ 𝔍)} (hy : InfinitesimallyEtaleAt F ξ y)
    (C : Type u) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Algebra R C] [Algebra R' C]
    [IsScalarTower R R' C]
    (hC : (IsLocalRing.maximalIdeal C).comap (algebraMap R' C) =
      y.asIdeal.comap (Ideal.Quotient.mk 𝔍)) :
    NoLargerLift (f := Spec.map (CommRingCat.ofHom (algebraMap R R'))) C ξ := by
  rw [noLargerLift_iff]
  intro J hJ η heq
  have h𝔍 : 𝔍.map (algebraMap R' C) ≤ IsLocalRing.maximalIdeal C := by
    rw [Ideal.map_le_iff_le_comap, hC]
    intro x hx
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have hJtop : J ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top (hJ.le.trans h𝔍)
  have : Nontrivial (C ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (C ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : Nontrivial (C ⧸ 𝔍.map (algebraMap R' C)) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal C).ne_top h𝔍)
  set π := Ideal.Quotient.factor hJ.le
  have hnil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C ⧸ J)
    refine ⟨n, eq_bot_iff.2 ((Ideal.pow_right_mono ?_ n).trans hn.le)⟩
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  have hu₀ : ∀ x, (rhom (g₁ := Spec.map (CommRingCat.ofHom
      (algebraMap R' (C ⧸ 𝔍.map (algebraMap R' C)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Ideal.quotientMap (𝔍.map (algebraMap R' C)) (algebraMap R' C) Ideal.le_comap_map)
      (spec_comp₁₁ (quotientMap_comp_mk 𝔍))).left x = y := by
    intro x
    let x' : PrimeSpectrum (C ⧸ 𝔍.map (algebraMap R' C)) := x
    have hx : x'.asIdeal.comap (Ideal.Quotient.mk (𝔍.map (algebraMap R' C))) =
        IsLocalRing.maximalIdeal C := Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := 𝔍))
    change Ideal.comap (Ideal.Quotient.mk 𝔍) (Ideal.comap
      (Ideal.quotientMap (𝔍.map (algebraMap R' C)) (algebraMap R' C) Ideal.le_comap_map)
        x'.asIdeal) = _
    rw [Ideal.comap_comap, ← hC, ← hx, Ideal.comap_comap]
    rfl
  obtain ⟨u, hu, -⟩ := exists_lift_of_surjective hy
    (fL := Spec.map (CommRingCat.ofHom (algebraMap R' (C ⧸ J))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')))
    π (Ideal.Quotient.factor_surjective hJ.le) hnil
    (spec_comp₁₁ (factor_comp_algebraMap hJ.le)) _ hu₀ η heq.symm
  set σ := Spec.preimage u.left
  have hσ : Spec.map σ = u.left := Spec.map_preimage _
  have h1 : σ.hom.comp ((Ideal.Quotient.mk 𝔍).comp (algebraMap R R')) =
      (algebraMap R' (C ⧸ J)).comp (algebraMap R R') := by
    have hw := Over.w u
    simp only [Over.mk_hom, ← hσ] at hw
    change Spec.map σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔍)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')) =
        Spec.map (CommRingCat.ofHom (algebraMap R' (C ⧸ J))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) at hw
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp] at hw
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
    exact this
  have h2 : π.comp σ.hom = Ideal.quotientMap (𝔍.map (algebraMap R' C)) (algebraMap R' C)
      Ideal.le_comap_map := by
    have hl : Spec.map (CommRingCat.ofHom π) ≫ Spec.map σ = Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (𝔍.map (algebraMap R' C)) (algebraMap R' C) Ideal.le_comap_map)) := by
      rw [hσ]
      exact congrArg CommaMorphism.left hu
    rw [← Spec.map_comp] at hl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hl)
  let g₁ : R' →ₐ[R] C ⧸ J :=
    { σ.hom.comp (Ideal.Quotient.mk 𝔍) with
      commutes' := fun r ↦ by
        have := RingHom.congr_fun h1 r
        simp only [RingHom.coe_comp, Function.comp_apply] at this
        simpa [← IsScalarTower.algebraMap_apply] using this }
  have hg : g₁ = IsScalarTower.toAlgHom R R' (C ⧸ J) := by
    refine Algebra.FormallyUnramified.ext' π hnil _ _ fun x ↦ ?_
    have := RingHom.congr_fun h2 (Ideal.Quotient.mk 𝔍 x)
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    change π (σ.hom (Ideal.Quotient.mk 𝔍 x)) = π (algebraMap R' (C ⧸ J) x)
    rw [this]
    rfl
  have hle : 𝔍.map (algebraMap R' C) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have := AlgHom.congr_fun hg x
    change σ.hom (Ideal.Quotient.mk 𝔍 x) = algebraMap R' (C ⧸ J) x at this
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero] at this
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    exact this.symm
  exact lt_irrefl _ (lt_of_lt_of_le hJ hle)

end Artinian

end GenericLift

end Langlands.AlgebraicGeometry.UnramifiedFunctor
