import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal
import Mathlib.RingTheory.Etale.Basic

/-! # The étale locus of a closed subscheme of an étale chart: basic dictionary

Let `R` be a ring, `R'` an étale `R`-algebra, `𝔍` an ideal of `R'` and
`U = Spec (R'/𝔍)` over `Spec R`. For `ξ ∈ F(U)` and a point `w` of `U`, infinitesimal
étaleness of `ξ` at `w` is rephrased as a condition on ring maps `β : R' → A` into local
artinian rings (`KillAt`): every such map underlying a lifting problem at `w` kills `𝔍`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

section RingLift

variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A] [Algebra R R']

/-- Lifting along a nilpotent thickening, for a formally smooth algebra, in ring-hom form. -/
lemma exists_lift [Algebra.FormallySmooth R R'] (φ : R →+* A) (J : Ideal A) (hJ : IsNilpotent J)
    (γ₀ : R' →+* A ⧸ J) (h : γ₀.comp (algebraMap R R') = (Ideal.Quotient.mk J).comp φ) :
    ∃ β : R' →+* A, β.comp (algebraMap R R') = φ ∧ (Ideal.Quotient.mk J).comp β = γ₀ := by
  let _ := φ.toAlgebra
  let g : R' →ₐ[R] A ⧸ J :=
    { γ₀ with
      commutes' := fun r => RingHom.congr_fun h r }
  refine ⟨(Algebra.FormallySmooth.lift J hJ g : R' →+* A), ?_, ?_⟩
  · ext r
    exact (Algebra.FormallySmooth.lift J hJ g).commutes r
  · ext x
    exact Algebra.FormallySmooth.mk_lift J hJ g x

/-- Uniqueness of lifts along a nilpotent thickening, for a formally unramified algebra. -/
lemma lift_unique [Algebra.FormallyUnramified R R'] (J : Ideal A) (hJ : IsNilpotent J)
    (β₁ β₂ : R' →+* A) (h : β₁.comp (algebraMap R R') = β₂.comp (algebraMap R R'))
    (h' : (Ideal.Quotient.mk J).comp β₁ = (Ideal.Quotient.mk J).comp β₂) : β₁ = β₂ := by
  let _ := (β₂.comp (algebraMap R R')).toAlgebra
  let g₁ : R' →ₐ[R] A := { β₁ with commutes' := fun r => RingHom.congr_fun h r }
  let g₂ : R' →ₐ[R] A := { β₂ with commutes' := fun r => rfl }
  have := Algebra.FormallyUnramified.lift_unique J hJ g₁ g₂
    (AlgHom.ext fun x => RingHom.congr_fun h' x)
  ext x
  exact AlgHom.congr_fun this x

end RingLift

section SpecHelpers

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

lemma specMap_ofHom_comp (ψ : A →+* B) (φ : B →+* C) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom (φ.comp ψ)) := by
  rw [← Spec.map_comp]
  rfl

lemma specMap_ofHom_inj {φ ψ : A →+* B} :
    Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) ↔ φ = ψ := by
  rw [Spec.map_inj]
  exact ⟨fun h => congrArg CommRingCat.Hom.hom h, fun h => h ▸ rfl⟩

lemma exists_specMap_ofHom (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)) :
    ∃ φ : B →+* A, Spec.map (CommRingCat.ofHom φ) = f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  exact ⟨φ.hom, rfl⟩

end SpecHelpers

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'}

variable (R R') in
/-- The structure morphism `Spec R' ⟶ Spec R`. -/
abbrev baseMap : Spec (CommRingCat.of R') ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

variable (R R' 𝔍) in
/-- The closed subscheme `Spec (R'/𝔍)` of `Spec R'`, as an object over `Spec R`. -/
abbrev chart : Over (Spec R) :=
  algebraOver (baseMap R R') (R' ⧸ 𝔍)

/-- A ring map `C → A` together with a structure ring map of `C`, as the structure equation of
`Spec A` over `Spec R`. -/
lemma chart_hom :
    (chart R R' 𝔍).hom = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk 𝔍).comp (algebraMap R R'))) := by
  simp only [chart, algebraOver, baseMap, Over.mk_hom]
  rw [specMap_ofHom_comp]

/-- The morphism `Spec C ⟶ Spec (R'/𝔍)` over `Spec R` given by a ring map `γ : R'/𝔍 → C`. -/
def homU {C : Type u} [CommRing C] (γ : R' ⧸ 𝔍 →+* C) (f : Spec (CommRingCat.of C) ⟶ Spec R)
    (hf : Spec.map (CommRingCat.ofHom ((γ.comp (Ideal.Quotient.mk 𝔍)).comp (algebraMap R R'))) = f) :
    Over.mk f ⟶ chart R R' 𝔍 :=
  Over.homMk (Spec.map (CommRingCat.ofHom γ)) (by
    rw [chart_hom, ← hf, specMap_ofHom_comp]
    rfl)

@[simp]
lemma homU_left {C : Type u} [CommRing C] (γ : R' ⧸ 𝔍 →+* C)
    (f : Spec (CommRingCat.of C) ⟶ Spec R) (hf) :
    (homU (𝔍 := 𝔍) γ f hf).left = Spec.map (CommRingCat.ofHom γ) := rfl

/-- The ring-level form of the lifting condition at `w`: every ring map `β : R' → A` into a
local artinian ring which underlies a lifting problem for `ξ` at `w` (a nilpotent ideal `J`, a
point `u₀ : Spec (A/J) ⟶ U` at `w` reducing `β`, and `v ∈ F(Spec A)` restricting to `ξ ∘ u₀`)
kills `𝔍`. -/
def KillAt (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    (A : Type u) [CommRing A] (β : R' →+* A) : Prop :=
  ∀ (f : Spec (CommRingCat.of A) ⟶ Spec R),
    Spec.map (CommRingCat.ofHom (β.comp (algebraMap R R'))) = f →
    ∀ (J : Ideal A), IsNilpotent J → ∀ u₀ : algebraOver f (A ⧸ J) ⟶ chart R R' 𝔍,
      u₀.left ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔍)) =
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp β)) →
      (∀ x, u₀.left x = w) →
      ∀ v : F.obj (op (Over.mk f)),
        F.map u₀.op ξ = F.map (algebraOverBase f (A ⧸ J)).op v →
        ∀ j ∈ 𝔍, β j = 0

/-- The ring map `R'/𝔍 → C` of an `Spec R`-morphism `Spec C ⟶ Spec (R'/𝔍)`, where `Spec C`
lies over `Spec R` through `φ`, is compatible with `φ`. -/
lemma comp_eq_of_over {C : Type u} [CommRing C] (φ : R →+* C)
    (γ : R' ⧸ 𝔍 →+* C)
    (h : Spec.map (CommRingCat.ofHom γ) ≫ (chart R R' 𝔍).hom =
      Spec.map (CommRingCat.ofHom φ)) :
    (γ.comp (Ideal.Quotient.mk 𝔍)).comp (algebraMap R R') = φ := by
  rw [chart_hom, specMap_ofHom_comp, specMap_ofHom_inj] at h
  rw [← h]
  rfl

/-- Infinitesimal étaleness at `w` in terms of ring maps into local artinian rings. -/
theorem infinitesimallyEtaleAt_iff [Algebra.Etale R R'] (hF5 : NilpotentInjective F)
    (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) :
    InfinitesimallyEtaleAt F ξ w ↔
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] (β : R' →+* A),
        KillAt ξ w A β := by
  constructor
  · intro H A _ _ _ β f hf J hJ u₀ hc hw v hv
    obtain ⟨u, ⟨hu₁, hu₂⟩, -⟩ := H A f J hJ u₀ hw v hv
    obtain ⟨γ, hγ⟩ := exists_specMap_ofHom u.left
    have hover : Spec.map (CommRingCat.ofHom γ) ≫ (chart R R' 𝔍).hom =
        Spec.map (CommRingCat.ofHom (β.comp (algebraMap R R'))) := by
      rw [hγ, hf]
      exact Over.w u
    have e1 := comp_eq_of_over _ γ hover
    have e2 : (Ideal.Quotient.mk J).comp (γ.comp (Ideal.Quotient.mk 𝔍)) =
        (Ideal.Quotient.mk J).comp β := by
      have h1 := congrArg (fun k => k.left) hu₁
      simp only [Over.comp_left, algebraOverBase, Over.homMk_left] at h1
      rw [← specMap_ofHom_inj, ← hc, ← h1, ← hγ, Category.assoc, specMap_ofHom_comp,
        specMap_ofHom_comp, Ideal.Quotient.algebraMap_eq]
    have e3 := lift_unique J hJ _ _ e1 e2
    intro j hj
    rw [← e3]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hj]
  · intro H A _ _ _ f J hJ u₀ hw v hv
    obtain ⟨φ, rfl⟩ := exists_specMap_ofHom f
    obtain ⟨γ₀, hγ₀⟩ := exists_specMap_ofHom u₀.left
    have hover : Spec.map (CommRingCat.ofHom γ₀) ≫ (chart R R' 𝔍).hom =
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp φ)) := by
      rw [hγ₀, Over.w u₀]
      simp only [algebraOver, Over.mk_hom]
      rw [specMap_ofHom_comp, Ideal.Quotient.algebraMap_eq]
    have e1 := comp_eq_of_over _ γ₀ hover
    obtain ⟨β, hβ₁, hβ₂⟩ := exists_lift φ J hJ (γ₀.comp (Ideal.Quotient.mk 𝔍)) e1
    have hkill := H A β _ (by rw [hβ₁]) J hJ u₀
      (by rw [← hγ₀, specMap_ofHom_comp, hβ₂]) hw v hv
    let γ : R' ⧸ 𝔍 →+* A := Ideal.Quotient.lift 𝔍 β hkill
    have hγ : γ.comp (Ideal.Quotient.mk 𝔍) = β := by
      ext x
      rfl
    have hγφ : (γ.comp (Ideal.Quotient.mk 𝔍)).comp (algebraMap R R') = φ := by
      rw [hγ, hβ₁]
    let u := homU γ _ (by rw [hγφ])
    have hγ₀' : (Ideal.Quotient.mk J).comp γ = γ₀ := by
      apply Ideal.Quotient.ringHom_ext
      rw [RingHom.comp_assoc, hγ, hβ₂]
    have hu₁ : algebraOverBase (Spec.map (CommRingCat.ofHom φ)) (A ⧸ J) ≫ u = u₀ := by
      ext1
      simp only [Over.comp_left, algebraOverBase, Over.homMk_left, u, homU_left]
      rw [← hγ₀, specMap_ofHom_comp, Ideal.Quotient.algebraMap_eq, hγ₀']
    have hu₂ : F.map u.op ξ = v := by
      apply hF5 A J hJ
      rw [← Functor.map_comp_apply, ← op_comp, hu₁, hv]
    refine ⟨u, ⟨hu₁, hu₂⟩, ?_⟩
    rintro u' ⟨hu'₁, -⟩
    obtain ⟨γ', hγ'⟩ := exists_specMap_ofHom u'.left
    have hover' : Spec.map (CommRingCat.ofHom γ') ≫ (chart R R' 𝔍).hom =
        Spec.map (CommRingCat.ofHom φ) := by
      rw [hγ']
      exact Over.w u'
    have e1' := comp_eq_of_over _ γ' hover'
    have e2' : (Ideal.Quotient.mk J).comp (γ'.comp (Ideal.Quotient.mk 𝔍)) =
        (Ideal.Quotient.mk J).comp β := by
      have h1 := congrArg (fun k => k.left) hu'₁
      simp only [Over.comp_left, algebraOverBase, Over.homMk_left] at h1
      rw [hβ₂, ← RingHom.comp_assoc]
      congr 1
      rw [← specMap_ofHom_inj, hγ₀, ← h1, ← hγ', specMap_ofHom_comp,
        Ideal.Quotient.algebraMap_eq]
    have e3 := lift_unique J hJ _ _ (e1'.trans hβ₁.symm) e2'
    have e4 : γ' = γ := by
      apply Ideal.Quotient.ringHom_ext
      rw [e3, hγ]
    ext1
    rw [← hγ', e4]
    rfl

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
