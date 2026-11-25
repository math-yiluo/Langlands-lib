/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSections
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Sheaves of homomorphisms out of a module into an injective sheaf are acyclic

Let `Λ` be a commutative ring, `I` an injective sheaf of `Λ`-modules on a site and `M` a
`Λ`-module. The sheaf `Hom_Λ(M, I) : U ↦ Hom_Λ(M, I(U))`
(`CategoryTheory.Sheaf.homSheaf`) is in general not injective, but it is acyclic for every
left exact functor `Φ` which sends the morphisms that are surjective on sections to
epimorphisms (`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`); this applies to the direct
images of sheaves on sites.

The sections `I(U)` are injective `Λ`-modules
(`CategoryTheory.Sheaf.baer_obj_of_injective`), so a presentation
`0 ⟶ K ⟶ Λ^{(M)} ⟶ M ⟶ 0` gives a short exact sequence of sheaves
`0 ⟶ Hom(M, I) ⟶ Hom(Λ^{(M)}, I) ⟶ Hom(K, I) ⟶ 0` which is exact on sections. Its middle term
is injective, `Hom(Λ^{(M)}, -)` being right adjoint to the functor `Λ^{(M)} ⊗ -`, which
preserves monomorphisms since `Λ^{(M)}` is flat. The vanishing of `R^q Φ (Hom(M, I))` follows by
induction on `q`, for all `M` at once.
-/

@[expose] public section

universe t v u

namespace CategoryTheory

open Limits Opposite MonoidalCategory

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type t} [CommRing Λ]

variable (Λ) in
/-- The functor `Hom_Λ(M, -)` on `Λ`-modules. -/
abbrev homFunctor (M : ModuleCat.{t} Λ) : ModuleCat.{t} Λ ⥤ ModuleCat.{t} Λ :=
  (linearCoyoneda Λ (ModuleCat.{t} Λ)).obj (op M)

/-- `Hom_Λ(M, -)` is right adjoint to `M ⊗ -`. -/
instance (M : ModuleCat.{t} Λ) : (homFunctor Λ M).IsRightAdjoint :=
  (ihom.adjunction M).isRightAdjoint

variable (J) in
/-- The sheaf `U ↦ Hom_Λ(M, F(U))` of homomorphisms out of a `Λ`-module `M` into a sheaf `F` of
`Λ`-modules. -/
noncomputable abbrev homSheaf (M : ModuleCat.{t} Λ) :
    Sheaf J (ModuleCat.{t} Λ) ⥤ Sheaf J (ModuleCat.{t} Λ) :=
  sheafCompose J (homFunctor Λ M)

variable (J) in
/-- The morphism `Hom_Λ(N, F) ⟶ Hom_Λ(M, F)` of sheaves induced by a morphism `M ⟶ N`. -/
noncomputable abbrev homSheafMap {M N : ModuleCat.{t} Λ} (π : M ⟶ N) :
    homSheaf J N ⟶ homSheaf J M :=
  sheafCompose_map J ((linearCoyoneda Λ (ModuleCat.{t} Λ)).map π.op)

variable [HasSheafify J (ModuleCat.{t} Λ)]

/-- **A short complex of sheaves of modules which is short exact on sections is short exact.** -/
lemma shortExact_of_shortExact_sections (S : ShortComplex (Sheaf J (ModuleCat.{t} Λ)))
    (h : ∀ U : Cᵒᵖ, (S.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj U)).ShortExact) :
    S.ShortExact := by
  let T := S.map (sheafToPresheaf J (ModuleCat.{t} Λ))
  have hT : T.ShortExact := by
    have : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      exact fun U ↦ (h U).mono_f
    have : Epi T.g := by
      rw [NatTrans.epi_iff_epi_app]
      exact fun U ↦ (h U).epi_g
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.exact_iff_evaluation]
    exact fun U ↦ (h U).exact
  have hT' := hT.map_of_exact (presheafToSheaf J (ModuleCat.{t} Λ))
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.mapNatIso S (sheafificationNatIso J _)).symm hT'

/-- The sheaf `Hom_Λ(M, I)` is injective if `I` is injective and `M` is a flat `Λ`-module:
`Hom_Λ(M, -)` is right adjoint to the sheafification of `M ⊗ -`, which preserves
monomorphisms. -/
lemma injective_homSheaf_obj (M : ModuleCat.{t} Λ) [Module.Flat Λ M]
    (I : Sheaf J (ModuleCat.{t} Λ)) [Injective I] :
    Injective ((homSheaf J M).obj I) := by
  have : (composeAndSheafify J (tensorLeft M)).PreservesMonomorphisms := by
    have : ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{t} Λ) (ModuleCat.{t} Λ)).obj
        (tensorLeft M)).PreservesMonomorphisms := by
      refine ⟨fun {P Q} α hα ↦ ?_⟩
      rw [NatTrans.mono_iff_mono_app] at hα ⊢
      intro U
      have := hα U
      rw [ModuleCat.mono_iff_injective] at this ⊢
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := M) (α.app U).hom this
    dsimp only [composeAndSheafify]
    infer_instance
  exact Injective.injective_of_adjoint (Sheaf.adjunction J (ihom.adjunction M)) I

/-- The short complex `Hom(M, E) ⟶ Hom(F, E) ⟶ Hom(K, E)` of `Λ`-modules attached to a short
complex `K ⟶ F ⟶ M` and a `Λ`-module `E`. -/
noncomputable abbrev homShortComplex (S : ShortComplex (ModuleCat.{t} Λ)) (E : ModuleCat.{t} Λ) :
    ShortComplex (ModuleCat.{t} Λ) :=
  ShortComplex.mk (((linearCoyoneda Λ (ModuleCat.{t} Λ)).map S.g.op).app E)
    (((linearCoyoneda Λ (ModuleCat.{t} Λ)).map S.f.op).app E) (by
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, S.zero, op_zero,
        Functor.map_zero, NatTrans.app_zero])

/-- For a short exact sequence `0 ⟶ K ⟶ F ⟶ M ⟶ 0` of `Λ`-modules and a `Λ`-module `E`
satisfying Baer's criterion, the sequence `0 ⟶ Hom(M, E) ⟶ Hom(F, E) ⟶ Hom(K, E) ⟶ 0` is
short exact. -/
lemma shortExact_homShortComplex {S : ShortComplex (ModuleCat.{t} Λ)} (hS : S.ShortExact)
    (E : ModuleCat.{t} Λ) (hE : Module.Baer Λ E) : (homShortComplex S E).ShortExact := by
  have hf := hS.moduleCat_injective_f
  have := hS.epi_g
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    constructor
    · intro h
      obtain ⟨x, hx⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel y h
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, Limits.zero_comp]
  · intro x y hxy
    exact (cancel_epi S.g).1 hxy
  · intro z
    obtain ⟨h, hh⟩ := hE.extension_property S.f.hom hf z.hom
    exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

variable (J) in
/-- The short complex of sheaves `Hom(M, I) ⟶ Hom(F, I) ⟶ Hom(K, I)` attached to a short
complex `K ⟶ F ⟶ M` of `Λ`-modules and a sheaf `I` of `Λ`-modules. -/
noncomputable abbrev homSheafShortComplex (S : ShortComplex (ModuleCat.{t} Λ))
    (I : Sheaf J (ModuleCat.{t} Λ)) : ShortComplex (Sheaf J (ModuleCat.{t} Λ)) :=
  ShortComplex.mk ((homSheafMap J S.g).app I) ((homSheafMap J S.f).app I) (by
    apply (fullyFaithfulSheafToPresheaf J _).map_injective
    ext U : 2
    exact (homShortComplex S (I.obj.obj U)).zero)

/-- For a short exact sequence `0 ⟶ K ⟶ F ⟶ M ⟶ 0` of `Λ`-modules and a sheaf `I` whose
sections satisfy Baer's criterion, `0 ⟶ Hom(M, I) ⟶ Hom(F, I) ⟶ Hom(K, I) ⟶ 0` is short exact,
and even short exact on sections. -/
lemma shortExact_homSheafShortComplex {S : ShortComplex (ModuleCat.{t} Λ)} (hS : S.ShortExact)
    (I : Sheaf J (ModuleCat.{t} Λ)) (hI : ∀ U, Module.Baer Λ (I.obj.obj U)) :
    (homSheafShortComplex J S I).ShortExact :=
  shortExact_of_shortExact_sections _ fun U ↦ shortExact_homShortComplex hS _ (hI U)

/-- **Sheaves of homomorphisms into an injective sheaf are acyclic.** Let `Φ` be a left exact
functor on sheaves of `Λ`-modules which sends morphisms that are surjective on sections to
epimorphisms. For an injective sheaf `I` whose sections satisfy Baer's criterion (which is
automatic, `CategoryTheory.Sheaf.baer_obj_of_injective`) and any `Λ`-module `M`, the sheaf
`Hom_Λ(M, I)` is `Φ`-acyclic. -/
theorem rightAcyclic_homSheaf_obj [HasInjectiveResolutions (Sheaf J (ModuleCat.{t} Λ))]
    {D : Type*} [Category* D] [Abelian D] (Φ : Sheaf J (ModuleCat.{t} Λ) ⥤ D) [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hΦ : ∀ {A B : Sheaf J (ModuleCat.{t} Λ)} (p : A ⟶ B),
      (∀ U, Function.Surjective (p.hom.app U)) → Epi (Φ.map p))
    (I : Sheaf J (ModuleCat.{t} Λ)) [Injective I] (hI : ∀ U, Module.Baer Λ (I.obj.obj U))
    (M : ModuleCat.{t} Λ) : Φ.rightAcyclic ((homSheaf J M).obj I) := by
  intro q
  induction q generalizing M with
  | zero =>
    let π : (M →₀ Λ) →ₗ[Λ] M := Finsupp.linearCombination Λ id
    have hπ : Function.Surjective π := fun x ↦ ⟨Finsupp.single x 1, by simp [π]⟩
    have hS := LinearMap.shortExact_shortComplexKer hπ
    let T := homSheafShortComplex J π.shortComplexKer I
    have hT : T.ShortExact := shortExact_homSheafShortComplex hS I hI
    have : Injective T.X₂ := injective_homSheaf_obj (ModuleCat.of Λ (M →₀ Λ)) I
    obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hT.exists_rightDerived_δ_exact Φ 0
    have : Epi ((Φ.rightDerived 0).map T.g) := by
      rw [← NatIso.naturality_2 Φ.rightDerivedZeroIsoSelf T.g]
      have := hΦ T.g fun U ↦ (shortExact_homShortComplex hS _ (hI U)).moduleCat_surjective_g
      infer_instance
    exact h₂.isZero_X₂_iff.2 ⟨h₁.epi_f_iff.1 this,
      (Φ.isZero_rightDerived_obj_injective_succ 0 T.X₂).eq_of_tgt _ _⟩
  | succ q ih =>
    let π : (M →₀ Λ) →ₗ[Λ] M := Finsupp.linearCombination Λ id
    have hπ : Function.Surjective π := fun x ↦ ⟨Finsupp.single x 1, by simp [π]⟩
    have hS := LinearMap.shortExact_shortComplexKer hπ
    let T := homSheafShortComplex J π.shortComplexKer I
    have hT : T.ShortExact := shortExact_homSheafShortComplex hS I hI
    have : Injective T.X₂ := injective_homSheaf_obj (ModuleCat.of Λ (M →₀ Λ)) I
    obtain ⟨δ, w₁, w₂, -, h₂⟩ := hT.exists_rightDerived_δ_exact Φ (q + 1)
    exact h₂.isZero_X₂_iff.2 ⟨(ih _).eq_of_src _ _,
      (Φ.isZero_rightDerived_obj_injective_succ (q + 1) T.X₂).eq_of_tgt _ _⟩

end Sheaf

end CategoryTheory
