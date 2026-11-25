/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.FiveLemma
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionData
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtRestrictionMap
import WeilConjectures.AlgebraicGeometry.Cohomology.OpenImmersionInverseImageInjectives
import WeilConjectures.AlgebraicGeometry.Cohomology.OpenFreeSheafRestrictionHom
import WeilConjectures.AlgebraicGeometry.Cohomology.InverseImageOpenFreeSheaf
/-! # Bijectivity of Ext restriction from a represented open

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
section DimensionShift
universe w w' v v' u₁ u₂
variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]

private theorem mapExt_bijective_of_restrictionHom (J : C ⥤ D) [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J] [EnoughInjectives C]
    [J.PreservesInjectiveObjects] (A : C)
    (hA : ∀ F : C, Function.Bijective (fun a : A ⟶ F => J.map a))
    (F : C) (n : ℕ) : Function.Bijective (J.mapExtAddHom A F n) := by
  induction n generalizing F with
  | zero =>
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
      obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
      change (Ext.mk₀ x).mapExactFunctor J = (Ext.mk₀ y).mapExactFunctor J at hxy
      simp only [Ext.mapExactFunctor_mk₀] at hxy
      exact congrArg Ext.mk₀ ((hA F).1 ((Ext.mk₀_bijective _ _).1 hxy))
    · obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
      obtain ⟨a, rfl⟩ := (hA F).2 z
      exact ⟨Ext.mk₀ a, Ext.mapExactFunctor_mk₀ _ _⟩
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective (S.map J).X₂ := J.injective_obj I.J
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ S.g).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
      ((Ext.mk₀ (J.map S.g)).postcomp (J.obj A) (add_zero n))
      ((hS.map_of_exact J).extClass.postcomp (J.obj A) rfl)
      (J.mapExtAddHom A S.X₂ n) (J.mapExtAddHom A S.X₃ n)
      (J.mapExtAddHom A S.X₁ (n + 1))
      (by
        ext x
        change (x.mapExactFunctor J).comp (Ext.mk₀ (J.map S.g)) (add_zero n) =
          (x.comp (Ext.mk₀ S.g) (add_zero n)).mapExactFunctor J
        simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀])
      (by
        ext x
        change (x.mapExactFunctor J).comp (hS.map_of_exact J).extClass rfl =
          (x.comp hS.extClass rfl).mapExactFunctor J
        simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass])
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (J.obj A) (hS.map_of_exact J) n (n + 1) rfl))
      (hn S.X₂).2 (hn S.X₃)
      (fun x => Ext.covariant_sequence_exact₁ A hS x
        (Ext.eq_zero_of_injective (I := I.J) _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ (J.obj A) (hS.map_of_exact J) x
        (Ext.eq_zero_of_injective (I := J.obj I.J) _) rfl)

omit [Abelian C] [HasExt C] [Abelian D] [HasExt D] in
private theorem restrictionHom_bijective_of_iso (J : C ⥤ D) {A B : C} (q : A ≅ B)
    (hB : ∀ F : C, Function.Bijective (fun b : B ⟶ F => J.map b))
    (F : C) : Function.Bijective (fun a : A ⟶ F => J.map a) := by
  constructor
  · intro a b hab
    apply (cancel_epi q.inv).mp
    apply (hB F).1
    simpa only [J.map_comp] using congrArg (fun t => J.map q.inv ≫ t) hab
  · intro c
    obtain ⟨b, hb⟩ := (hB F).2 (J.map q.inv ≫ c)
    refine ⟨q.hom ≫ b, ?_⟩
    dsimp only at hb ⊢
    rw [J.map_comp, hb, ← J.map_comp_assoc, q.hom_inv_id, J.map_id, Category.id_comp]

private theorem restrictAddHom_bijective_of_mapExt (J : C ⥤ D) [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {A F : C} {B E : D} (e : J.obj A ≅ B) (d : J.obj F ≅ E) (n : ℕ)
    (h : Function.Bijective (J.mapExtAddHom A F n)) :
    Function.Bijective (Ext.restrictAddHom J e d n) := by
  let post : Ext B (J.obj F) n ≃+ Ext B E n :=
    { toFun := fun x => x.comp (Ext.mk₀ d.hom) (add_zero n)
      invFun := fun x => x.comp (Ext.mk₀ d.inv) (add_zero n)
      left_inv := by
        intro x
        dsimp only
        rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, d.hom_inv_id,
          Ext.comp_mk₀_id]
      right_inv := by
        intro x
        dsimp only
        rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, d.inv_hom_id,
          Ext.comp_mk₀_id]
      map_add' := by intro x y; exact Ext.add_comp _ _ _ _ }
  exact post.bijective.comp
    ((Ext.precompAddEquiv e.symm (J.obj F) n).bijective.comp h)

end DimensionShift

namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}

private theorem openBaseChangeInclusion_eq (f : X ⟶ Spec (.of R)) (W : X.Opens) :
    H.openBaseChangeInclusion (S := S) f W =
      (pullbackRightPullbackFstIso f (baseChangeMap R S) W.ι).inv ≫
        Limits.pullback.snd W.ι (baseChangeFst (S := S) f) := by
  apply Limits.pullback.hom_ext
  · exact (Limits.pullback.lift_fst _ _ _).trans
      (pullbackRightPullbackFstIso_inv_snd_fst f (baseChangeMap R S) W.ι).symm
  · exact (Limits.pullback.lift_snd _ _ _).trans
      ((pullbackRightPullbackFstIso_inv_snd_snd f (baseChangeMap R S) W.ι).symm.trans
        (Category.assoc _ _ _).symm)

private theorem openBaseChangeInclusion_isOpenImmersion
    (f : X ⟶ Spec (.of R)) (W : X.Opens) :
    IsOpenImmersion (H.openBaseChangeInclusion (S := S) f W) := by
  rw [openBaseChangeInclusion_eq]
  infer_instance

attribute [local instance] openBaseChangeInclusion_isOpenImmersion

private theorem openBaseChangeInclusion_opensRange
    (f : X ⟶ Spec (.of R)) (W : X.Opens) :
    (H.openBaseChangeInclusion (S := S) f W).opensRange =
      baseChangeFst (S := S) f ⁻¹ᵁ W := by
  simp only [openBaseChangeInclusion_eq, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]

/-- Restriction from the free sheaf on an open, before and after base change, is bijective.
Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
(blueprint: lem-pc-open-restriction-ext-bijective)

Proof: Restriction preserves injective abelian sheaves, and is bijective on
ordinary morphisms from the free sheaf of its image open. Induct on Ext degree,
generalizing the coefficient sheaf. Degree zero is the morphism assertion through
Ext.mk₀. In the successor step choose an injective presentation and its cokernel
short exact sequence. Exact restriction preserves this sequence and the middle
object is still injective. The two covariant Ext sequences are right exact and
the connecting morphisms commute with the exact-functor map. The induction
hypothesis and the additive five lemma give bijectivity in the next degree.
For base change, express the constructed inclusion as a pullback projection
preceded by the inverse of the pullback-pasting isomorphism. It is open and its
image is the preimage of W. The inverse-image/free-sheaf isomorphism, proved by
adjunction and Yoneda, transports the ordinary morphism assertion to the pulled
free sheaf. Apply the same induction. Finally, precomposition with e.inv or
e'.inv and postcomposition with d.hom or d'.hom are bijective, with inverses
induced by the inverse object isomorphisms. This proves the specific restriction
maps for all independently chosen isomorphisms. Empty opens, top opens and zero
coefficients are included; no flatness or quasi-coherence is used.
-/
theorem H.openRestrictionExt_bijective
    (f : X ⟶ Spec (.of R)) (M : X.Modules) (W : X.Opens)
    (e : (invImage W.ι).obj (H.openFreeSheaf W) ≅
      H.openFreeSheaf (⊤ : W.toScheme.Opens))
    (d : (invImage W.ι).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) ≅
      (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj ((pullback W.ι).obj M))
    (e' : (invImage (H.openBaseChangeInclusion (S := S) f W)).obj
      ((invImage (baseChangeFst (S := S) f)).obj (H.openFreeSheaf W)) ≅
      (invImage (baseChangeFst (S := S) (W.ι ≫ f))).obj
        (H.openFreeSheaf (⊤ : W.toScheme.Opens)))
    (d' : (invImage (H.openBaseChangeInclusion (S := S) f W)).obj
      ((SheafOfModules.toSheaf (baseChangedScheme (S := S) f).ringCatSheaf).obj
        (baseChangedModule (S := S) f M)) ≅
      (SheafOfModules.toSheaf (baseChangedScheme (S := S) (W.ι ≫ f)).ringCatSheaf).obj
        (baseChangedModule (S := S) (W.ι ≫ f) ((pullback W.ι).obj M))) :
    (∀ n, Function.Bijective (Ext.restrictAddHom (invImage W.ι) e d n)) ∧
      (∀ n, Function.Bijective
        (Ext.restrictAddHom
          (invImage (H.openBaseChangeInclusion (S := S) f W)) e' d' n)) := by
  constructor
  · intro n
    have := invImage_preservesInjectiveObjects_of_openImmersion W.ι
    apply restrictAddHom_bijective_of_mapExt
    apply mapExt_bijective_of_restrictionHom
    exact restrictionHom_bijective_of_iso (invImage W.ι)
      (eqToIso (congrArg H.openFreeSheaf (Scheme.Opens.opensRange_ι W).symm))
      (H.openFreeSheaf_restrictionHom_bijective W.ι)
  · intro n
    let k := H.openBaseChangeInclusion (S := S) f W
    have := invImage_preservesInjectiveObjects_of_openImmersion k
    obtain ⟨a⟩ := H.invImage_openFreeSheaf_iso (baseChangeFst (S := S) f) W
    let q := a ≪≫ eqToIso (congrArg H.openFreeSheaf
      (openBaseChangeInclusion_opensRange (S := S) f W).symm)
    apply restrictAddHom_bijective_of_mapExt
    apply mapExt_bijective_of_restrictionHom
    exact restrictionHom_bijective_of_iso (invImage k) q
      (H.openFreeSheaf_restrictionHom_bijective k)


end AlgebraicGeometry.Scheme.Modules
