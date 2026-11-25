/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Unramified.Field
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Hilbert 90 over quasi-compact étale schemes over a field

Let `K` be a field. Hilbert 90 for `Spec K`
(`AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf`) says that for a short exact
sequence `0 → 𝔾ₘ → E → Q → 0` of abelian sheaves on the small étale site of `Spec K`, every
global section of `Q` lifts to `E`. Here we extend this to the sections over every étale
`K`-scheme `W` with quasi-compact underlying space.

Such a `W` is a finite disjoint union of one-point schemes. A one-point étale `K`-scheme is the
spectrum of a finite separable field extension `L` of `K`, and restricting the sequence along
`Spec L ⟶ Spec K` (`AlgebraicGeometry.Etale.localizationRestriction`) reduces the lifting
problem over `W` to Hilbert 90 for `Spec L`, since `𝔾ₘ` restricts to `𝔾ₘ`.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf_of_subsingleton`: sections of
  `Q` lift to `E` over a one-point étale `K`-scheme.
- `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf_of_compactSpace`: sections of
  `Q` lift to `E` over an étale `K`-scheme with quasi-compact underlying space.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- An abelian étale sheaf has at most one section over an étale `X`-scheme with empty
underlying scheme. -/
lemma subsingleton_obj_of_isEmpty (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Z : X.Etale} [IsEmpty Z.left] : Subsingleton (F.obj.obj (op Z)) := by
  refine ⟨fun a b ↦ (isSheafFor_ofArrows F (U := (PEmpty.elim : PEmpty.{1} → X.Etale))
    (fun a ↦ a.elim)
    ?_).isSeparatedFor.ext fun _ _ ⟨a⟩ ↦ a.elim⟩
  exact Set.eq_univ_of_forall fun z ↦ isEmptyElim z

/-- The ring of global sections of a one-point scheme étale over a field is a field. -/
lemma isField_of_etale_of_subsingleton {K : Type u} [Field K] (W : (Spec (.of K)).Etale)
    [Subsingleton W.left] [Nonempty W.left] : IsField Γ(W.left, ⊤) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.left.isoSpec.inv ≫ W.hom)
  have hc : Etale (W.left.isoSpec.inv ≫ W.hom) := by
    have := W.prop
    infer_instance
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at hc
  algebraize [φ.hom]
  have : _root_.IsReduced Γ(W.left, ⊤) := Algebra.FormallyUnramified.isReduced_of_field K _
  have hsub : Subsingleton (PrimeSpectrum Γ(W.left, ⊤)) :=
    (TopCat.homeoOfIso (forgetToTop.mapIso W.left.isoSpec.symm)).injective.subsingleton
  have : Nonempty (PrimeSpectrum Γ(W.left, ⊤)) :=
    ⟨TopCat.homeoOfIso (forgetToTop.mapIso W.left.isoSpec) (Classical.arbitrary _)⟩
  have : Nontrivial Γ(W.left, ⊤) := (Classical.arbitrary (PrimeSpectrum _)).nontrivial
  refine ⟨exists_pair_ne _, mul_comm, fun {x} hx ↦ ?_⟩
  by_contra hu
  have hunit : ¬ IsUnit x := fun h ↦ hu ⟨h.unit⁻¹.1, h.mul_val_inv⟩
  obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal _ ((Ideal.span_singleton_ne_top hunit))
  have hnil : IsNilpotent x := by
    refine (nilpotent_iff_mem_prime).2 fun J hJ ↦ ?_
    have : J = m := congrArg PrimeSpectrum.asIdeal
      (hsub.elim ⟨J, hJ⟩ ⟨m, hm.isPrime⟩)
    exact this ▸ hxm (Ideal.mem_span_singleton_self x)
  exact hx (IsNilpotent.eq_zero hnil)

variable {K : Type u} [Field K]
  {E Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}}
  (ι : (Spec (.of K)).gmSheaf ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0)
  (hS : (ShortComplex.mk ι π w).ShortExact)
include hS

/-- **Hilbert 90 over a one-point étale `K`-scheme.** For a short exact sequence
`0 → 𝔾ₘ → E → Q → 0` of abelian sheaves on the small étale site of `Spec K` and an étale
`K`-scheme `W` with exactly one point, every section of `Q` over `W` lifts to `E`. -/
theorem surjective_app_of_shortExact_gmSheaf_of_subsingleton (W : (Spec (.of K)).Etale)
    [Subsingleton W.left] [Nonempty W.left] : Function.Surjective (π.hom.app (op W)) := by
  let := (isField_of_etale_of_subsingleton W).toField
  let L := ↥Γ(W.left, ⊤)
  let f : Spec (.of L) ⟶ Spec (.of K) := W.left.isoSpec.inv ≫ W.hom
  have hf : Etale f := by
    have := W.prop
    exact inferInstanceAs (Etale (W.left.isoSpec.inv ≫ W.hom))
  let R := Etale.localizationRestriction AddCommGrpCat.{u + 1} f hf
  have : R.IsLeftAdjoint :=
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} f hf).isLeftAdjoint
  have : PreservesFiniteLimits R := inferInstanceAs (PreservesFiniteLimits
    ((MorphismProperty.Over.map ⊤ hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      ((Spec (.of L)).smallGrothendieckTopology @AlgebraicGeometry.Etale)
      ((Spec (.of K)).smallGrothendieckTopology @AlgebraicGeometry.Etale)))
  -- the restriction of `𝔾ₘ` is `𝔾ₘ`
  let e : (Spec (.of L)).gmSheaf ≅ R.obj (Spec (.of K)).gmSheaf := Iso.refl _
  let ι' := e.hom ≫ R.map ι
  have w' : ι' ≫ R.map π = 0 := by simp [ι', ← Functor.map_comp, w]
  have hS' : (ShortComplex.mk ι' (R.map π) w').ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := (ShortComplex.mk ι π w).map R)
      (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _) (by simp [ι']) (by simp))
      (hS.map_of_exact R)
  -- the global sections of the restriction are the sections over `W`
  let T := MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of L)))
    (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of L)))
  let i : (MorphismProperty.Over.map ⊤ hf).obj T ≅ W :=
    MorphismProperty.Over.isoMk W.left.isoSpec.symm (by
      change W.left.isoSpec.inv ≫ W.hom = 𝟙 _ ≫ f
      rw [Category.id_comp])
  have hsurj : Function.Surjective (π.hom.app (op ((MorphismProperty.Over.map ⊤ hf).obj T))) :=
    surjective_app_of_shortExact_gmSheaf ι' (R.map π) w' hS'
  intro q
  obtain ⟨x, hx⟩ := hsurj (Q.obj.map i.hom.op q)
  refine ⟨E.obj.map i.inv.op x, ?_⟩
  rw [NatTrans.naturality_apply, hx, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- **Hilbert 90 over a quasi-compact étale `K`-scheme.** For a short exact sequence
`0 → 𝔾ₘ → E → Q → 0` of abelian sheaves on the small étale site of `Spec K` and an étale
`K`-scheme `W` whose underlying space is quasi-compact, every section of `Q` over `W` lifts to
`E`. -/
theorem surjective_app_of_shortExact_gmSheaf_of_compactSpace (W : (Spec (.of K)).Etale)
    [CompactSpace W.left] : Function.Surjective (π.hom.app (op W)) := by
  have := discreteTopology_of_etale_of_unique W
  let O (x : W.left) : W.left.Opens := ⟨{x}, isOpen_discrete _⟩
  let g (x : W.left) : Etale.ofOpens W (O x) ⟶ W := Etale.ofOpensι W (O x)
  have hg (x : W.left) : Set.range (g x).left = {x} := Scheme.Opens.range_ι (O x)
  have hcov : ⋃ x, Set.range (g x).left = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, by rw [hg]; rfl⟩
  have (x : W.left) : Subsingleton (Etale.ofOpens W (O x)).left :=
    ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  have (x : W.left) : Nonempty (Etale.ofOpens W (O x)).left := ⟨⟨x, rfl⟩⟩
  intro q
  choose e he using fun x ↦
    surjective_app_of_shortExact_gmSheaf_of_subsingleton ι π w hS _ (Q.obj.map (g x).op q)
  obtain ⟨y, hy, -⟩ := (Presieve.isSheafFor_arrows_iff _ g).1 (isSheafFor_ofArrows E g hcov) e
    fun a b Z ga gb hab ↦ by
      by_cases hZ : IsEmpty Z.left
      · exact (subsingleton_obj_of_isEmpty E (Z := Z)).elim _ _
      obtain ⟨z⟩ := not_isEmpty_iff.1 hZ
      have hz : (g a).left (ga.left z) = (g b).left (gb.left z) :=
        congrArg (fun φ ↦ φ.left z) hab
      have ha : (g a).left (ga.left z) = a := (hg a).subset ⟨_, rfl⟩
      have hb : (g b).left (gb.left z) = b := (hg b).subset ⟨_, rfl⟩
      obtain rfl : a = b := ha.symm.trans (hz.trans hb)
      obtain rfl : ga = gb := MorphismProperty.Over.Hom.ext
        ((cancel_mono (O a).ι).1 (congrArg (fun φ ↦ φ.left) hab))
      rfl
  refine ⟨y, (isSheafFor_ofArrows Q g hcov).isSeparatedFor.ext fun Z f ⟨x⟩ ↦ ?_⟩
  change Q.obj.map _ (π.hom.app _ y) = Q.obj.map _ q
  rw [← NatTrans.naturality_apply]
  erw [hy x]
  exact he x

end AlgebraicGeometry.Scheme
