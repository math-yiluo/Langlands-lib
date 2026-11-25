/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenComparison
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnitNaturality
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Normalization of the source-open comparison at the whole scheme

Source: Stacks Project, Tag 0DJ9, the final application U = X.
(blueprint: lem-pc-single-complex-open-top).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The top-open comparison is the original comparison up to canonical isomorphisms.
Source: Stacks Project, Tag 0DJ9, conclusion of source-open induction.
(blueprint: lem-pc-single-complex-open-top).

Proof: The top-open immersion is an isomorphism. Its base change is an isomorphism,
and the other projection identifies the fibre product with X'. Derived pullback
along either isomorphism is an equivalence, with inverse the corresponding derived
direct image. The composition comparisons and these equivalences identify the
source and target of the top-open comparison with those of the original comparison.
The adjoint counit description of schemeDerivedBaseChangeMap, naturality of the
counits, and coherence of the composition comparisons identify the two arrows.
Conjugating an invertible morphism by isomorphisms is invertible. This works for
any commutative square and arbitrary derived objects, including the empty scheme;
it uses neither quasi-coherence nor the stalk hypothesis. -/
theorem singleComplexOpenComparison_top
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (htop : IsIso (singleComplexOpenComparison f f' g g' h K K' φ ⊤)) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' h K ≫
      (schemeDerivedDirectImage f').map φ) := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))
  let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction s
      (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) s))
  obtain ⟨_, i, _, _, _⟩ := Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))
  have unitIso {A B : Scheme.{u}} (e : A ≅ B) : IsIso (a e.hom).unit := by
    let b : derivedPullback e.hom ⋙ derivedPullback e.inv ≅ 𝟭 _ :=
      c e.inv e.hom ≪≫
        eqToIso (congrArg (fun s ↦ derivedPullback s) e.inv_hom_id) ≪≫ i B
    let d : derivedPullback e.inv ⋙ derivedPullback e.hom ≅ 𝟭 _ :=
      c e.hom e.inv ≪≫
        eqToIso (congrArg (fun s ↦ derivedPullback s) e.hom_inv_id) ≪≫ i A
    have : (derivedPullback e.inv).Faithful := Functor.Faithful.of_comp_iso d
    have : (derivedPullback e.hom).Faithful := Functor.Faithful.of_comp_iso b
    have : (derivedPullback e.hom).Full := Functor.Full.of_comp_faithful_iso b
    infer_instance
  have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
    inferInstanceAs (IsIso X.topIso.hom)
  let p := pullback.fst g' (Scheme.Opens.ι (⊤ : X.Opens))
  have : IsIso p := inferInstance
  have ht : IsIso (a (Scheme.Opens.ι (⊤ : X.Opens))).unit := unitIso X.topIso
  have hp : IsIso (a p).unit := unitIso (asIso p)
  let k := conjugateIsoEquiv (a ((⊤ : X.Opens).ι ≫ f))
    ((a f).comp (a (⊤ : X.Opens).ι)) (c (⊤ : X.Opens).ι f)
  let k' := conjugateIsoEquiv (a (p ≫ f')) ((a f').comp (a p)) (c p f')
  have eqn := singleComplexOpenComparison_unit_naturality f f' g g' h K K' φ ⊤
  change (derivedPullback g).map
      ((schemeDerivedDirectImage f).map ((a (⊤ : X.Opens).ι).unit.app K) ≫
        k.inv.app ((derivedPullback (⊤ : X.Opens).ι).obj K)) ≫
      singleComplexOpenComparison f f' g g' h K K' φ ⊤ =
    (schemeDerivedBaseChangeMap f f' g g' h K ≫
      (schemeDerivedDirectImage f').map φ) ≫
      ((schemeDerivedDirectImage f').map ((a p).unit.app K') ≫
        k'.inv.app ((derivedPullback p).obj K')) at eqn
  have hiso : IsIso ((schemeDerivedBaseChangeMap f f' g g' h K ≫
      (schemeDerivedDirectImage f').map φ) ≫
      ((schemeDerivedDirectImage f').map ((a p).unit.app K') ≫
        k'.inv.app ((derivedPullback p).obj K'))) := by
    rw [← eqn]
    infer_instance
  exact (isIso_comp_right_iff (schemeDerivedBaseChangeMap f f' g g' h K ≫
    (schemeDerivedDirectImage f').map φ)
    ((schemeDerivedDirectImage f').map ((a p).unit.app K') ≫
      k'.inv.app ((derivedPullback p).obj K'))).mp hiso

end AlgebraicGeometry
