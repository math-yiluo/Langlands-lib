/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalAffineBaseChangeComparison
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Conormal sheaves under flat base change
Source: Stacks Project, Morphisms, Lemma 0473 (morphisms-lemma-conormal-functorial-flat),
case of closed immersions (blueprint: lem-weil-pbc-closed-immersion-conormal-flat-base-change).
-/

@[expose] public section

universe uc
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
/-- For a cartesian square of closed immersions, the canonical conormal map is an
 epimorphism; if the ambient morphism is flat, it is an isomorphism. The canonical map
 is the unique map supplied by `closedImmersion_conormal_functorial`.

Source: Stacks Project, Morphisms, Lemma 0473 (lemma-conormal-functorial-flat),
closed-immersion case; Schemes, Lemma 01JU (lemma-fibre-product-immersion), assertion (1)
(blueprint: lem-weil-pbc-closed-immersion-conormal-flat-base-change).
Proof:
1. Compatible pairs of affine opens in X and X' form a basis of X. Since i is a
   closed embedding, their inverse images form a basis of Z and an affine cover.
2. The affine comparison lemma identifies each section map with
   Ideal.tensorCotangentHom. Its surjectivity, transported through the two
   equivalences, gives surjectivity on the basis. Restricting each section to
   a basis neighbourhood proves local surjectivity. The underlying additive
   sheaf map is therefore epi; the forgetful functor reflects epimorphisms.
3. If g is flat, its affine ring maps are flat. The injectivity of
   Ideal.tensorCotangentHom under flat base change gives bijectivity on this
   basis. TopCat.Sheaf.isIso_iff_isIso_basis gives an isomorphism of the underlying
   additive sheaves, and toPresheaf reflects isomorphisms of modules. -/
theorem closedImmersion_conormal_flat_base_change
    {X Z X' Z' : Scheme.{uc}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
      (tensorPullback i).obj i.ker.toModules)
    (hcanonical : c = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    : Epi c ∧ (Flat g → IsIso c) := by
  classical
  let Charts := {p : X.affineOpens × X'.affineOpens // p.1.1 ≤ g ⁻¹ᵁ p.2.1}
  let A : Charts → X.Opens := fun t ↦ t.1.1.1
  let B : Charts → Z.Opens := fun t ↦ i ⁻¹ᵁ A t
  have hA : Opens.IsBasis (Set.range A) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨U', hU', hxU', _⟩ := exists_isAffineOpen_mem_and_subset
      (show g x ∈ (⊤ : X'.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ W ⊓ g ⁻¹ᵁ U' from ⟨hx, hxU'⟩)
    let t : Charts := ⟨(⟨U, hU⟩, ⟨U', hU'⟩), le_trans hUW inf_le_right⟩
    exact ⟨U, ⟨t, rfl⟩, hxU, le_trans hUW inf_le_left⟩
  have hB : Opens.IsBasis (Set.range B) := by
    convert hA.of_isInducing i.isClosedEmbedding.isInducing using 1
    ext V
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨A t, ⟨t, rfl⟩, ht⟩
    · rintro ⟨U, ⟨t, rfl⟩, ht⟩
      exact ⟨t, ht⟩
  have hsurj : ∀ t, Function.Surjective (c.app (B t)) := by
    intro t
    let : Algebra Γ(X', t.1.2.1) Γ(X, t.1.1.1) :=
      (g.appLE t.1.2.1 t.1.1.1 t.2).hom.toAlgebra
    obtain ⟨eS, eT, he⟩ := closedImmersion_conormal_affine_base_change_comparison
      i i' g f h hc c hcanonical t.1.1 t.1.2 t.2
    intro y
    obtain ⟨a, ha⟩ := (i'.ker.ideal t.1.2).tensorCotangentHom_surjective
      Γ(X', t.1.2.1) Γ(X, t.1.1.1) (eT y)
    refine ⟨eS.symm a, eT.injective ?_⟩
    rw [he, eS.apply_symm_apply, ha]
  have hepi : Epi c := by
    have hloc : TopCat.Presheaf.IsLocallySurjective ((toPresheaf Z).map c) := by
      rw [TopCat.Presheaf.isLocallySurjective_iff]
      intro W y z hz
      obtain ⟨V, ⟨t, rfl⟩, hzV, hVW⟩ := Opens.isBasis_iff_nbhd.mp hB hz
      obtain ⟨s, hs⟩ := hsurj t
        (((tensorPullback i).obj i.ker.toModules).presheaf.map (homOfLE hVW).op y)
      exact ⟨B t, hVW, ⟨s, hs⟩, hzV⟩
    have : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map c) := hloc
    exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map
      (Sheaf.epi_of_isLocallySurjective _)
  refine ⟨hepi, ?_⟩
  intro hg
  have : Flat g := hg
  have hbij : ∀ t, Function.Bijective (c.app (B t)) := by
    intro t
    let : Algebra Γ(X', t.1.2.1) Γ(X, t.1.1.1) :=
      (g.appLE t.1.2.1 t.1.1.1 t.2).hom.toAlgebra
    have : Module.Flat Γ(X', t.1.2.1) Γ(X, t.1.1.1) :=
      g.flat_appLE t.1.2.2 t.1.1.2 t.2
    obtain ⟨eS, eT, he⟩ := closedImmersion_conormal_affine_base_change_comparison
      i i' g f h hc c hcanonical t.1.1 t.1.2 t.2
    refine ⟨?_, hsurj t⟩
    intro a b hab
    apply eS.injective
    apply (i'.ker.ideal t.1.2).tensorCotangentHom_injective_of_flat
      Γ(X', t.1.2.1) Γ(X, t.1.1.1)
    rw [← he a, ← he b, hab]
  let F : TopCat.Sheaf AddCommGrpCat Z :=
    ⟨((tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules)).presheaf,
      ((tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules)).isSheaf⟩
  let G : TopCat.Sheaf AddCommGrpCat Z :=
    ⟨((tensorPullback i).obj i.ker.toModules).presheaf,
      ((tensorPullback i).obj i.ker.toModules).isSheaf⟩
  let ψ : F ⟶ G := Sheaf.homEquiv.symm ((toPresheaf Z).map c)
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB fun t ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (hbij t)
  have : IsIso ((toPresheaf Z).map c) := by
    obtain ⟨d, hd₁, hd₂⟩ := hψ.out
    exact ⟨d.hom, congrArg (fun a ↦ a.hom) hd₁, congrArg (fun a ↦ a.hom) hd₂⟩
  exact isIso_of_reflects_iso c (toPresheaf Z)
end AlgebraicGeometry.Scheme.Modules
