/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Zero sets of quasi-coherent ideal sheaves on affine opens

Source: Stacks Project, Schemes, Example 01HM and Lemma 01IN
(blueprint: lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The underlying abelian-group stalk map is surjective precisely off the support.
Lift the germ of `1` and shrink the equality to an affine neighborhood for the forward
implication. For the reverse implication, restrict each representative to an affine
neighborhood disjoint from the support, where the ideal of sections is the unit ideal.
Source: Stacks Project, Schemes, Example 01HM and Lemma 01IN; the germ argument is
written directly using Mathlib's representation and equality lemmas for stalks.
(blueprint: lem-weil-pbc-quasi-coherent-ideal-zero-set-affine). -/
private theorem stalk_surjective_iff_not_mem_support (X : Scheme.{u})
    (K : X.IdealSheafData) (x : X) :
    Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom ↔
      x ∉ K.support := by
  let O := (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  let F : TopCat.Presheaf Ab X.toTopCat := K.toModules.val.presheaf
  let G : TopCat.Presheaf Ab X.toTopCat := O.val.presheaf
  let f : F ⟶ G := (PresheafOfModules.toPresheaf _).map K.toModulesι.val
  change Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab x).map f) ↔ _
  constructor
  · intro hs hx
    obtain ⟨a, ha⟩ := hs (G.germ ⊤ x (by trivial) (1 : Γ(X, ⊤)))
    obtain ⟨U, hxU, a, rfl⟩ := F.exists_germ_eq a
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ha
    obtain ⟨W, hxW, hW, hWU, hWT, he⟩ :=
      G.germ_eq_of_isBasis X.isBasis_affineOpens x hxU (by trivial) ha
    have hres : f.app (Opposite.op W) (F.map (homOfLE hWU).op a) =
        (1 : Γ(X, W)) := by
      rw [← ConcreteCategory.comp_apply, f.naturality,
        ConcreteCategory.comp_apply]
      have h1 : G.map (homOfLE hWT).op (1 : Γ(X, ⊤)) = (1 : Γ(X, W)) := by
        change X.presheaf.map (homOfLE hWT).op 1 = 1
        exact map_one _
      exact he.trans h1
    have hone : (1 : Γ(X, W)) ∈ K.ideal ⟨W, hW⟩ := by
      change (1 : Γ(X, W)) ∈ (K.ideal ⟨W, hW⟩ : Set Γ(X, W))
      rw [← K.range_toModulesι_app ⟨W, hW⟩]
      exact ⟨F.map (homOfLE hWU).op a, hres⟩
    have hz := (K.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW).mp hx
    exact ((X.mem_zeroLocus_iff _ x).mp hz) 1 hone (by simpa using hxW)
  · intro hx b
    obtain ⟨V, hxV, b, rfl⟩ := G.exists_germ_eq b
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ V.1 ∩ (K.support : Set X)ᶜ from ⟨hxV, hx⟩)
        (V.isOpen.inter K.support.isClosed.isOpen_compl)
    have htop : K.ideal ⟨W, hW⟩ = ⊤ :=
      K.ideal_eq_top_of_disjoint_support (Set.disjoint_left.mpr
        (fun y hyW hyK ↦ (hWV hyW).2 hyK))
    have hb : G.map (homOfLE (fun y hy ↦ (hWV hy).1)).op b ∈
        Set.range (K.toModulesι.app W) := by
      rw [K.range_toModulesι_app ⟨W, hW⟩, htop]
      trivial
    obtain ⟨a, ha⟩ := hb
    refine ⟨F.germ W x hxW a, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change G.germ W x hxW (K.toModulesι.app W a) = _
    rw [ha]
    exact G.germ_res_apply _ x hxW b

/-- The stalk inclusion of a quasi-coherent ideal is injective. On an affine open it is
surjective exactly when the ideal of sections is not contained in the prime of the point.
Thus the set of points where the stalk ideal is proper is locally the ordinary zero locus,
is closed, and equals the image of every closed immersion with this kernel ideal sheaf.
Here `K : X.IdealSheafData` is the compatible affine-local encoding of a quasi-coherent
ideal sheaf, whose actual submodule sheaf and inclusion are `K.toModules` and `K.toModulesι`.
Surjectivity means that the image ideal is the whole stalk ring, without choosing an
identification of the module stalk of the structure sheaf with its ring stalk.

Source: Stacks Project, Schemes, Example 01HM, Lemmas 01HP and 01IN
(blueprint: lem-weil-pbc-quasi-coherent-ideal-zero-set-affine).

Proof:
1. The underlying map is Mathlib's abelian-group stalk map. Sectionwise injectivity of
   `K.toModulesι` implies its stalkwise injectivity by the concrete stalk lemma.
2. If the stalk inclusion is surjective, lift the germ of the global section `1`.
   Represent the lift on an open neighborhood, then shrink the equality of germs
   to an affine neighborhood W. Naturality shows that the restricted section maps
   to `1`, so `1` belongs to `K.ideal W`. Hence the point is outside `K.support`.
3. Conversely, outside the closed support, restrict any representative to an affine
   neighborhood W contained in its domain and disjoint from the support. The ideal
   `K.ideal W` is the unit ideal by `ideal_eq_top_of_disjoint_support`, so the restricted
   section lifts through `K.toModulesι.app W`. Taking its germ gives the required lift.
4. Thus the set of nonsurjective stalk maps is `K.support`. The affine prime criterion
   and affine zero-locus equality follow from `mem_support_iff_of_mem`,
   `fromSpec_preimage_zeroLocus`, `fromSpec_primeIdealOf`, and `fromSpec_image_zeroLocus`.
5. Closedness is `K.support.isClosed`. For a closed immersion with kernel K, use
   `Scheme.Hom.support_ker` and closedness of its range to identify that range with K's
   support. -/
theorem quasi_coherent_ideal_zero_set_affine (X : Scheme.{u}) (K : X.IdealSheafData) :
    (∀ x : X, Function.Injective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom) ∧
    (∀ (U : X.affineOpens) (x : U.1),
      Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x.1).map K.toModulesι).hom ↔
      ¬ K.ideal U ≤ (U.2.primeIdealOf x).asIdeal) ∧
    (∀ U : X.affineOpens,
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∩ U.1 =
      U.2.fromSpec '' {p : PrimeSpectrum Γ(X, U.1) | K.ideal U ≤ p.asIdeal}) ∧
    IsClosed {x : X | ¬ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} ∧
    (∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i], i.ker = K →
      Set.range i = {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom}) := by
  have hset :
      {x : X | ¬ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} =
        (K.support : Set X) := by
    ext x
    simp only [Set.mem_ofPred_eq, stalk_surjective_iff_not_mem_support, not_not]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map K.toModulesι.val))
    apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    intro U
    exact K.injective_toModulesι_app U
  · intro U x
    rw [stalk_surjective_iff_not_mem_support,
      K.mem_support_iff_of_mem (U := U) x.2]
    apply not_congr
    have h := Set.ext_iff.mp (U.2.fromSpec_preimage_zeroLocus (K.ideal U))
      (U.2.primeIdealOf x)
    change (U.2.fromSpec (U.2.primeIdealOf x) ∈ X.zeroLocus (U := U.1)
      (K.ideal U : Set Γ(X, U.1))) ↔
      K.ideal U ≤ (U.2.primeIdealOf x).asIdeal at h
    rwa [U.2.fromSpec_primeIdealOf] at h
  · intro U
    rw [hset, K.coe_support_inter U]
    exact (U.2.fromSpec_image_zeroLocus (K.ideal U)).symm
  · rw [hset]
    exact K.support.isClosed
  · intro Z i hi hker
    rw [hset, ← hker, i.support_ker]
    exact IsClosedImmersion.isClosedEmbedding i |>.isClosed_range |>.closure_eq.symm

end AlgebraicGeometry.Scheme
