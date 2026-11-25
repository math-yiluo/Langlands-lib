/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Coproducts of complexes in the derived category of module sheaves

The K-injective proof of `CategoryTheory.derivedModuleDirectSums` applies to module
sheaves as well. We reuse its generic homotopy lemmas for this category.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

local instance (X : Scheme.{u}) (I : Type u)
    (K : I → CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HasCoproduct K := HasColimitsOfShape.has_colimit _

/-- The termwise coproduct representative has the coproduct universal property in the
derived category. This is the localization and coproduct part of the direct-sums lemma.
Source: Stacks Project, Injectives, Lemma 07D9 (1)-(2).
(blueprint: lem-pc-derived-ambient-direct-sums-cofan)

Proof: Sheaves of modules form a Grothendieck abelian category, so every complex
has a K-injective resolution. Given any target in the derived category, choose such a
resolution J. Morphisms into Q(J) are chain maps modulo homotopy. A chain map from
the termwise coproduct to J is uniquely specified by a family of chain maps K(i) to J:
the degreewise coproduct property assembles their components, and the chain-map
identities follow by precomposing with each coprojection. The same property assembles
a family of homotopies degreewise, so two assembled maps are homotopic exactly when
all their restrictions are homotopic. Consequently restriction is a bijection from
Hom(Q(∐ K), Q(J)) to the product of Hom(Q(K(i)), Q(J)). Transport the target along
its K-injective resolution and each source along e(i); the resulting restriction maps
are composition with the displayed legs from E(i) to Q(∐ K). These natural bijections
give the required colimit. For an empty family the product of Hom sets is a singleton;
for a singleton this construction gives the usual representative isomorphism. -/
theorem derivedAmbientDirectSumsCofan (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (K : I → CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : ∀ i : I, DerivedCategory.Q.obj (K i) ≅ E i) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ (e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian _
  let : Abelian.HasKInjectiveResolutions C :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u}
  have hu (Y : DerivedCategory C)
      (a : ∀ i, DerivedCategory.Q.obj (K i) ⟶ Y) :
      ∃! d : DerivedCategory.Q.obj (∐ K) ⟶ Y,
        ∀ i, DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨L, _, r, _, _⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective
        (DerivedCategory.Q.objPreimage Y)
    let iso : Y ≅ DerivedCategory.Q.obj L :=
      (DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫ asIso (DerivedCategory.Q.map r)
    choose f hf using fun i ↦ CategoryTheory.derived_map_surjective (K i) L (a i ≫ iso.hom)
    let d := DerivedCategory.Q.map (Sigma.desc f) ≫ iso.inv
    have hd (i : I) : DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
      dsimp [d]
      rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_comp_desc, hf]
      simp
    refine ⟨d, hd, ?_⟩
    intro m hm
    apply (cancel_mono iso.hom).1
    obtain ⟨g, hg⟩ := CategoryTheory.derived_map_surjective (∐ K) L (m ≫ iso.hom)
    have he (i : I) :
        DerivedCategory.Q.map (Sigma.ι K i ≫ g) = DerivedCategory.Q.map (f i) := by
      rw [Functor.map_comp, hg, ← Category.assoc, hm, hf]
    have hhom := CategoryTheory.coproduct_homotopy K g (Sigma.desc f) (fun i ↦
      (CategoryTheory.derived_map_homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f)
        (by simpa only [Sigma.ι_comp_desc] using he i)).some)
    rw [← hg, DerivedCategory.Q_map_eq_of_homotopy _ hhom.some]
    simp [d]
  let a (t : Cofan E) (i : I) := (e i).hom ≫ t.inj i
  refine ⟨Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt (a t)).choose) ?_ ?_⟩
  · intro t i
    change ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)) ≫ _ = _
    rw [Category.assoc, (hu t.pt (a t)).choose_spec.1 i]
    simp [a]
  · intro t m hm
    apply (hu t.pt (a t)).choose_spec.2 m
    intro i
    have hi := hm i
    change ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)) ≫ m = t.inj i at hi
    dsimp [a]
    rw [← hi]
    simp

end AlgebraicGeometry
