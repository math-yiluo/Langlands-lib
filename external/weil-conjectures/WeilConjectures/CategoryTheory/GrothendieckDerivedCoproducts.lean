/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Coproducts in derived categories with K-injective resolutions

Source: Stacks Project, Tag 07D9, Lemma 19.13.4, coproduct clauses (1)-(2).
-/

@[expose] public section

universe w v u s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem derivedCoproductCofan
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [Abelian.HasKInjectiveResolutions C] [HasCoproducts.{s} C]
    (I : Type s) (E : I → DerivedCategory C)
    (K : I → CochainComplex C ℤ) (e : ∀ i, DerivedCategory.Q.obj (K i) ≅ E i) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ (e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  classical
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

/-- A derived category with K-injective resolutions has coproducts at every size
at which the underlying abelian category has coproducts.
Source: Stacks Project, Tag 07D9, Lemma 19.13.4, coproduct clauses (1)-(2).
(auxiliary; not a blueprint node)

Proof in words: choose a complex representative of each derived object and form
its termwise coproduct. Resolve any target by a K-injective complex. Derived maps
into it are chain maps modulo homotopy. The degreewise coproduct property assembles
chain maps, and also assembles homotopies. Thus restriction to the coprojections
is a bijection on derived Hom sets. Transport the coprojections along the chosen
representative isomorphisms to obtain a coproduct of the original family. This
works also for the empty family; no exactness of coproducts is needed. -/
theorem derived_hasCoproducts
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    [Abelian.HasKInjectiveResolutions C] [HasCoproducts.{s} C] :
    HasCoproducts.{s} (DerivedCategory C) := by
  classical
  let Q := DerivedCategory.Q (C := C)
  let K {I : Type s} (E : I → DerivedCategory C) := fun i ↦ Q.objPreimage (E i)
  let e {I : Type s} (E : I → DerivedCategory C) := fun i ↦ Q.objObjPreimageIso (E i)
  let c {I : Type s} (E : I → DerivedCategory C) : Cofan E :=
    Cofan.mk (Q.obj (∐ K E)) (fun i ↦ (e E i).inv ≫ Q.map (Sigma.ι (K E) i))
  exact hasCoproducts_of_colimit_cofans (fun E ↦ c E)
    (fun E ↦ (derivedCoproductCofan _ E (K E) (e E)).some)

end CategoryTheory
