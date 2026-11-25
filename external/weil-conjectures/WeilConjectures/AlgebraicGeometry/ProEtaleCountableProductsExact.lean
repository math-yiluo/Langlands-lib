/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits

/-!
# Exact countable products of pro-etale module sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Propositions 3.1.9,
3.2.3 (1), and 4.2.8; Stacks Project, Tags 03DB and 0947 (4)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe t u w v v'

open CategoryTheory CategoryTheory.Limits Opposite

/-- Weak contractibility is unchanged by enlarging the universe of sections.
Choose one local lift for each arrow of the image sieve of a fixed section.
The coproduct of the corresponding representables is a small presheaf mapping
locally surjectively to the representable of W. Sheafify, apply weak contractibility,
and map the resulting section to the original sheaf, using compatibility of
sheafification with universe lifting. -/
private theorem large_section_surjective
    {C : Type v} [Category.{v'} C] (J : GrothendieckTopology C) (W : C)
    (hW : ∀ (F G : Sheaf J (Type (max v v'))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W)))
    (F G : Sheaf J (Type (max u v v'))) (e : F ⟶ G)
    [Sheaf.IsLocallySurjective e] : Function.Surjective (e.hom.app (op W)) := by
  classical
  intro x
  let S := Presheaf.imageSieve e.hom x
  let P : Cᵒᵖ ⥤ Type (max v v') :=
    { obj := fun V ↦ Σ (Z : C) (g : Z ⟶ W), {h : V.unop ⟶ Z // S g}
      map := fun a ↦ TypeCat.ofHom (fun z ↦
        ⟨z.1, z.2.1, a.unop ≫ z.2.2.val, z.2.2.property⟩)
      map_id := by intros; apply ConcreteCategory.hom_ext; intro z; simp
      map_comp := by intros; apply ConcreteCategory.hom_ext; intro z; simp [Category.assoc] }
  let Q := uliftYoneda.{v}.obj W
  let b : P ⟶ Q :=
    { app := fun _ ↦ TypeCat.ofHom (fun z ↦ ⟨z.2.2.val ≫ z.2.1⟩)
      naturality := by
        intros
        apply ConcreteCategory.hom_ext
        intro z
        simp [P, Q, Category.assoc] }
  have hb : Presheaf.IsLocallySurjective J b := by
    constructor
    intro V a
    apply J.superset_covering (S := S.pullback a.down)
    · intro Z g hg
      exact ⟨⟨Z, g ≫ a.down, 𝟙 Z, hg⟩, by simp [b, Q]⟩
    · exact J.pullback_stable a.down (Presheaf.imageSieve_mem J e.hom x)
  let bS : (⟨J.sheafify P, J.sheafify_isSheaf P⟩ : Sheaf J (Type (max v v'))) ⟶
      ⟨J.sheafify Q, J.sheafify_isSheaf Q⟩ := ⟨J.sheafifyMap b⟩
  have : Epi bS := by
    have : Sheaf.IsLocallySurjective bS := by
      change Presheaf.IsLocallySurjective J (J.sheafifyMap b)
      have : Presheaf.IsLocallySurjective J (b ≫ J.toSheafify Q) := inferInstance
      rw [J.toSheafify_naturality] at this
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J (J.toSheafify P)
        (J.sheafifyMap b)
    infer_instance
  obtain ⟨z, hz⟩ := hW _ _ bS inferInstance ((J.toSheafify Q).app (op W) ⟨𝟙 W⟩)
  let L := uliftFunctor.{u, max v v'}
  let a : P ⋙ L ⟶ F.obj :=
    { app := fun V ↦ TypeCat.ofHom (fun z ↦ F.obj.map z.down.2.2.val.op
        (Presheaf.localPreimage e.hom x z.down.2.1 z.down.2.2.property))
      naturality := by intros; ext z; simp [L, P, Functor.map_comp] }
  let q : Q ⋙ L ⟶ G.obj :=
    { app := fun _ ↦ TypeCat.ofHom (fun z ↦ G.obj.map z.down.down.op x)
      naturality := by intros; ext z; simp [L, Q, Functor.map_comp] }
  have ha : a ≫ e.hom = Functor.whiskerRight b L ≫ q := by
    ext V z
    dsimp [a, q, b, L, Q]
    rw [NatTrans.naturality_apply, Presheaf.app_localPreimage]
    simp [Functor.map_comp]
  let aS := (J.sheafifyCompIso L P).hom ≫ J.sheafifyLift a F.property
  let qS := (J.sheafifyCompIso L Q).hom ≫ J.sheafifyLift q G.property
  have hS : aS ≫ e.hom = Functor.whiskerRight (J.sheafifyMap b) L ≫ qS := by
    have hn := (J.sheafificationWhiskerRightIso L).hom.naturality b
    change Functor.whiskerRight (J.sheafifyMap b) L ≫ (J.sheafifyCompIso L Q).hom =
      (J.sheafifyCompIso L P).hom ≫ J.sheafifyMap (Functor.whiskerRight b L) at hn
    dsimp only [aS, qS]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, J.sheafifyMap_sheafifyLift]
    rw [← ha]
    congr 1
    apply J.sheafify_hom_ext _ _ G.property
    simp
  refine ⟨aS.app (op W) ⟨z⟩, ?_⟩
  have hh := congrArg (fun k ↦ k.app (op W) ⟨z⟩) hS
  change e.hom.app (op W) (aS.app (op W) ⟨z⟩) = _ at hh
  rw [hh]
  change qS.app (op W) ⟨bS.hom.app (op W) z⟩ = x
  rw [hz]
  have hq : Functor.whiskerRight (J.toSheafify Q) L ≫ qS = q := by
    dsimp only [qS]
    rw [← Category.assoc, J.whiskerRight_toSheafify_sheafifyCompIso_hom,
      J.toSheafify_sheafifyLift]
  have := congrArg (fun k ↦ k.app (op W) ⟨⟨𝟙 W⟩⟩) hq
  simpa [q, L, Q] using this

/-- Coordinatewise lifts assemble in any product preserved by a functor to types. -/
private theorem map_product_surjective
    {D : Type*} [Category D] {I : Type w} (E : D ⥤ Type v)
    [HasProductsOfShape I D] [PreservesLimitsOfShape (Discrete I) E]
    (F G : I → D) (f : ∀ i, F i ⟶ G i)
    (hf : ∀ i, Function.Surjective (E.map (f i))) :
    Function.Surjective (E.map (Limits.Pi.map f)) := by
  classical
  let cF := E.mapCone (limit.cone (Discrete.functor F))
  let cG := E.mapCone (limit.cone (Discrete.functor G))
  let eF := Types.isLimitEquivSections
    (isLimitOfPreserves E (limit.isLimit (Discrete.functor F)))
  let eG := Types.isLimitEquivSections
    (isLimitOfPreserves E (limit.isLimit (Discrete.functor G)))
  intro y
  choose x hx using fun i ↦ hf i ((E.map (Limits.Pi.π G i)) y)
  let s : (Discrete.functor F ⋙ E).sections :=
    ⟨fun j ↦ x j.as, by
      rintro ⟨i⟩ ⟨j⟩ a
      obtain rfl := Discrete.eq_of_hom a
      have ha : a = 𝟙 _ := Subsingleton.elim _ _
      subst a
      simp⟩
  refine ⟨eF.symm s, ?_⟩
  apply eG.injective
  apply Subtype.ext
  funext j
  have hcoord : (E.map (Limits.Pi.π F j.as)) (eF.symm s) = x j.as :=
    congrArg (fun z ↦ z.val j) (eF.apply_symm_apply s)
  change (E.map (Limits.Pi.π G j.as)) (E.map (Limits.Pi.map f) (eF.symm s)) =
    (E.map (Limits.Pi.π G j.as)) y
  rw [← ConcreteCategory.comp_apply, ← E.map_comp, Limits.Pi.map_π, E.map_comp,
    ConcreteCategory.comp_apply, hcoord, hx]

namespace AlgebraicGeometry.Scheme.ProEt

/-- Countable products exist, evaluation computes them sectionwise, and a product
of epimorphisms is an epimorphism. Preservation by evaluation identifies the
canonical product cone with the product of section modules; thus both scalar actions
and restriction maps are coordinatewise. Surjectivity here is sheaf surjectivity,
expressed categorically by `Epi`, not surjectivity on every object's sections.

Source: Bhatt--Scholze, Propositions 3.1.9, 3.2.3 (1), 4.2.8;
Stacks Project, Tags 03DB and 0947 (4)
(auxiliary; not a blueprint node).

Proof:
1. Apply situation-conventions to discrete countable
   diagrams. Mathlib's module-sheaf limits give the product universal property,
   coordinatewise scalar actions, restrictions, and the evaluation identification.
2. Kernels are sectionwise by situation-conventions. The product
   functor is additive and preserves kernels and zero objects, hence is left exact.
3. For each site object use lem-weil-pbc-proetale-affine-wcontractible-covering-family
   to choose a cover by affine weakly contractible objects. By
   lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits, each given
   epimorphism is surjective on sections over each member of this cover.
4. Choose lifts of all coordinates over each fixed covering object, using ordinary
   set-theoretic choice. The sectionwise product formula assembles these lifts
   into a section of the product source mapping to the restricted target section.
5. If two maps out of the product target agree after composition with the product
   map, these local lifts make their values agree over the cover. Separatedness
   from def-weil-pbc-sites-and-cohomology gives equality of their values downstairs.
   They therefore agree, proving `Epi`. With step 2 this proves exactness.
The same argument works in every coefficient universe containing the site. -/
theorem countableProducts_exact (Y : Scheme.{t})
    (R : Sheaf (topology Y) CommRingCat.{max u (t + 1)}) :
    HasCountableProducts
      (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) ∧
    (∀ (I : Type w) [Countable I] (U : Y.ProEt),
      PreservesLimitsOfShape (Discrete I)
        (SheafOfModules.evaluation.{max u (t + 1)}
          ((sheafCompose (topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
          (op U))) ∧
    (∀ (I : Type w) [Countable I]
      (F G : I → ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (topology Y)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
      (f : ∀ i : I, F i ⟶ G i), (∀ i : I, Epi (f i)) → Epi (Limits.Pi.map f)) := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · intro I _ U
    have : PreservesLimitsOfShape (Discrete (Shrink.{0} I))
        (SheafOfModules.evaluation.{max u (t + 1)}
          ((sheafCompose (topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
          (op U)) := inferInstance
    exact preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{0} I).symm) _
  · intro I _ F G f hf
    let X : Scheme := Y
    let J := topology X
    let A := (sheafCompose J
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
    let T := SheafOfModules.toSheaf.{max u (t + 1)} A ⋙
      sheafCompose (topology Y) (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})
    have hlocal (i : I) : Sheaf.IsLocallySurjective (T.map (f i)) := by
      have : Epi (f i) := hf i
      let g := (SheafOfModules.toSheaf A).map (f i)
      have : Sheaf.IsLocallySurjective g :=
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr
          inferInstance
      change Sheaf.IsLocallySurjective
        ((sheafCompose (topology Y)
          (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g)
      infer_instance
    have : Sheaf.IsLocallySurjective (T.map (Limits.Pi.map f)) := by
      constructor
      intro U s
      obtain ⟨K, V, a, hcov, _, hweak⟩ :=
        exists_affine_weaklyContractible_covering_family X U
      apply (topology Y).superset_covering
        (S := Sieve.ofArrows V a) _ (Precoverage.generate_mem_toGrothendieck hcov)
      apply (Sieve.generate_le_iff _ _).mpr
      intro W g hg
      obtain ⟨k⟩ := hg
      let E := SheafOfModules.evaluation.{max u (t + 1)} A (op (V k)) ⋙
        CategoryTheory.forget _
      have : PreservesLimitsOfShape (Discrete I) E := by
        have : PreservesLimitsOfShape (Discrete (Shrink.{0} I)) E := inferInstance
        exact preservesLimitsOfShape_of_equiv
          (Discrete.equivalence (equivShrink.{0} I).symm) E
      have hs (i : I) : Function.Surjective (E.map (f i)) := by
        change Function.Surjective ((T.map (f i)).hom.app (op (V k)))
        exact large_section_surjective (C := X.ProEt) (J := topology X) (W := V k)
          (hW := hweak k)
          (T.obj (F i)) (T.obj (G i)) (T.map (f i))
      exact map_product_surjective E F G f hs
        ((T.obj (∏ᶜ G)).obj.map (a k).op s)
    exact T.epi_of_epi_map inferInstance

end AlgebraicGeometry.Scheme.ProEt
