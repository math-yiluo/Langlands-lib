/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor

/-!
# Exact restriction and K-flat complexes on a localized ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0E8K, lemma-restriction-K-flat;
Modules on Sites, Tags 03DJ and 0E8G
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

/-- Sheafification is injective on each single summand, by local injectivity of
its unit and separatedness of the original sheaf on the slice (Stacks 0E8G). -/
private theorem sheafification_single_injective
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w}) (U : C)
    (G : SheafOfModules.{max u v w} (R.over U)) (V : C) [DecidableEq (V ⟶ U)] (φ : V ⟶ U)
    (x y : G.val.obj (Opposite.op (Over.mk φ)))
    (h : (toSheafify J ((extensionByZeroPresheaf R U).obj G).presheaf).app (Opposite.op V)
        (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      (toSheafify J ((extensionByZeroPresheaf R U).obj G).presheaf).app (Opposite.op V)
        (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y)) :
    x = y := by
  classical
  let P := ((extensionByZeroPresheaf R U).obj G).presheaf
  let S := Presheaf.equalizerSieve (F := P)
    (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x)
    (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y)
  have hS : S ∈ J V := Presheaf.equalizerSieve_mem J (toSheafify J P) _ _ h
  let T := (Sieve.overEquiv (Over.mk φ)).symm S
  have hT : T ∈ (J.over U) (Over.mk φ) :=
    J.overEquiv_symm_mem_over (Over.mk φ) S hS
  apply G.isSheaf.isSeparated (Over.mk φ) T hT
  intro B f hf
  obtain ⟨B, ψ, rfl⟩ := B.mk_surjective
  obtain ⟨b, hb, rfl⟩ := Over.homMk_surjective f
  change B ⟶ V at b
  change b ≫ φ = ψ at hb
  subst ψ
  have he : P.map b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
    P.map b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y) := hf
  change extensionByZeroPresheafRestrictAdd R U G b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ x) =
    extensionByZeroPresheafRestrictAdd R U G b.op
      (DirectSum.of (fun ψ : V ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) φ y) at he
  dsimp only [extensionByZeroPresheafRestrictAdd] at he
  erw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of] at he
  erw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at he
  exact (DirectSum.of_injective
    (β := fun ψ : B ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) (b ≫ φ)) he

/-- The sheafified direct-sum extension from a ringed slice is faithful.

Source: Stacks Project, Modules on Sites, Tag 0E8G.
Proof: include each section in its indexed summand and use naturality of the
module sheafification unit. Equality of the extended maps gives equality of
the sheafified sections in that summand. The preceding local-injectivity
argument and separatedness of the original slice sheaf recover their equality. -/
private theorem ringedSliceExtension_faithful
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J RingCat.{max u v w}) (U : C) :
    (extensionByZeroPresheaf.{max u v w} R U ⋙
      PresheafOfModules.sheafification.{max u v w} (𝟙 R.obj)).Faithful := by
  classical
  let P := extensionByZeroPresheaf.{max u v w} R U
  let L := PresheafOfModules.sheafification.{max u v w} (𝟙 R.obj)
  let Q := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let adj : L ⊣ Q := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  constructor
  intro G H f g hfg
  have hn : P.map f ≫ adj.unit.app (P.obj H) = P.map g ≫ adj.unit.app (P.obj H) := by
    calc
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map f)) :=
        (adj.unit_naturality (P.map f)).symm
      _ = adj.unit.app (P.obj G) ≫ Q.map (L.map (P.map g)) :=
        congrArg (fun t ↦ adj.unit.app (P.obj G) ≫ Q.map t) hfg
      _ = _ := adj.unit_naturality (P.map g)
  ext V s
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun t ↦ (PresheafOfModules.toPresheaf R.obj).map t) hn)
      (Opposite.op V.unop.left))
    (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ))) V.unop.hom s)
  apply sheafification_single_injective.{u, v, w} J R U H V.unop.left V.unop.hom
  change (toSheafify J (P.obj H).presheaf).app (Opposite.op V.unop.left)
      ((extensionByZeroPresheafHomApp R U f (Opposite.op V.unop.left)).hom
        (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ)))
          V.unop.hom s)) =
    (toSheafify J (P.obj H).presheaf).app (Opposite.op V.unop.left)
      ((extensionByZeroPresheafHomApp R U g (Opposite.op V.unop.left)).hom
        (DirectSum.of (fun ψ : V.unop.left ⟶ U ↦ G.val.obj (Opposite.op (Over.mk ψ)))
          V.unop.hom s)) at he
  dsimp only [extensionByZeroPresheafHomApp] at he
  erw [DirectSum.lmap_of, DirectSum.lmap_of] at he
  exact he

universe u₀ v₀ r

private theorem tensor_sheafification_naturality
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    [(J.W.inverseImage (PresheafOfModules.toPresheaf.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).IsMonoidal] :
    let := monoidalCategory R
    ∀ (A B X Y : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (f : A ⟶ B) (g : X ⟶ Y),
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification B Y).hom =
      (tensorObjIsoSheafification A X).hom ≫
        (PresheafOfModules.sheafification.{r} (𝟙 _)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  dsimp only
  intro A B X Y f g
  let S := PresheafOfModules.sheafification.{r}
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) (𝟙 _)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{r}
    (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      (𝟙 _)).counit
  have hf := c.inv.naturality f
  have hg := c.inv.naturality g
  change f ≫ c.inv.app B = c.inv.app A ≫ S.map f.val at hf
  change g ≫ c.inv.app Y = c.inv.app X ≫ S.map g.val at hg
  change (f ⊗ₘ g) ≫ ((c.inv.app B ⊗ₘ c.inv.app Y) ≫
    Functor.LaxMonoidal.μ S B.val Y.val) =
    ((c.inv.app A ⊗ₘ c.inv.app X) ≫ Functor.LaxMonoidal.μ S A.val X.val) ≫
      S.map (f.val ⊗ₘ g.val)
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Category.assoc]
  rfl

private theorem naturality_comp {D : Type*} [Category* D]
    {A B C A' B' C' : D} {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'}
    {s : A ⟶ B} {s' : A' ⟶ B'} {t : B ⟶ C} {t' : B' ⟶ C'}
    (hs : f ≫ s' = s ≫ g) (ht : g ≫ t' = t ≫ h) :
    f ≫ (s' ≫ t') = (s ≫ t) ≫ h := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

private theorem naturality_inv {D : Type*} [Category* D]
    {A B A' B' : D} (i : A ≅ B) (j : A' ≅ B')
    {f : A ⟶ A'} {g : B ⟶ B'} (h : f ≫ j.hom = i.hom ≫ g) :
    g ≫ j.inv = i.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem extension_tensor_natural
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (R : Sheaf J CommRingCat.{max u v w}) (U : C) :
    let := isMonoidal_W_independentCoefficients R
    let : HasSheafify (J.over U) AddCommGrpCat.{max u v w} :=
      hasSheafify_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
      wEqualsLocallyBijective_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
    let := isMonoidal_W_independentCoefficients (R.over U)
    let := monoidalCategory R
    let : MonoidalCategory (SheafOfModules.{max u v w}
      (((sheafCompose J
        (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).over U)) :=
      monoidalCategory (R.over U)
    let A := (sheafCompose J
      (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R
    let L := localizedSystemExtension.{u, v, w} R U
    let V := localizedSystemRestriction.{u, v, w} R U
    ∃ e : ∀ (G : SheafOfModules.{max u v w} (A.over U))
      (F : SheafOfModules.{max u v w} A), L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F,
      ∀ (G H : SheafOfModules.{max u v w} (A.over U))
        (F E : SheafOfModules.{max u v w} A) (a : G ⟶ H) (b : F ⟶ E),
        L.map (a ⊗ₘ V.map b) ≫ (e H E).hom =
          (e G F).hom ≫ (L.map a ⊗ₘ b) := by
  let := isMonoidal_W_independentCoefficients R
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v w} :=
    hasSheafify_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    wEqualsLocallyBijective_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
  let := isMonoidal_W_independentCoefficients (R.over U)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let A := (sheafCompose J
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R
  let : MonoidalCategory (SheafOfModules.{max u v w} (A.over U)) :=
    monoidalCategory (R.over U)
  let L := localizedSystemExtension.{u, v, w} R U
  let V := localizedSystemRestriction.{u, v, w} R U
  obtain ⟨e⟩ := ringedSlice_extension_tensor.{u, max u v w, v} J R U
  refine ⟨fun G F ↦ L.mapIso (tensorObjIsoSheafification (R := R.over U) G (V.obj F)) ≪≫
    e.app (G, F) ≪≫ (tensorObjIsoSheafification (R := R) (L.obj G) F).symm, ?_⟩
  intro G H F E a b
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have h₁ := congrArg L.map (tensor_sheafification_naturality (R.over U)
    G H (V.obj F) (V.obj E) a (V.map b))
  have h₂ := e.hom.naturality (X := (G, F)) (Y := (H, E)) (a, b)
  have h₃ := tensor_sheafification_naturality R (L.obj G) (L.obj H) F E (L.map a) b
  simp only [Functor.map_comp] at h₁
  simp only [Functor.comp_map, Functor.prod_map, MonoidalCategory.tensor_map] at h₂
  exact naturality_comp h₁ (naturality_comp h₂
    (naturality_inv (tensorObjIsoSheafification (R := R) (L.obj G) F)
      (tensorObjIsoSheafification (R := R) (L.obj H) E) h₃))

private theorem tensor_acyclic_of_extension
    {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
    [MonoidalCategory D] [MonoidalCategory E]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X : D, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [(curriedTensor E).PreservesZeroMorphisms]
    [∀ X : E, ((curriedTensor E).obj X).PreservesZeroMorphisms]
    [HasCoproducts.{0} D] [HasCoproducts.{0} E]
    (L : D ⥤ E) (V : E ⥤ D) [L.Additive] [V.PreservesZeroMorphisms]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.Faithful] [PreservesColimitsOfSize.{0, 0} L]
    (e : ∀ G : D, ∀ F : E, L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F)
    (he : ∀ (G H : D) (F E : E) (a : G ⟶ H) (b : F ⟶ E),
      L.map (a ⊗ₘ V.map b) ≫ (e H E).hom =
        (e G F).hom ≫ (L.map a ⊗ₘ b))
    (G : CochainComplex D ℤ) (K : CochainComplex E ℤ)
    (ht : (CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (.up ℤ)).obj G) K (curriedTensor E)).Acyclic) :
    (CochainComplex.mapBifunctor G ((V.mapHomologicalComplex (.up ℤ)).obj K)
      (curriedTensor D)).Acyclic := by
  classical
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj G).obj
    (VC.obj K)
  have : L.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso L T (.up ℤ)).symm
  let f :
      (((L.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (LC.obj G)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ e (G.X p) (K.X q)) (by
          intro q q' hq
          change (e (G.X p) (K.X q)).hom ≫
            whiskerLeft (L.obj (G.X p)) (K.d q q') =
            L.map (whiskerLeft (G.X p) (V.map (K.d q q'))) ≫
              (e (G.X p) (K.X q')).hom
          have hh := he (G.X p) (G.X p) (K.X q) (K.X q') (𝟙 _) (K.d q q')
          rw [L.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (G.X p) (K.X q)).hom ≫
          whiskerRight (L.map (G.d p p')) (K.X q) =
          L.map (whiskerRight (G.d p p') (V.obj (K.X q))) ≫
            (e (G.X p') (K.X q)).hom
        have hh := he (G.X p) (G.X p') (K.X q) (K.X q) (G.d p p') (𝟙 _)
        rw [V.map_id, tensorHom_id, tensorHom_id] at hh
        exact hh.symm)
  intro i
  apply ((CochainComplex.mapBifunctor G (VC.obj K) (curriedTensor _)).sc i
    |>.exact_map_iff_of_faithful L).mp
  exact (ht i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)).symm

/-- Restriction to an arbitrary object of a ringed site is exact and preserves
K-flatness of possibly unbounded complexes, without flatness of their terms.
Source: Stacks Project, Cohomology on Sites, Tag 0E8K, lemma-restriction-K-flat;
Modules on Sites, Tags 03DJ, 0E8G and 0E8I
(auxiliary; not a blueprint node).

Proof plan:
1. Use lem-pur-site-restriction-module-adjunction-exact for exact restriction
and the exact extension left adjoint L = j_!. The restriction here is literally
localizedSystemRestriction, hence overFunctor on J.over U with ring R.over U.
2. Given an acyclic complex G on the slice, exactness of L preserves
exactness of each consecutive triple. Thus LG is acyclic. K-flatness of K makes
Tot(LG tensor K) acyclic, using
 def-pc-acyclic-complex-modules and def-pc-kflat-complex.
3. The extension adjunction gives Hom(L(directSum G_i), H) =
product_i Hom(G_i, j^*H) = product_i Hom(LG_i, H), naturally in H.
The coproduct universal property therefore identifies L of a direct sum with
the direct sum of the extensions. The diagonal subsets of Z squared indexing
 def-pc-tensor-complex-sheaves are small in the coefficient universe.
4. Apply lem-weil-pbc-ringed-slice-extension-tensor in every bidegree and the
coproduct comparison of step 3. This gives L Tot(G tensor K|U) isomorphic to
Tot(LG tensor K). Naturality in G identifies the first differential components;
naturality in K identifies the second. Additivity of L preserves their sum and
the coefficient (-1)^p. Thus this is an isomorphism of the signed total complexes,
including when both complexes are unbounded.
5. Extension is faithful: equality after sheafification gives local equality
on each direct-sum summand; projection and sheaf separatedness give equality
of the original maps. Exact faithful functors reflect exactness. Apply this
to every consecutive triple of Tot(G tensor K|U). Its extension is acyclic
by steps 2 and 4, so it is itself acyclic. Quantifying over all acyclic G is
precisely K-flatness on the slice.
No enough-points, subterminal-object, boundedness or termwise-flatness hypothesis
is used. -/
theorem ringedSite_restriction_exact_kflat
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v w}) (U : C) :
    PreservesFiniteLimits (localizedSystemRestriction.{u, v, w} R U) ∧
    PreservesFiniteColimits (localizedSystemRestriction.{u, v, w} R U) ∧
    ∀ K : CochainComplex (SheafOfModules.{max u v w}
      ((sheafCompose J
        (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R) K →
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U)
        (((localizedSystemRestriction.{u, v, w} R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  let : HasSheafify J AddCommGrpCat.{max u v w} :=
    hasSheafify_coefficientUniverse.{u, v, max u v w} (J := J)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    wEqualsLocallyBijective_coefficientUniverse.{u, v, max u v w} (J := J)
  have h := localizedSystemExact.{u, v, w} (J := J) R U
  refine ⟨h.2.2.2.2.1, h.2.2.2.2.2, ?_⟩
  classical
  let := isMonoidal_W_independentCoefficients R
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v w} :=
    hasSheafify_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    wEqualsLocallyBijective_coefficientUniverse.{max u v, v, max u v w} (J := J.over U)
  let := isMonoidal_W_independentCoefficients (R.over U)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let : MonoidalCategory (SheafOfModules.{max u v w}
      (((sheafCompose J
        (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R).over U)) :=
    monoidalCategory (R.over U)
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients (R.over U)
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (R.over U)
  let A := (sheafCompose J
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R
  let : (curriedTensor (SheafOfModules.{max u v w} (A.over U))).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_independentCoefficients (R.over U)
  let : ∀ X : SheafOfModules.{max u v w} (A.over U),
      ((curriedTensor (SheafOfModules.{max u v w} (A.over U))).obj X).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (R.over U)
  let L := localizedSystemExtension.{u, v, w} R U
  let V := localizedSystemRestriction.{u, v, w} R U
  have : L.Additive := h.1
  have : PreservesFiniteLimits L := h.2.1
  have : PreservesFiniteColimits L := h.2.2.1
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  let : L.Faithful := ringedSliceExtension_faithful.{u, v, w} J A U
  let adj := localizedSystemAdjunction.{u, v, w} R U
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  obtain ⟨e, he⟩ := extension_tensor_natural.{u, v, w} J R U
  intro K hK G hG
  have hLG : (LC.obj G).Acyclic := by
    intro i
    exact (hG i).map L
  have ht := hK (LC.obj G) hLG
  exact tensor_acyclic_of_extension L V e he G K ht

end SheafOfModules
