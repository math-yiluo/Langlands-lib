/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Change of rings preserves K-flat complexes with flat terms

Source: Stacks Project, Cohomology on Sites, Lemma 21.18.1, Tag 0G7E,
identity-topos coefficient-change case (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

open CategoryTheory.Limits in
private theorem restrictScalars_exact_kflat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B) :
    PreservesFiniteLimits (restrictScalars.{r} α) ∧
      PreservesFiniteColimits (restrictScalars.{r} α) := by
  let U := restrictScalars.{r} α
  have : PreservesFiniteLimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf B))
  have : PreservesFiniteColimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (toSheaf A)⟩

open CategoryTheory.Limits in
private theorem acyclic_restrictScalars_kflat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B)
    (L : CochainComplex (SheafOfModules.{r} B) ℤ) (hL : L.Acyclic) :
    (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
  have := (restrictScalars_exact_kflat α).1
  have := (restrictScalars_exact_kflat α).2
  intro i
  exact (hL i).map (restrictScalars α)

open CategoryTheory.Limits in
private theorem acyclic_of_restrictScalars_kflat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {A B : Sheaf J RingCat.{r}} (α : A ⟶ B)
    (L : CochainComplex (SheafOfModules.{r} B) ℤ)
    (hL : (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (toSheaf B)).mp
  exact (hL i).map (toSheaf A)

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)

/-- Change of rings preserves K-flatness and flatness of every term.
Source: Stacks, Tag 0G7E (auxiliary; not a blueprint node).

Proof:
1. Restriction of scalars leaves underlying abelian sheaves unchanged. Kernels are
sectionwise and cokernels are sheafified sectionwise cokernels; thus restriction preserves
and reflects exactness and acyclicity (def-pc-sheaf-restrict-scalars,
situation-conventions).
2. For an R-module M and S-module N, the balanced maps n tensor (m tensor s) maps to
sn tensor m and n tensor m maps to n tensor (m tensor 1) give inverse natural maps
U(N tensor_S (M tensor_R S)) and UN tensor_R M. Construct them on presheaf tensor
generators, then extend by monoidal sheafification. The resulting comparison is natural
in both factors (lem-pur-change-of-rings-tensor-cancellation).
3. Restrict a short exact sequence of S-modules, tensor with K.X p, and use step 2.
Exactness of tensor with K.X p and reflection of exactness prove flatness of its change
of rings (Stacks, Tag 05V4).
4. Take direct sums of step 2 over a+b=n. Restriction commutes with these sheafified
sums of finite-support tuples. The resulting isomorphism of total complexes respects
the two differential terms, including the sign (-1)^a on the second term
(def-pc-tensor-complex-sheaves).
5. If F is acyclic over S, UF is acyclic over R. K-flatness of K makes Tot(UF tensor_R K)
acyclic. Steps 4 and 1 give acyclicity of Tot(F tensor_S (K tensor_R S)), which is
K-flatness of the changed complex (def-pc-kflat-complex). Combine with step 3. -/
theorem changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (E : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (g : M ⟶ N), E.map g =
      eqToHom (h M) ≫ changeOfRingsHom φ M g ≫ eqToHom (h N).symm)
    [E.Additive]
    (hK : CochainComplex.IsKFlatIndependentCoefficients K)
    (hflat : ∀ p : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _ (monoidalCategory R) (K.X p))) :
    CochainComplex.IsKFlatIndependentCoefficients ((E.mapHomologicalComplex (.up ℤ)).obj K) ∧
      ∀ p : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _ (monoidalCategory S)
          (((E.mapHomologicalComplex (.up ℤ)).obj K).X p)) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let α := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ
  let U := restrictScalars.{r} α
  have hU := restrictScalars_exact_kflat α
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ toSheaf
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp U (toSheaf _)
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let e (M : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
      (N : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    U.mapIso (((curriedTensor _).obj M).mapIso (eqToIso (h N))) ≪≫ e₀ M N
  have he {M M' : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj S)}
      {N N' : SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (tensorHom f (E.map g)) ≫ (e M' N').hom =
        (e M N).hom ≫ tensorHom (U.map f) g := by
    have hs : tensorHom f (E.map g) ≫ whiskerLeft M' (eqToHom (h N')) =
        whiskerLeft M (eqToHom (h N)) ≫ tensorHom f (changeOfRingsHom φ N g) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp, hm, Category.assoc,
        eqToHom_trans, eqToHom_refl]
    change U.map (tensorHom f (E.map g)) ≫
        U.map (whiskerLeft M' (eqToHom (h N'))) ≫ (e₀ M' N').hom =
      U.map (whiskerLeft M (eqToHom (h N))) ≫ (e₀ M N).hom ≫ tensorHom (U.map f) g
    rw [← U.map_comp_assoc, hs, U.map_comp, Category.assoc, he₀ f g]
  constructor
  · intro F hF
    let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj K)
    have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
      have : PreservesColimitsOfShape D (U ⋙ toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
        inferInstanceAs (PreservesColimitsOfShape D (toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
      have : ReflectsColimitsOfShape D (toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
        reflectsColimitsOfShape_of_reflectsIsomorphisms
      exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
    have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
    have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
    let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
    let f :
        (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
        (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj F)).obj K :=
      HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ HomologicalComplex.Hom.isoOfComponents
          (fun j ↦ e (F.X i) (K.X j)) (by
            intro j j' hj
            change (e (F.X i) (K.X j)).hom ≫ whiskerLeft (U.obj (F.X i)) (K.d j j') =
              U.map (whiskerLeft (F.X i) (E.map (K.d j j'))) ≫
                (e (F.X i) (K.X j')).hom
            have hh := he (𝟙 (F.X i)) (K.d j j')
            change U.map (tensorHom (𝟙 (F.X i)) (E.map (K.d j j'))) ≫
                (e (F.X i) (K.X j')).hom =
              (e (F.X i) (K.X j)).hom ≫ tensorHom (U.map (𝟙 (F.X i))) (K.d j j') at hh
            rw [U.map_id, id_tensorHom, id_tensorHom] at hh
            exact hh.symm))
        (by
          intro i i' hi
          apply HomologicalComplex.Hom.ext
          funext j
          change (e (F.X i) (K.X j)).hom ≫ whiskerRight (U.map (F.d i i')) (K.X j) =
            U.map (whiskerRight (F.d i i') (E.obj (K.X j))) ≫
              (e (F.X i') (K.X j)).hom
          simpa only [E.map_id, tensorHom_id]
            using (he (F.d i i') (𝟙 (K.X j))).symm)
    have h := hK ((U.mapHomologicalComplex (.up ℤ)).obj F)
      (acyclic_restrictScalars_kflat α F hF)
    apply acyclic_of_restrictScalars_kflat α
    intro i
    exact (h i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)).symm
  · intro p
    let TR := tensorRight (K.X p)
    let TS := tensorRight (((E.mapHomologicalComplex (.up ℤ)).obj K).X p)
    have : PreservesFiniteLimits TR := (hflat p).1
    have : PreservesFiniteColimits TR := (hflat p).2
    let q : TS ⋙ U ≅ U ⋙ TR := NatIso.ofComponents (fun M ↦ e M (K.X p)) (by
      intro M N f
      change U.map (whiskerRight f (E.obj (K.X p))) ≫ (e N (K.X p)).hom =
        (e M (K.X p)).hom ≫ whiskerRight (U.map f) (K.X p)
      simpa only [E.map_id, tensorHom_id]
        using he f (𝟙 (K.X p)))
    have : PreservesFiniteLimits (U ⋙ TR) := comp_preservesFiniteLimits U TR
    have : PreservesFiniteColimits (U ⋙ TR) := comp_preservesFiniteColimits U TR
    have : PreservesFiniteLimits (TS ⋙ U) := preservesFiniteLimits_of_natIso q.symm
    have : PreservesFiniteColimits (TS ⋙ U) := preservesFiniteColimits_of_natIso q.symm
    exact ⟨preservesFiniteLimits_of_reflects_of_preserves TS U,
      preservesFiniteColimits_of_reflects_of_preserves TS U⟩

end SheafOfModules
