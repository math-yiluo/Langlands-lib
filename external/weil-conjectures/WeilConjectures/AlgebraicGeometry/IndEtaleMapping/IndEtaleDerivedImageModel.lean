/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # The direct-image part of affine ind-etale continuity

The complex diagram here lives on the fixed small etale site of the base. Its
normalization uses the actual derived inverse-image/direct-image adjunction.
Source: Bhatt--Scholze 6.3.16 and Stacks 0GIU
(blueprint: lem-per-ind-etale-derived-image-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (M : DerivedCategoryModule A X)

/-- The actual derived direct image of the pullback of the coefficient complex.
Source: Stacks 0GIU (blueprint: lem-per-ind-etale-derived-image-model). -/
def imageValue (T : Over X) : DerivedCategoryModule A X :=
  ((lowerStar (ModuleCat.{u + 1} A) T.hom).rightDerivedFunctor).obj
    ((ExternalRHom.pull A T.hom).obj M)

/-- The transition is adjoint to pullback of the earlier counit. The two composition
isomorphisms identify iterated inverse images with the specified inverse image.
Source: Stacks 0EYM and Bhatt--Scholze 6.3.16
(blueprint: lem-per-ind-etale-derived-image-model). -/
def imagePullback {T S : Over X} (f : T ⟶ S) :
    imageValue A M S ⟶ imageValue A M T :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom).homEquiv _ _
    (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app (imageValue A M S)) ≫
      (ExternalRHom.pull A f.left).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) S.hom).counit.app
          ((ExternalRHom.pull A S.hom).obj M)) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).inv.app M)

/-- The canonical comparison of the two left adjoints whose right adjoints
compute global Hom on X and on T.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction). -/
def imageTensorIso (K : DerivedCategoryModule A X) (T : Over X) :
    ExternalRHom.constant A T.left ⋙
        tensorLeft ((ExternalRHom.pull A T.hom).obj K) ≅
      (ExternalRHom.constant A X ⋙ tensorLeft K) ⋙ ExternalRHom.pull A T.hom := by
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} A) T.hom
  exact Functor.isoWhiskerRight (ExternalRHom.constantPullbackIso A T.hom) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorLeft (ExternalRHom.pull A T.hom) K) ≪≫
    (Functor.associator _ _ _).symm

/-- Global Hom adjunction for the direct image, constructed by conjugating the
canonical monoidal and constant-pullback comparisons. In particular no witness
of an existence theorem is used to define this isomorphism.
Source: Stacks 08JA (blueprint: lem-per-ind-etale-derived-image-hom-adjunction). -/
def imageHomIso (K : DerivedCategoryModule A X) (T : Over X) :
    ((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T) ≅
      ((ExternalRHom.globalHom A T.left).obj
        (op ((ExternalRHom.pull A T.hom).obj K))).obj
          ((ExternalRHom.pull A T.hom).obj M) :=
  (conjugateIsoEquiv
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T)).app ((ExternalRHom.pull A T.hom).obj M)

/-- The derived direct image of a bounded-below pullback stays bounded below:
inverse image is exact and the total right derived functor is left t-exact.
Source: Stacks 0EYM, proof (blueprint: lem-per-ind-etale-derived-image-model). -/
theorem isGE_imageValue (T : Over X) (a : ℤ) [M.IsGE a] : (imageValue A M T).IsGE a := by
  have := (upperStar (ModuleCat.{u + 1} A) T.hom).isGE_mapDerivedCategory_obj M a
  have hK : ((ExternalRHom.pull A T.hom).obj M).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) T.hom).app M).symm a
  let F := lowerStar (ModuleCat.{u + 1} A) T.hom
  let K' : DerivedCategory.Plus (Sheaf T.left.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(ExternalRHom.pull A T.hom).obj M, ⟨a, hK⟩⟩
  have : K'.IsGE a := (K'.isGE_ι_obj_iff a).1 hK
  refine (DerivedCategory.isGE_iff _ a).2 fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K' a hq).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K')).symm

/-- **Strict models of the derived direct images of pullbacks** (missing input).
For any small diagram `E : J ⥤ Over X` of `X`-schemes and any bounded-below `M`, the
derived diagram `j ↦ R(g_j)_* L(g_j)^* M` with transition maps `imagePullback` admits a
strict model: a functor `Jᵒᵖ ⥤ CochainComplex` whose image in the derived category is
identified with it, compatibly with all transition maps.

Source: Stacks 0EYM/0GIU, proofs, and Bhatt--Scholze 6.3.16, proof: compute the direct
images by functorial `g_*`-acyclic (Godement, resp. K-injective) resolutions of the
pulled-back complexes, which are strictly compatible with the inverse-image composition
isomorphisms; the transitions are the adjunction units.
This is a missing input from the chapter on derived inverse and direct images: the project
has the derived adjunctions `Lg^* ⊣ Rg_*` and their coherence, but no strict functorial
models of `Rg_* Lg^*` along diagrams of schemes. -/
theorem exists_imageValue_strictModel (hM : ∃ a : ℤ, M.IsGE a)
    {J : Type (u + 1)} [SmallCategory J] (E : J ⥤ Over X) :
    ∃ (F : Jᵒᵖ ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (e : ∀ j : J, DerivedCategory.Q.obj (F.obj (op j)) ≅ imageValue A M (E.obj j)),
      ∀ {j k : J} (f : j ⟶ k),
        DerivedCategory.Q.map (F.map f.op) ≫ (e j).hom =
          (e k).hom ≫ imagePullback A M (E.map f) := by
  sorry

/-- **Continuity of the higher direct images of pullbacks along affine limits**
(missing input). Let `T = lim T_i` be a cofiltered limit of affine `X`-schemes with
affine transition maps, `X` affine, and `M` bounded below. Then for every `n` the
canonical maps `Hⁿ(imageValue T_i) ⟶ Hⁿ(imageValue T)` (the cohomology of
`imagePullback`) exhibit `Hⁿ(R g_* g^* M)` as the filtered colimit of the
`Hⁿ(R (g_i)_* g_i^* M)`. The colimit diagram is presented by any strict diagram `G`
identified with these cohomology sheaves compatibly with the transition maps.

Source: Stacks 0GIU (and 09YQ, 0EYM): on an affine étale `V → X`, the presheaf
`V ↦ Hⁿ(V ×_X T, M)` is the colimit of `V ↦ Hⁿ(V ×_X T_i, M)`, and the cohomology
sheaves are the sheafifications of these presheaves.
This is a missing input from the chapter on cohomology and limits: the project has the
absolute statement for global sections with abelian coefficients
(`AlgebraicGeometry.derivedEtaleCohomology_limit`, Stacks 0GIT), but not the relative,
sheaf-level version over a fixed base with module coefficients. -/
theorem isColimit_homology_imageValue [IsAffine X]
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over X) (c : Cone D)
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hM : ∃ a : ℤ, M.IsGE a) (n : ℤ)
    (G : Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (e : ∀ i : I, G.obj (op i) ≅
      (DerivedCategory.homologyFunctor _ n).obj (imageValue A M (D.obj i)))
    (he : ∀ {i j : I} (f : i ⟶ j), G.map f.op ≫ (e i).hom =
      (e j).hom ≫ (DerivedCategory.homologyFunctor _ n).map (imagePullback A M (D.map f)))
    (t : Cocone G)
    (et : t.pt ≅ (DerivedCategory.homologyFunctor _ n).obj (imageValue A M c.pt))
    (ht : ∀ i : I, t.ι.app (op i) ≫ et.hom =
      (e i).hom ≫ (DerivedCategory.homologyFunctor _ n).map
        (imagePullback A M (c.π.app i))) :
    Nonempty (IsColimit t) := by
  sorry

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

/-- A strict complex realization of the derived direct-image diagram and cocone.
No continuity assertion is part of this data.
Source: Bhatt--Scholze 6.3.16, proof, direct-image construction
(blueprint: lem-per-ind-etale-derived-image-model). -/
structure DerivedImageModel where
  diagram : Iᵒᵖ ⥤ CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ
  cocone : Cocone diagram
  stage : ∀ i : I, DerivedCategory.Q.obj (diagram.obj (op i)) ≅ imageValue A M (D.obj i)
  apex : DerivedCategory.Q.obj cocone.pt ≅ imageValue A M c.pt
  transition : ∀ {i j : I} (f : i ⟶ j),
    DerivedCategory.Q.map (diagram.map f.op) ≫ (stage i).hom =
      (stage j).hom ≫ imagePullback A M (D.map f)
  leg : ∀ i : I,
    DerivedCategory.Q.map (cocone.ι.app (op i)) ≫ apex.hom =
      (stage i).hom ≫ imagePullback A M (c.π.app i)

-- The hypotheses `hetale` and `hfp` are part of the blueprint statement but are not needed
-- for the direct-image part: Stacks 0GIU holds for affine transition maps.
set_option linter.unusedVariables false in
/-- The direct-image diagram has uniformly bounded-below strict representatives,
and its actual cocone comparison is a derived isomorphism. This concerns only M;
it makes no assertion about constructible global Hom.

Source: Stacks 0GIU, Bhatt--Scholze 6.3.16, proof, direct-image continuity
(blueprint: lem-per-ind-etale-derived-image-model).

Proof: choose a bounded-below injective representative of M. At an etale stage
its exact inverse image remains injective, since etale extension by zero is an
exact left adjoint. Apply direct image to obtain the stage complexes. Their
transition maps are the adjunction units, with the inverse-image composition
identifications. At the limit resolve the pulled-back complex by a bounded-below
injective complex with the same lower bound, and use the resolution map for the
cocone legs. The unit and counit identities give the displayed normalizations.
Stacks 0GIU gives the colimit isomorphism on every cohomology sheaf; forgetting
coefficient modules preserves the colimit and reflects the isomorphism. Exactness
of filtered colimits identifies these cohomology maps with those of the complex
cocone comparison, so localization inverts it. Construct the strict
representatives on I itself. For the cohomology continuity argument only, take
a directed final index in the opposite of I and adjoin X as an initial stage.
Finality identifies the cohomology cocone comparisons; no strict diagram is
transported backwards along a final functor.
-/
theorem derivedImageModel_exists_continuous [Finite A] [IsAffine X]
    [IsNoetherian X] [IsCofiltered I]
    (hc : IsLimit ((Over.forget X).mapCone c))
    (haffine : ∀ i : I, IsAffine (D.obj i).left)
    (hetale : ∀ i : I, Etale (D.obj i).hom)
    (hfp : ∀ i : I, LocallyOfFinitePresentation (D.obj i).hom)
    (htransition : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left)
    (hM : ∃ a : ℤ, M.IsGE a) :
    ∃ (N : DerivedImageModel A M D c) (a : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.diagram.obj (op i))).IsGE a) ∧
      IsIso (DerivedCategory.Q.map (colimit.desc N.diagram N.cocone)) := by
  classical
  obtain ⟨a, ha⟩ := hM
  let E : WithInitial I ⥤ Over X :=
    WithInitial.lift D (fun i ↦ c.π.app i) (fun _ _ f ↦ c.w f)
  obtain ⟨F, e, he⟩ := exists_imageValue_strictModel A M ⟨a, ha⟩ E
  let N : DerivedImageModel A M D c :=
    { diagram := WithInitial.incl.op ⋙ F
      cocone :=
        { pt := F.obj (op WithInitial.star)
          ι :=
            { app := fun i ↦ F.map (WithInitial.starInitial.to (WithInitial.of i.unop)).op
              naturality := fun i j f ↦ by
                dsimp
                rw [Category.comp_id, ← F.map_comp, ← op_comp]
                congr 2 } }
      stage := fun i ↦ e (WithInitial.of i)
      apex := e WithInitial.star
      transition := fun f ↦ he (WithInitial.incl.map f)
      leg := fun i ↦ he (WithInitial.starInitial.to (WithInitial.of i)) }
  refine ⟨N, a, fun i ↦ ?_, ?_⟩
  · have := isGE_imageValue A M (D.obj i) a
    exact DerivedCategory.TStructure.t.isGE_of_iso (N.stage i).symm a
  · let S := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let H := HomologicalComplex.homologyFunctor S (ComplexShape.up ℤ)
    let Hd := DerivedCategory.homologyFunctor S
    let φ := DerivedCategory.homologyFunctorFactors S
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso, quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have hP : IsColimit ((H n).mapCocone (colimit.cocone N.diagram)) :=
      isColimitOfPreserves (H n) (colimit.isColimit _)
    have he {i j : I} (f : i ⟶ j) : (N.diagram ⋙ H n).map f.op ≫
        (((φ n).app _).symm ≪≫ (Hd n).mapIso (N.stage i)).hom =
        (((φ n).app _).symm ≪≫ (Hd n).mapIso (N.stage j)).hom ≫
          (Hd n).map (imagePullback A M (D.map f)) := by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.comp_map]
      rw [Category.assoc, ← Functor.map_comp, ← N.transition f, Functor.map_comp,
        ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) ((φ n).inv.naturality _)
    have ht (i : I) : ((H n).mapCocone N.cocone).ι.app (op i) ≫
        (((φ n).app _).symm ≪≫ (Hd n).mapIso N.apex).hom =
        (((φ n).app _).symm ≪≫ (Hd n).mapIso (N.stage i)).hom ≫
          (Hd n).map (imagePullback A M (c.π.app i)) := by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapCocone_ι_app]
      rw [Category.assoc, ← Functor.map_comp, ← N.leg i, Functor.map_comp,
        ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) ((φ n).inv.naturality _)
    obtain ⟨hT⟩ := isColimit_homology_imageValue A M D c hc haffine htransition ⟨a, ha⟩ n
      (N.diagram ⋙ H n) (fun i ↦ ((φ n).app _).symm ≪≫ (Hd n).mapIso (N.stage i)) he
      ((H n).mapCocone N.cocone) (((φ n).app _).symm ≪≫ (Hd n).mapIso N.apex) ht
    have : HomologicalComplex.homologyMap (colimit.desc N.diagram N.cocone) n =
        (hP.coconePointUniqueUpToIso hT).hom := hP.hom_ext fun j ↦ by
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
      simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
      rw [← HomologicalComplex.homologyFunctor_map, ← Functor.map_comp, colimit.ι_desc]
    rw [this]
    infer_instance

end AlgebraicGeometry.Etale.IndEtaleMapping
