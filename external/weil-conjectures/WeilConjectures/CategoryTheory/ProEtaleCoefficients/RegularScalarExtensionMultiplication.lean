/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-!
# Regular scalar extension and multiplication

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-change-of-scalars/`,
`def-sfb-modobj-extension.md` and its proof, regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)

/-- Abelian sheafification on the essentially small site.
Source: Stacks 00WH and the sheafification in `sk-def-sfb-sheaf-tensor`
(blueprint: lem-sfb-regular-scalar-extension-multiplication).
Proof: replace the site by its small model in the coefficient universe, apply
`GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian`, and transport back. -/
instance sfbRegularAb_hasSheafify : HasSheafify J AddCommGrpCat.{w} := by
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J)
      AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite J AddCommGrpCat.{w}

/-- The specified sheafified tensor, specialized to abelian sheaves.
Source: blueprint `sk-def-sfb-sheaf-tensor`, as used in the regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbMonoidal : MonoidalCategory (Sheaf J Ab.{w}) :=
  (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal

/-- The symmetry of the specified tensor on abelian sheaves.
Source: blueprint `sk-def-sfb-sheaf-tensor`, regular-module specialization
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbSymmetric : SymmetricCategory (Sheaf J Ab.{w}) :=
  (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric

/-- Left tensor preserves the small colimits used for balancing.
Source: blueprint `sk-def-sfb-sheaf-tensor`, clause 2
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbTensorLeft (F : Sheaf J Ab.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
  ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 F).1

/-- Right tensor preserves the small colimits used for balancing.
Source: blueprint `sk-def-sfb-sheaf-tensor`, clause 2
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable instance sfbRegularAbTensorRight (F : Sheaf J Ab.{w}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
  ((sfbSheafTensor_properties (A := Ab.{w}) J).2.2 F).2.1

/-- The canonical presheaf-to-sheaf tensor generator map.
Source: blueprint `def-sfb-modobj-extension`, local generator interpretation
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable def sfbRegularTensorGenerators (F G : Sheaf J Ab.{w}) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  toSheafify J (F.obj ⊗ G.obj) ≫ (sfbSheafTensor_comparison J F G).inv.hom

/-- Evaluate a map from the tensor unit as a compatible family of sections.
The integer 1 first enters the sheafified constant integer sheaf by its actual unit map.
Source: blueprint `def-sfb-modobj-extension`, global-section interpretation
(blueprint: lem-sfb-regular-scalar-extension-multiplication). -/
noncomputable def sfbRegularSection (F : Sheaf J Ab.{w})
    (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ F) (U : Cᵒᵖ) : F.obj.obj U :=
  t.hom.app U
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (𝟙_ Ab.{w}))).app U (ULift.up (1 : ℤ)))

private noncomputable def regularIso
    (R S : Sheaf J Ab.{w}) [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S :=
  Mod.isoMk
    { hom := Bimod.RightUnitorBimod.hom (Bimod.ofMonHom φ)
      inv := Bimod.RightUnitorBimod.inv (Bimod.ofMonHom φ)
      hom_inv_id := Bimod.RightUnitorBimod.hom_inv_id (Bimod.ofMonHom φ)
      inv_hom_id := Bimod.RightUnitorBimod.inv_hom_id (Bimod.ofMonHom φ) }
    (Bimod.RightUnitorBimod.hom_left_act_hom' (Bimod.ofMonHom φ))

private theorem regularIso_π
    (R S : Sheaf J Ab.{w}) [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] :
    Mod.extendπ φ (Mod.regular R) ≫ (regularIso J R S φ).hom.hom = S ◁ φ ≫ μ[S] := by
  apply coequalizer.π_desc

private theorem regularIso_inv
    (R S : Sheaf J Ab.{w}) [MonObj R] [MonObj S]
    [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] :
    (regularIso J R S φ).inv.hom =
      (ρ_ S).inv ≫ S ◁ η[R] ≫ Mod.extendπ φ (Mod.regular R) := rfl

private theorem regularLift_eq
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R]
    (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ R) :
    (Mod.regularLift (Mod.regular R) t).hom = (λ_ R).inv ≫ t ▷ R ≫ μ[R] := by
  change (ρ_ R).inv ≫ R ◁ t ≫ μ[R] = _
  calc
    _ = (ρ_ R).inv ≫ R ◁ t ≫ (β_ R R).hom ≫ μ[R] := by
      rw [IsCommMonObj.mul_comm]
    _ = _ := by
      rw [BraidedCategory.braiding_naturality_right_assoc,
        ← Category.assoc, rightUnitor_inv_braiding]

private noncomputable instance regularSheafifyMonoidal :
    (presheafToSheaf J Ab.{w}).Monoidal :=
  (sfbSheafTensorStructure (A := Ab.{w}) J).sheafificationMonoidal

private noncomputable instance regularUnderlyingLax :
    (sheafToPresheaf J Ab.{w}).LaxMonoidal :=
  (sheafificationAdjunction J Ab.{w}).rightAdjointLaxMonoidal

private theorem generators_eq (F G : Sheaf J Ab.{w}) :
    sfbRegularTensorGenerators J F G =
      Functor.LaxMonoidal.μ (sheafToPresheaf J Ab.{w}) F G := by
  rfl

private theorem generators_natural
    {F F' G G' : Sheaf J Ab.{w}} (f : F ⟶ F') (g : G ⟶ G') :
    (f.hom ⊗ₘ g.hom) ≫ sfbRegularTensorGenerators J F' G' =
      sfbRegularTensorGenerators J F G ≫ (f ⊗ₘ g).hom := by
  with_unfolding_all
    simpa only [generators_eq, ObjectProperty.ι_obj, ObjectProperty.ι_map] using
      Functor.LaxMonoidal.μ_natural (sheafToPresheaf J Ab.{w}) f g

private theorem generators_map
    {F F' G G' : Sheaf J Ab.{w}} (f : F ⟶ F') (g : G ⟶ G')
    (U : Cᵒᵖ) (a : F.obj.obj U) (b : G.obj.obj U) :
    (f ⊗ₘ g).hom.app U ((sfbRegularTensorGenerators J F G).app U
        (TensorProduct.tmul ℤ a b)) =
      (sfbRegularTensorGenerators J F' G').app U
        (TensorProduct.tmul ℤ (f.hom.app U a) (g.hom.app U b)) := by
  exact (congrArg (fun k ↦ k.app U (TensorProduct.tmul ℤ a b))
    (generators_natural J f g)).symm

private theorem left_section (F G : Sheaf J Ab.{w})
    (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ G) (U : Cᵒᵖ) (a : F.obj.obj U) :
    ((λ_ F).inv ≫ t ▷ F).hom.app U a =
      (sfbRegularTensorGenerators J G F).app U
        (TensorProduct.tmul ℤ (sfbRegularSection J G t U) a) := by
  with_unfolding_all
    have h : ((λ_ F).inv ≫ t ▷ F).hom =
        (λ_ F.obj).inv ≫
          ((Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{w}) ≫ t.hom) ▷ F.obj) ≫
          sfbRegularTensorGenerators J G F := by
      rw [generators_eq]
      change (sheafToPresheaf J Ab.{w}).map ((λ_ F).inv ≫ t ▷ F) = _
      rw [Functor.map_comp, ← Functor.LaxMonoidal.left_unitality_inv,
        Category.assoc, Category.assoc, ← Functor.LaxMonoidal.μ_natural_left]
      simp only [comp_whiskerRight, Category.assoc]
      rfl
    exact congrArg (fun f ↦ f.app U a) h

private theorem right_section (F G : Sheaf J Ab.{w})
    (t : 𝟙_ (Sheaf J Ab.{w}) ⟶ G) (U : Cᵒᵖ) (a : F.obj.obj U) :
    ((ρ_ F).inv ≫ F ◁ t).hom.app U a =
      (sfbRegularTensorGenerators J F G).app U
        (TensorProduct.tmul ℤ a (sfbRegularSection J G t U)) := by
  with_unfolding_all
    have h : ((ρ_ F).inv ≫ F ◁ t).hom =
        (ρ_ F.obj).inv ≫
          F.obj ◁ (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{w}) ≫ t.hom) ≫
          sfbRegularTensorGenerators J F G := by
      rw [generators_eq]
      change (sheafToPresheaf J Ab.{w}).map ((ρ_ F).inv ≫ F ◁ t) = _
      rw [Functor.map_comp, ← Functor.LaxMonoidal.right_unitality_inv,
        Category.assoc, Category.assoc, ← Functor.LaxMonoidal.μ_natural_right]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rfl
    exact congrArg (fun f ↦ f.app U a) h

/-- Normalization of extension on regular modules, including multiplication by every
compatible global section. Source: blueprint `def-sfb-modobj-extension.md` and its proof,
regular-module specialization (blueprint: lem-sfb-regular-scalar-extension-multiplication).

Proof, following the node:
1. Abelian sheaf coequalizers are sheafifications of the objectwise cokernels of the
parallel difference. Their projections are epimorphisms; so are their tensors, since
both tensor functors preserve colimits (`sk-def-sfb-sheaf-tensor`,
`def-weil-pbc-sheafification`, `def-weil-pbc-category-colimit`).
2. The right R-action on S is S tensor phi followed by multiplication. Its unit,
associativity and compatibility with the left S-action follow from the ring-object
axioms. The balancing pair is exactly that of `def-sfb-modobj-extension` on regular R.
3. Apply `lem-sfb-mixed-bimodule-right-unitor` to this S-R-bimodule. Its forward map
composed with the balancing projection is the right action. Its inverse inserts the
unit of R. Uniqueness of the coequalizer factorization identifies this with the specified
extension object and its first-factor S-action, even if coequalizer choices differ.
4. Precompose with the presheaf tensor generators of
`lem-sfb-braided-sheaf-tensor-generators`. The forward formula becomes b phi(a).
The right-unitor comparison of `lem-sfb-sheaf-tensor-unit-comparison`, with
`det-def-sfb-sheaf-tensor-structure`, identifies the inverse with b tensor 1.
These tests assert equalities of sheaf maps, not pure-tensor generation of sections.
5. The left-unitor comparison identifies `extendUnitHom` with a mapped to 1 tensor a.
The left unit law of S and the multiplication compatibility of phi give q iota = phi.
6. Maps from the sheafified constant integers are compatible families, by the unit Hom
bijection in `lem-sfb-braided-sheaf-tensor-generators`. Multiplication by such a map t
is left-unitor inverse, followed by t tensor R and multiplication. Its section formula
is multiplication by t_U. Associativity and commutativity of R give R-linearity;
the same argument for S gives S-linearity for t followed by phi.
7. The induced map under extension is characterized after the balancing projection by
S tensor m_t. Precomposing the desired conjugation with that projection reduces it to
r(S tensor m_t) = m_phi(t) r. This follows from phi preserving multiplication and the
S-linearity in step 6. Cancel the epimorphic projection. No flatness, invertibility,
or final object of the site is used.
-/
theorem sfbRegularScalarExtensionMultiplication
    (R S : Sheaf J Ab.{w}) [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] :
    ∃! q : (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S,
      Mod.extendπ φ (Mod.regular R) ≫ q.hom.hom = S ◁ φ ≫ μ[S] ∧
      q.inv.hom = (ρ_ S).inv ≫ S ◁ η[R] ≫ Mod.extendπ φ (Mod.regular R) ∧
      Mod.extendUnitHom φ (Mod.regular R) ≫ q.hom.hom = φ ∧
      (∀ (U : Cᵒᵖ) (b : S.obj.obj U) (a : R.obj.obj U),
        q.hom.hom.hom.app U
            ((Mod.extendπ φ (Mod.regular R)).hom.app U
              ((sfbRegularTensorGenerators J S R).app U (TensorProduct.tmul ℤ b a))) =
          μ[S].hom.app U ((sfbRegularTensorGenerators J S S).app U
            (TensorProduct.tmul ℤ b (φ.hom.app U a)))) ∧
      (∀ (U : Cᵒᵖ) (b : S.obj.obj U),
        q.inv.hom.hom.app U b =
          (Mod.extendπ φ (Mod.regular R)).hom.app U
            ((sfbRegularTensorGenerators J S R).app U
              (TensorProduct.tmul ℤ b (sfbRegularSection J R η[R] U)))) ∧
      (∀ (U : Cᵒᵖ) (a : R.obj.obj U),
        (Mod.extendUnitHom φ (Mod.regular R)).hom.app U a =
          (Mod.extendπ φ (Mod.regular R)).hom.app U
            ((sfbRegularTensorGenerators J S R).app U
              (TensorProduct.tmul ℤ (sfbRegularSection J S η[S] U) a))) ∧
      ∀ t : 𝟙_ (Sheaf J Ab.{w}) ⟶ R,
        ∃ mR : Mod.regular R ⟶ Mod.regular R,
        ∃ mS : Mod.regular S ⟶ Mod.regular S,
          mR.hom = (λ_ R).inv ≫ t ▷ R ≫ μ[R] ∧
          mS.hom = (λ_ S).inv ≫ (t ≫ φ) ▷ S ≫ μ[S] ∧
          (∀ (U : Cᵒᵖ) (a : R.obj.obj U),
            mR.hom.hom.app U a =
              μ[R].hom.app U ((sfbRegularTensorGenerators J R R).app U
                (TensorProduct.tmul ℤ (sfbRegularSection J R t U) a))) ∧
          (∀ (U : Cᵒᵖ) (b : S.obj.obj U),
            mS.hom.hom.app U b =
              μ[S].hom.app U ((sfbRegularTensorGenerators J S S).app U
                (TensorProduct.tmul ℤ (φ.hom.app U (sfbRegularSection J R t U)) b))) ∧
          (Mod.extendScalars φ).map mR ≫ q.hom = q.hom ≫ mS := by
  with_unfolding_all
    let q := regularIso J R S φ
    have hq : Mod.extendπ φ (Mod.regular R) ≫ q.hom.hom = S ◁ φ ≫ μ[S] :=
      regularIso_π J R S φ
    have hi : q.inv.hom =
        (ρ_ S).inv ≫ S ◁ η[R] ≫ Mod.extendπ φ (Mod.regular R) :=
      regularIso_inv J R S φ
    refine ⟨q, ⟨hq, hi, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [Mod.extendUnitHom]
      simp only [Category.assoc]
      rw [hq]
      exact MonObj.leftUnitor_inv_one_whiskerRight_whiskerLeft_mul φ
    · intro U b a
      have h := congrArg (fun f ↦ f.hom.app U
        ((sfbRegularTensorGenerators J S R).app U (TensorProduct.tmul ℤ b a))) hq
      change q.hom.hom.hom.app U
        ((Mod.extendπ φ (Mod.regular R)).hom.app U
          ((sfbRegularTensorGenerators J S R).app U (TensorProduct.tmul ℤ b a))) =
        μ[S].hom.app U
        ((S ◁ φ).hom.app U
          ((sfbRegularTensorGenerators J S R).app U (TensorProduct.tmul ℤ b a))) at h
      rw [h]
      congr 1
      have hid : (𝟙 S : S ⟶ S).hom.app U b = b := rfl
      simpa only [id_tensorHom, hid] using generators_map J (𝟙 S) φ U b a
    · intro U b
      rw [hi]
      exact congrArg (fun x ↦ (Mod.extendπ φ (Mod.regular R)).hom.app U x)
        (right_section J S R η[R] U b)
    · intro U a
      exact congrArg (fun x ↦ (Mod.extendπ φ (Mod.regular R)).hom.app U x)
        (left_section J R S η[S] U a)
    · intro t
      let mR := Mod.regularLift (Mod.regular R) t
      let mS := Mod.regularLift (Mod.regular S) (t ≫ φ)
      have hmR : mR.hom = (λ_ R).inv ≫ t ▷ R ≫ μ[R] := regularLift_eq J R t
      have hmS : mS.hom = (λ_ S).inv ≫ (t ≫ φ) ▷ S ≫ μ[S] :=
        regularLift_eq J S (t ≫ φ)
      refine ⟨mR, mS, hmR, hmS, ?_, ?_, ?_⟩
      · intro U a
        rw [hmR]
        exact congrArg (fun x ↦ μ[R].hom.app U x) (left_section J R R t U a)
      · intro U b
        rw [hmS]
        exact congrArg (fun x ↦ μ[S].hom.app U x) (left_section J S S (t ≫ φ) U b)
      · have hm : mR.hom ≫ φ = φ ≫ mS.hom := by
          rw [hmR, hmS]
          change ((λ_ R).inv ≫ t ▷ R ≫ μ[R]) ≫ φ =
            φ ≫ (λ_ S).inv ≫ (t ≫ φ) ▷ S ≫ μ[S]
          simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_def]
          rw [← comp_whiskerRight_assoc, ← whisker_exchange_assoc,
            ← leftUnitor_inv_naturality_assoc]
        apply Mod.extendScalarsObj_hom_ext φ
        change Mod.extendπ φ (Mod.regular R) ≫
            (Mod.extendScalarsMap φ mR).hom ≫ q.hom.hom =
          Mod.extendπ φ (Mod.regular R) ≫ q.hom.hom ≫ mS.hom
        rw [Mod.extendπ_extendScalarsMap_assoc, reassoc_of% hq, hq]
        change S ◁ mR.hom ≫ S ◁ φ ≫ μ[S] = S ◁ φ ≫ μ[S] ≫ mS.hom
        rw [← whiskerLeft_comp_assoc, hm, whiskerLeft_comp_assoc]
        have hs : S ◁ mS.hom ≫ μ[S] = μ[S] ≫ mS.hom := (Mod.act_hom mS).symm
        exact congrArg (fun k : S ⊗ S ⟶ S ↦ S ◁ φ ≫ k) hs
    · intro q' h'
      apply Iso.ext
      apply Mod.hom_ext
      apply (cancel_epi (Mod.extendπ φ (Mod.regular R))).1
      exact h'.1.trans hq.symm

end CategoryTheory
