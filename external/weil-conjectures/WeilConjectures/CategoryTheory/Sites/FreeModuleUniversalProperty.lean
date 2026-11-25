/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Universal property of the free module on a sheaf of sets

Source: Stacks Project, Modules on Sites, Tags 04BL and 03CY
(auxiliary; not a blueprint node).

The free functor and generator map are the existing `SheafFreeModule.free` and
`SheafFreeModule.generatorRaw`; no second free object is introduced here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafFreeModule

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (B : Sheaf J CommRingCat.{w})

/-- The underlying sheaf of sets without the inverse-image interface's `ULift`.
Source: Stacks 04BL (auxiliary; not a blueprint node). -/
abbrev underlyingRaw : SheafOfModules.{w} (ring B) ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf (ring B) ⋙ sheafCompose J (forget AddCommGrpCat.{w})

/-- Restriction of a module map to the canonical generators.
Source: Stacks 04BL (auxiliary; not a blueprint node). -/
def restrictGenerators (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B))
    (h : (free B).obj E ⟶ M) : E ⟶ (underlyingRaw B).obj M :=
  generatorRaw B E ≫ (underlyingRaw B).map h

/-- Extend a sheaf map by the sectionwise linear extension and module sheafification.
This is the actual inverse of the composite of the two Mathlib Hom equivalences.
Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node). -/
def extendGenerators (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B))
    (a : E ⟶ (underlyingRaw B).obj M) : (free B).obj E ⟶ M :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  (((PresheafOfModules.freeAdjunction (ring B).obj).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj))).homEquiv E.obj M).symm
      a.hom

/-- The actual abelian-presheaf sheafification unit for the free presheaf.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def freeModuleUnit (E : Sheaf J (Type w)) :
    (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf ⟶
      ((free B).obj E).val.presheaf :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  toSheafify J (PresheafOfModules.freeObj (R := (ring B).obj) E.obj).presheaf

private def freeHomEquivRaw (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B)) :
    ((free B).obj E ⟶ M) ≃ (E.obj ⟶ ((underlyingRaw B).obj M).obj) :=
  letI := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  letI : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  letI := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  ((PresheafOfModules.freeAdjunction (ring B).obj).comp
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj))).homEquiv E.obj M

private lemma freeHomEquivRaw_apply (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B)) (h : (free B).obj E ⟶ M) :
    freeHomEquivRaw B E M h = (restrictGenerators B E M h).hom := by
  ext U e
  rfl

/-- Restriction to generators is a bijection for every module sheaf.
Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node).

Proof: form the sectionwise free presheaf. Its restrictions combine coefficients of
indices that merge, hence are semilinear and functorial (node step 1). Extend a map
from E sectionwise by the finite sum of coefficients times generator images; naturality
makes these linear maps a presheaf map (step 2). The module sheafification adjunction
factors it uniquely (step 3). The two inverse identities follow because linear maps
agreeing on basis vectors agree, and the sheafification factorization is unique (step 4).
These use def-weil-pbc-free-module and def-weil-presheaf-modules-sheafification. -/
theorem freeModule_restrict_bijective (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B)) :
    Function.Bijective (restrictGenerators B E M) := by
  constructor
  · intro h h' hh
    apply (freeHomEquivRaw B E M).injective
    simpa only [freeHomEquivRaw_apply] using congrArg (fun a ↦ a.hom) hh
  · intro a
    refine ⟨extendGenerators B E M a, ?_⟩
    apply Sheaf.hom_ext
    rw [← freeHomEquivRaw_apply]
    exact (freeHomEquivRaw B E M).apply_symm_apply a.hom

/-- The explicitly constructed extension is the inverse bijection.
Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node).

Proof: evaluating the presheaf extension on [e] gives a(e). Sheafification's unit
therefore gives the first identity. For a map h, its composite with the sheafification
unit and the extension of its generator values agree on [e], hence on finite sums.
Uniqueness in def-weil-presheaf-modules-sheafification gives the second identity.
These are steps 2--4 of the node's proof. -/
theorem freeModule_extend_inverse (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B)) :
    (∀ a : E ⟶ (underlyingRaw B).obj M,
      restrictGenerators B E M (extendGenerators B E M a) = a) ∧
    (∀ h : (free B).obj E ⟶ M,
      extendGenerators B E M (restrictGenerators B E M h) = h) := by
  constructor
  · intro a
    apply Sheaf.hom_ext
    rw [← freeHomEquivRaw_apply]
    exact (freeHomEquivRaw B E M).apply_symm_apply a.hom
  · intro h
    change (freeHomEquivRaw B E M).symm (restrictGenerators B E M h).hom = h
    rw [← freeHomEquivRaw_apply]
    exact (freeHomEquivRaw B E M).symm_apply_apply h

/-- The inverse has exactly the finite-sum formula before module sheafification.
Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node).

Proof: node steps 2--3 identify the presheaf extension with freeObjDesc, whose
component is ModuleCat.freeDesc, namely Finsupp.lift. Thus it sends a finite
coefficient family v to the sum of v(e) times a(e). The defining Hom equivalence
for module sheafification says that composing the extension with its unit is this
presheaf map. No surjectivity of the unit on sections is asserted or needed. -/
theorem freeModule_extend_formula (E : Sheaf J (Type w))
    (M : SheafOfModules.{w} (ring B))
    (a : E ⟶ (underlyingRaw B).obj M) (U : Cᵒᵖ)
    (v : E.obj.obj U →₀ (ring B).obj.obj U) :
    (extendGenerators B E M a).val.app U
      ((freeModuleUnit B E).app U v) =
        v.sum (fun e b ↦ b • @id (M.val.obj U) (a.hom.app U e)) := by
  let := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  let : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  let := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  have h : PresheafOfModules.sheafificationHomEquiv (𝟙 (ring B).obj)
      (extendGenerators B E M a) = PresheafOfModules.freeObjDesc a.hom := by
    rw [← PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
    dsimp only [extendGenerators]
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.symm_trans_apply, PresheafOfModules.freeAdjunction_homEquiv]
    erw [Equiv.apply_symm_apply]
    rfl
  have h' := congrArg (PresheafOfModules.toPresheaf (ring B).obj).map h
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h'
  have h'' := ConcreteCategory.congr_hom (NatTrans.congr_app h' U) v
  change (extendGenerators B E M a).val.app U
      ((freeModuleUnit B E).app U v) = ModuleCat.freeDesc (a.hom.app U) v at h''
  rw [h'']
  exact Finsupp.lift_apply (M := M.val.obj U) (R := (ring B).obj.obj U)
    (X := E.obj.obj U) (fun e ↦ a.hom.app U e) v

/-- Naturality of the restriction bijections in both E and M.
Source: Stacks 04BL and 03CY
(auxiliary; not a blueprint node).

Proof: node step 5 applies the sectionwise free functor to f, then sheafifies;
its generator equation follows on every basis element. Substitute that equation
in the restriction of h composed with B[f] and use associativity. Postcomposition
the same way is simply functoriality of the underlying-set functor. The inverse
bijections are natural too, by applying these equalities and injectivity. -/
theorem freeModule_restrict_naturality
    (E E' : Sheaf J (Type w)) (f : E ⟶ E')
    (M M' : SheafOfModules.{w} (ring B)) :
    (∀ h : (free B).obj E' ⟶ M,
      restrictGenerators B E M ((free B).map f ≫ h) =
        f ≫ restrictGenerators B E' M h) ∧
    (∀ (h : (free B).obj E ⟶ M) (g : M ⟶ M'),
      restrictGenerators B E M' (h ≫ g) =
        restrictGenerators B E M h ≫ (underlyingRaw B).map g) := by
  let := hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}
  let : ∀ U : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} C).inverse.op)
        AddCommGrpCat.{w} :=
    fun _ ↦ HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  let := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := AddCommGrpCat.{w})
  constructor
  · intro h
    apply Sheaf.hom_ext
    rw [← freeHomEquivRaw_apply]
    change _ = f.hom ≫ (restrictGenerators B E' M h).hom
    rw [← freeHomEquivRaw_apply]
    exact ((PresheafOfModules.freeAdjunction (ring B).obj).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ring B).obj))).homEquiv_naturality_left
        f.hom h
  · intro h g
    simp only [restrictGenerators, Functor.map_comp, Category.assoc]

/-- Every other universal realization is uniquely isomorphic with the given generators;
the inverse is the unique map taking the canonical generators to k.
Source: Stacks 04BL, universal-property consequence
(auxiliary; not a blueprint node).

Proof: node step 6 applies P's assumed bijection at B[E] to get the unique p with
p k = i, and the free-module bijection at P to get q with q i = k. Their composites
fix k and i respectively, so injectivity of the two restriction maps makes them
identities. Hence p and q are inverse. Injectivity at B[E] also makes p the unique
normalized isomorphism, and injectivity for the free module makes q unique. -/
theorem freeModule_unique_iso (E : Sheaf J (Type w))
    (P : SheafOfModules.{w} (ring B))
    (k : E ⟶ (underlyingRaw B).obj P)
    (hP : ∀ M : SheafOfModules.{w} (ring B),
      Function.Bijective (fun h : P ⟶ M ↦ k ≫ (underlyingRaw B).map h)) :
    ∃! p : P ≅ (free B).obj E,
      (k ≫ (underlyingRaw B).map p.hom = generatorRaw B E) ∧
      (generatorRaw B E ≫ (underlyingRaw B).map p.inv = k ∧
        ∀ q : (free B).obj E ⟶ P,
          generatorRaw B E ≫ (underlyingRaw B).map q = k → q = p.inv) := by
  obtain ⟨p, hp⟩ := (hP ((free B).obj E)).surjective (generatorRaw B E)
  obtain ⟨q, hq⟩ := (freeModule_restrict_bijective B E P).surjective k
  change generatorRaw B E ≫ (underlyingRaw B).map q = k at hq
  have hpq : p ≫ q = 𝟙 P := by
    apply (hP P).injective
    simp only [Functor.map_comp, Functor.map_id, ← Category.assoc, hp, hq,
      Category.comp_id]
  have hqp : q ≫ p = 𝟙 ((free B).obj E) := by
    apply (freeModule_restrict_bijective B E ((free B).obj E)).injective
    simp only [restrictGenerators, Functor.map_comp, Functor.map_id,
      ← Category.assoc, hq, hp, Category.comp_id]
  refine ⟨⟨p, q, hpq, hqp⟩, ⟨hp, hq, ?_⟩, ?_⟩
  · intro q' hq'
    apply (freeModule_restrict_bijective B E P).injective
    exact hq'.trans hq.symm
  · intro p' hp'
    apply Iso.ext
    exact (hP ((free B).obj E)).injective (hp'.1.trans hp.symm)

end CategoryTheory.SheafFreeModule
