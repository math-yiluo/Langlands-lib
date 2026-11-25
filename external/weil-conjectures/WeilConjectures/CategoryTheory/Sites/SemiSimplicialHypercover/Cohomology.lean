/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Homology.ExtResolution
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.FreeResolution

/-!
# Cohomology computed by hypercovers

Let `U` be a semi-simplicial hypercover of a site `(C, J)` and `F` a sheaf of `R`-modules. A
cocycle `z ∈ F(U_q)` of the cochain complex `C^•(U, F)` corresponds to a morphism
`R[U_q] ⟶ F` vanishing on the image of `R[U_{q + 1}]`, i.e. to a cocycle on the free resolution
`R[U_•] ⟶ R` of the constant sheaf; hence it has a class in the sheaf cohomology
`Ext^q(R, F)` (`CategoryTheory.SemiSimplicialObject.IsHypercover.cohomologyClass`).

These classes vanish on coboundaries, are natural in `F`, compatible with refinements
`V ⟶ U` of hypercovers and with connecting homomorphisms. The main result is the computation of
sheaf cohomology by hypercovers (blueprint `corollary-cohomology-pro-etale-affine`, [Stacks,
Tag 01H0]) in an elementwise form, for any class `𝒰` of hypercovers which is nonempty and in
which local lifting requirements can be met after refinement
(`CategoryTheory.SemiSimplicialObject.exists_cohomologyClass_eq` and
`CategoryTheory.SemiSimplicialObject.exists_isCoboundary_of_cohomologyClass_eq_zero`):

* every cohomology class is the class of a cocycle on some hypercover in `𝒰`;
* a cocycle whose class vanishes becomes a coboundary after refinement within `𝒰`.

Equivalently, `Ext^q(R, F)` is the colimit over refinements of the cohomology groups
`H^q(C^•(U, F))`. The proof is by dimension shifting along a short exact sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0` with `I` injective, whose cochain complexes on hypercovers are exact in
positive degrees
(`CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_cochainComplex_of_injective`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace ChainComplex.IsResolution

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜] {K : ChainComplex 𝒜 ℕ} {A : 𝒜}
  {ε : K.X 0 ⟶ A}

/-- The class of a cocycle only depends on the cocycle (and not on the proof that it is one). -/
lemma cocycleClass_congr (hK : IsResolution K ε) (q : ℕ) {F : 𝒜} {φ ψ : K.X q ⟶ F} (h : φ = ψ)
    (hφ : K.d (q + 1) q ≫ φ = 0) (hψ : K.d (q + 1) q ≫ ψ = 0) :
    hK.cocycleClass q φ hφ = hK.cocycleClass q ψ hψ := by
  subst h
  rfl

end ChainComplex.IsResolution

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type (max u v)} [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]
  {S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))}

/-- Sections over `W` of a short exact sequence of sheaves form a left exact sequence. -/
lemma ShortExact.exact_map_sections (hS : S.ShortExact) (W : Cᵒᵖ) :
    (S.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj W)).Exact :=
  hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance

/-- Sections of a monomorphism of sheaves are injective. -/
lemma ShortExact.injective_app_f (hS : S.ShortExact) (W : Cᵒᵖ) :
    Function.Injective (S.f.hom.app W).hom := by
  have := hS.mono_f
  exact (ModuleCat.mono_iff_injective _).1
    ((sheafToPresheaf J _ ⋙ (evaluation _ _).obj W).map_mono S.f)

omit [HasSheafify J (ModuleCat.{max u v} R)] in
/-- Sections of a short complex of sheaves compose to zero. -/
lemma app_g_app_f (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))) (W : Cᵒᵖ)
    (x : S.X₁.obj.obj W) : (S.g.hom.app W).hom ((S.f.hom.app W).hom x) = 0 :=
  (S.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj W)).moduleCat_zero_apply x

/-- A section over `W` of the middle term of a short exact sequence of sheaves which maps to zero
comes from the first term. -/
lemma ShortExact.exists_app_f_eq (hS : S.ShortExact) (W : Cᵒᵖ)
    (x : S.X₂.obj.obj W) (hx : (S.g.hom.app W).hom x = 0) :
    ∃ y, (S.f.hom.app W).hom y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (hS.exact_map_sections W) x hx

end CategoryTheory.ShortComplex

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Type (max u v)} [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]

section Sections

/-! ### Elementwise facts about cochain complexes and sections of sheaves -/

/-- The differential of the cochain complex commutes with morphisms of presheaves. -/
lemma cochainDifferential_naturality_apply (U : SemiSimplicialObject C)
    {F G : Cᵒᵖ ⥤ ModuleCat.{max u v} R} (φ : F ⟶ G) (q : ℕ) (z : F.obj (op (U.obj q))) :
    (U.cochainDifferential G q).hom ((φ.app _).hom z) =
      (φ.app _).hom ((U.cochainDifferential F q).hom z) := by
  have := congr(($((U.cochainComplexMap φ).comm q (q + 1))).hom z)
  simpa using this

/-- The differential of the cochain complex commutes with restriction along morphisms of
semi-simplicial objects. -/
lemma cochainDifferential_restrict_apply {U V : SemiSimplicialObject C} (f : V ⟶ U)
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (q : ℕ) (z : F.obj (op (U.obj q))) :
    (V.cochainDifferential F q).hom ((F.map (f.app q).op).hom z) =
      (F.map (f.app (q + 1)).op).hom ((U.cochainDifferential F q).hom z) := by
  have := congr(($((cochainComplexPullback f F).comm q (q + 1))).hom z)
  simpa using this

/-- The square of the differential of the cochain complex vanishes. -/
lemma cochainDifferential_cochainDifferential_apply (U : SemiSimplicialObject C)
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (q : ℕ) (z : F.obj (op (U.obj q))) :
    (U.cochainDifferential F (q + 1)).hom ((U.cochainDifferential F q).hom z) = 0 := by
  have := congr(($(U.cochainDifferential_comp F q)).hom z)
  simpa using this

/-- Restriction along the identity is the identity. -/
lemma restrict_id_apply (U : SemiSimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (q : ℕ)
    (z : F.obj (op (U.obj q))) : (F.map ((𝟙 U : U ⟶ U).app q).op).hom z = z := by
  simp

/-- Restriction along a composite is the composite of the restrictions. -/
lemma restrict_comp_apply {U V W : SemiSimplicialObject C} (g : W ⟶ V) (f : V ⟶ U)
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v} R) (q : ℕ) (z : F.obj (op (U.obj q))) :
    (F.map ((g ≫ f).app q).op).hom z =
      (F.map (g.app q).op).hom ((F.map (f.app q).op).hom z) := by
  simp

end Sections

section FreeSheaf

/-! ### Maps of free complexes -/

/-- The morphism of sheaves `R[f] : R[V_•] ⟶ R[U_•]` of free complexes induced by a morphism of
semi-simplicial objects `f : V ⟶ U`. -/
noncomputable def freeComplexMap {U V : SemiSimplicialObject C} (f : V ⟶ U) :
    V.freeComplex J R ⟶ U.freeComplex J R :=
  ChainComplex.ofHom (fun n ↦ (freeSheaf J R).map (f.app n)) (fun n ↦ by
    rw [freeComplex_d, freeComplex_d, Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, ← Functor.map_comp, ← Functor.map_comp,
      Hom.app_δ])

/-- The morphism of free complexes induced by `f : V ⟶ U` is compatible with the
augmentations. -/
lemma freeComplexMap_f_zero_comp_freeAugmentation {U V : SemiSimplicialObject C} (f : V ⟶ U) :
    (freeComplexMap (J := J) (R := R) f).f 0 ≫ U.freeAugmentation J R =
      V.freeAugmentation J R := by
  rw [freeAugmentation, freeAugmentation, ← freeYoneda_map_comp_freeYonedaToConst (f.app 0),
    Functor.map_comp]
  rfl

end FreeSheaf

/-- The cocycles of the cochain complex `C^•(U, F)` in degree `q`. -/
def IsCocycle (U : SemiSimplicialObject C) (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) : Prop :=
  (U.cochainDifferential F.obj q).hom z = 0

/-- The coboundaries of the cochain complex `C^•(U, F)` in degree `q`: `z = 0` if `q = 0`. -/
def IsCoboundary (U : SemiSimplicialObject C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    ∀ (q : ℕ), F.obj.obj (op (U.obj q)) → Prop
  | 0, z => z = 0
  | q + 1, z => ∃ y, (U.cochainDifferential F.obj q).hom y = z

section IsCocycle

variable {U : SemiSimplicialObject C} {F : Sheaf J (ModuleCat.{max u v} R)} {q : ℕ}

omit [HasSheafify J (ModuleCat.{max u v} R)] in
/-- `0` is a cocycle. -/
lemma isCocycle_zero : U.IsCocycle F q 0 :=
  map_zero _

omit [HasSheafify J (ModuleCat.{max u v} R)] in
/-- The sum of two cocycles is a cocycle. -/
lemma IsCocycle.add {z z' : F.obj.obj (op (U.obj q))} (hz : U.IsCocycle F q z)
    (hz' : U.IsCocycle F q z') : U.IsCocycle F q (z + z') := by
  rw [IsCocycle, map_add, hz, hz', add_zero]

omit [HasSheafify J (ModuleCat.{max u v} R)] in
/-- The image of a cocycle under a morphism of sheaves is a cocycle. -/
lemma IsCocycle.map {G : Sheaf J (ModuleCat.{max u v} R)} (φ : F ⟶ G)
    {z : F.obj.obj (op (U.obj q))} (hz : U.IsCocycle F q z) :
    U.IsCocycle G q ((φ.hom.app _).hom z) := by
  rw [IsCocycle, cochainDifferential_naturality_apply, hz, map_zero]

omit [HasSheafify J (ModuleCat.{max u v} R)] in
/-- The restriction of a cocycle along a morphism of semi-simplicial objects is a cocycle. -/
lemma IsCocycle.restrict {V : SemiSimplicialObject C} (f : V ⟶ U)
    {z : F.obj.obj (op (U.obj q))} (hz : U.IsCocycle F q z) :
    V.IsCocycle F q ((F.obj.map (f.app q).op).hom z) := by
  rw [IsCocycle, cochainDifferential_restrict_apply, hz, map_zero]

/-- A section is a cocycle if and only if the corresponding morphism from the free sheaf vanishes
on the image of the differential. -/
lemma isCocycle_iff_d_comp_eq_zero (z : F.obj.obj (op (U.obj q))) :
    U.IsCocycle F q z ↔
      (U.freeComplex J R).d (q + 1) q ≫ (freeSheafHomEquiv J R (U.obj q) F).symm z = 0 := by
  rw [← (freeSheafHomEquiv J R (U.obj (q + 1)) F).injective.eq_iff, freeSheafHomEquiv_d_comp,
    Equiv.apply_symm_apply, IsCocycle, ← map_zero (freeSheafHomAddEquiv J R (U.obj (q + 1)) F)]
  rfl

end IsCocycle

variable [HasExt.{w} (Sheaf J (ModuleCat.{max u v} R))]

namespace IsHypercover

variable {U : SemiSimplicialObject C}

omit [HasExt.{w} (Sheaf J (ModuleCat.{max u v} R))] in
/-- The free complex of a hypercover is a resolution of the constant sheaf. -/
lemma isResolution (hU : U.IsHypercover J) :
    (U.freeComplex J R).IsResolution (U.freeAugmentation J R) where
  d_comp := U.freeComplex_d_freeAugmentation J R
  exactAt := hU.exactAt_freeComplex R
  exact_zero := hU.exact_freeAugmentation R
  epi := hU.epi_freeAugmentation R

/-- The class in `Ext^q(R, F)` of a cocycle `z ∈ F(U_q)` on a hypercover `U`. -/
noncomputable def cohomologyClass (hU : U.IsHypercover J) (F : Sheaf J (ModuleCat.{max u v} R))
    (q : ℕ) (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) :
    Ext (constSheaf J R) F q :=
  hU.isResolution.cocycleClass q ((freeSheafHomEquiv J R (U.obj q) F).symm z)
    ((isCocycle_iff_d_comp_eq_zero z).1 hz)

variable (hU : U.IsHypercover J)
include hU

/-- The class of a cocycle only depends on the cocycle. -/
lemma cohomologyClass_congr (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    {z z' : F.obj.obj (op (U.obj q))} (h : z = z') (hz : U.IsCocycle F q z)
    (hz' : U.IsCocycle F q z') :
    hU.cohomologyClass F q z hz = hU.cohomologyClass F q z' hz' := by
  subst h
  rfl

lemma cohomologyClass_add (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z z' : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) (hz' : U.IsCocycle F q z') :
    hU.cohomologyClass F q (z + z') (hz.add hz') =
      hU.cohomologyClass F q z hz + hU.cohomologyClass F q z' hz' := by
  rw [cohomologyClass, cohomologyClass, cohomologyClass,
    ← hU.isResolution.cocycleClass_add]
  exact hU.isResolution.cocycleClass_congr _
    (map_add (freeSheafHomAddEquiv J R (U.obj q) F).symm z z') _ _

/-- Coboundaries have vanishing class. -/
lemma cohomologyClass_eq_zero_of_isCoboundary (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) (hz' : U.IsCoboundary F q z) :
    hU.cohomologyClass F q z hz = 0 := by
  cases q with
  | zero =>
    obtain rfl : z = 0 := hz'
    have h0 : (freeSheafHomEquiv J R (U.obj 0) F).symm 0 =
        (freeSheafHomEquiv J R (U.obj 0) F).symm 0 ≫ (0 : F ⟶ F) := by
      rw [Limits.comp_zero, ← map_zero (freeSheafHomAddEquiv J R (U.obj 0) F).symm]
      rfl
    rw [cohomologyClass, hU.isResolution.cocycleClass_congr 0 h0
        ((isCocycle_iff_d_comp_eq_zero 0).1 hz) (by rw [Limits.comp_zero, Limits.comp_zero]),
      hU.isResolution.cocycleClass_comp, Ext.mk₀_zero, Ext.comp_zero]
    exact (isCocycle_iff_d_comp_eq_zero 0).1 hz
  | succ q =>
    obtain ⟨y, rfl⟩ := hz'
    rw [cohomologyClass, ← hU.isResolution.cocycleClass_d q
      ((freeSheafHomEquiv J R (U.obj q) F).symm y)]
    refine hU.isResolution.cocycleClass_congr _ ?_ _ _
    apply (freeSheafHomEquiv J R (U.obj (q + 1)) F).injective
    rw [freeSheafHomEquiv_d_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Naturality in the sheaf. -/
lemma cohomologyClass_map {F G : Sheaf J (ModuleCat.{max u v} R)} (φ : F ⟶ G) (q : ℕ)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z) :
    hU.cohomologyClass G q ((φ.hom.app _).hom z) (hz.map φ) =
      (hU.cohomologyClass F q z hz).comp (Ext.mk₀ φ) (add_zero q) := by
  rw [cohomologyClass, cohomologyClass, ← hU.isResolution.cocycleClass_comp]
  refine hU.isResolution.cocycleClass_congr _ ?_ _ _
  apply (freeSheafHomEquiv J R (U.obj q) G).injective
  rw [freeSheafHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Compatibility with refinements: the class of the restriction of a cocycle along a morphism of
hypercovers `f : V ⟶ U` is the class of the cocycle. -/
lemma cohomologyClass_restrict {V : SemiSimplicialObject C} (hV : V.IsHypercover J) (f : V ⟶ U)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (z : F.obj.obj (op (U.obj q)))
    (hz : U.IsCocycle F q z) :
    hV.cohomologyClass F q ((F.obj.map (f.app q).op).hom z) (hz.restrict f) =
      hU.cohomologyClass F q z hz := by
  rw [cohomologyClass, cohomologyClass, ← hU.isResolution.cocycleClass_naturality hV.isResolution
    (freeComplexMap f) (freeComplexMap_f_zero_comp_freeAugmentation f)]
  refine hV.isResolution.cocycleClass_congr _ ?_ _ _
  apply (freeSheafHomEquiv J R (V.obj q) F).injective
  rw [Equiv.apply_symm_apply]
  exact ((freeSheafHomEquiv_map_comp J R (f.app q) F
    ((freeSheafHomEquiv J R (U.obj q) F).symm z)).trans (by rw [Equiv.apply_symm_apply])).symm

/-- Compatibility with connecting homomorphisms: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`
of sheaves, a cocycle `w ∈ X₃(U_q)` which lifts to `w' ∈ X₂(U_q)`, and `v ∈ X₁(U_{q + 1})` mapping
to `d w'`, the class of `v` is the image of the class of `w` under the connecting map. -/
lemma cohomologyClass_extClass {S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))}
    (hS : S.ShortExact) (q : ℕ) (w' : S.X₂.obj.obj (op (U.obj q)))
    (hw : U.IsCocycle S.X₃ q ((S.g.hom.app _).hom w')) (v : S.X₁.obj.obj (op (U.obj (q + 1))))
    (hv : (S.f.hom.app _).hom v = (U.cochainDifferential S.X₂.obj q).hom w')
    (hv' : U.IsCocycle S.X₁ (q + 1) v) :
    hU.cohomologyClass S.X₁ (q + 1) v hv' =
      (hU.cohomologyClass S.X₃ q _ hw).comp hS.extClass rfl := by
  have hφ : (freeSheafHomEquiv J R (U.obj q) S.X₃).symm ((S.g.hom.app _).hom w') =
      (freeSheafHomEquiv J R (U.obj q) S.X₂).symm w' ≫ S.g := by
    apply (freeSheafHomEquiv J R (U.obj q) S.X₃).injective
    rw [freeSheafHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [cohomologyClass, cohomologyClass, hU.isResolution.cocycleClass_congr q hφ _
    (hφ ▸ (isCocycle_iff_d_comp_eq_zero _).1 hw)]
  refine hU.isResolution.cocycleClass_extClass hS q _ _ _ ?_ _
  apply (freeSheafHomEquiv J R (U.obj (q + 1)) S.X₂).injective
  rw [freeSheafHomEquiv_comp, freeSheafHomEquiv_d_comp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, hv]

/-- In degree `0` the classes of cocycles exhaust `Ext⁰(R, F)`, each exactly once. -/
lemma bijective_cohomologyClass_zero (F : Sheaf J (ModuleCat.{max u v} R)) :
    Function.Bijective (fun z : {z : F.obj.obj (op (U.obj 0)) // U.IsCocycle F 0 z} ↦
      hU.cohomologyClass F 0 z.1 z.2) := by
  let e : {z : F.obj.obj (op (U.obj 0)) // U.IsCocycle F 0 z} ≃
      {φ : (U.freeComplex J R).X 0 ⟶ F // (U.freeComplex J R).d 1 0 ≫ φ = 0} :=
    Equiv.subtypeEquiv (freeSheafHomEquiv J R (U.obj 0) F).symm
      (fun z ↦ isCocycle_iff_d_comp_eq_zero (q := 0) z)
  have key (z : {z : F.obj.obj (op (U.obj 0)) // U.IsCocycle F 0 z}) :
      hU.cohomologyClass F 0 z.1 z.2 = hU.isResolution.cocycleClass 0 (e z).1 (e z).2 := by
    rfl
  have h := (hU.isResolution.bijective_cocycleClass_zero F).comp e.bijective
  convert h using 1
  exact funext key

end IsHypercover

/-- The inductive step of `CategoryTheory.SemiSimplicialObject.exists_cohomologyClass_eq`, along a
short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` injective. -/
lemma exists_cohomologyClass_eq_succ (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    {S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))} (hS : S.ShortExact) [Injective S.X₂]
    (q : ℕ) (ih : ∀ y : Ext (constSheaf J R) S.X₃ q, ∃ (U : SemiSimplicialObject C) (hU : 𝒰 U)
      (z : S.X₃.obj.obj (op (U.obj q))) (hz : U.IsCocycle S.X₃ q z),
        (h𝒰 U hU).cohomologyClass S.X₃ q z hz = y)
    (x : Ext (constSheaf J R) S.X₁ (q + 1)) :
    ∃ (U : SemiSimplicialObject C) (hU : 𝒰 U) (z : S.X₁.obj.obj (op (U.obj (q + 1))))
      (hz : U.IsCocycle S.X₁ (q + 1) z), (h𝒰 U hU).cohomologyClass S.X₁ (q + 1) z hz = x := by
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) rfl
  obtain ⟨U, hU, w, hw, rfl⟩ := ih y
  have := hS.epi_g
  obtain ⟨V, hV, f, w', hw'⟩ := hlift U hU q S.g w
  obtain ⟨v, hv⟩ := hS.exists_app_f_eq _ ((V.cochainDifferential S.X₂.obj q).hom w') (by
    rw [← cochainDifferential_naturality_apply, hw', cochainDifferential_restrict_apply, hw,
      map_zero])
  have hv' : V.IsCocycle S.X₁ (q + 1) v := by
    apply hS.injective_app_f
    rw [map_zero, ← cochainDifferential_naturality_apply, hv,
      cochainDifferential_cochainDifferential_apply]
  have hw'' : V.IsCocycle S.X₃ q ((S.g.hom.app _).hom w') := by
    rw [hw']
    exact hw.restrict f
  refine ⟨V, hV, v, hv', ?_⟩
  rw [(h𝒰 V hV).cohomologyClass_extClass hS q w' hw'' v hv hv',
    (h𝒰 V hV).cohomologyClass_congr _ q hw' hw'' (hw.restrict f),
    (h𝒰 U hU).cohomologyClass_restrict (h𝒰 V hV) f]

variable [EnoughInjectives (Sheaf J (ModuleCat.{max u v} R))] in
/-- **Every cohomology class is computed on a hypercover** (blueprint
`corollary-cohomology-pro-etale-affine`). Let `𝒰` be a nonempty class of hypercovers in which local
lifts of sections through epimorphisms of sheaves can be obtained after refinement. Then every
class in `Ext^q(R, F)` is the class of a cocycle on some hypercover of `𝒰`. -/
theorem exists_cohomologyClass_eq (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J) (hne : ∃ U, 𝒰 U)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (x : Ext (constSheaf J R) F q) :
    ∃ (U : SemiSimplicialObject C) (hU : 𝒰 U) (z : F.obj.obj (op (U.obj q)))
      (hz : U.IsCocycle F q z), (h𝒰 U hU).cohomologyClass F q z hz = x := by
  induction q generalizing F with
  | zero =>
    obtain ⟨U, hU⟩ := hne
    obtain ⟨⟨z, hz⟩, h⟩ := ((h𝒰 U hU).bijective_cohomologyClass_zero F).2 x
    exact ⟨U, hU, z, hz, h⟩
  | succ q ih =>
    exact exists_cohomologyClass_eq_succ 𝒰 h𝒰 hlift (S := ShortComplex.mk (Injective.ι F)
      (cokernel.π _) (cokernel.condition _))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) } q (ih _) x

/-- The inductive step of
`CategoryTheory.SemiSimplicialObject.exists_isCoboundary_of_cohomologyClass_eq_zero`, along a
short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₂` injective. -/
lemma exists_isCoboundary_succ (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    {S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))} (hS : S.ShortExact) [Injective S.X₂]
    (q : ℕ) (ih : ∀ (U : SemiSimplicialObject C) (hU : 𝒰 U) (z : S.X₃.obj.obj (op (U.obj q)))
      (hz : U.IsCocycle S.X₃ q z), (h𝒰 U hU).cohomologyClass S.X₃ q z hz = 0 →
        ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U),
          V.IsCoboundary S.X₃ q ((S.X₃.obj.map (f.app q).op).hom z))
    (U : SemiSimplicialObject C) (hU : 𝒰 U) (z : S.X₁.obj.obj (op (U.obj (q + 1))))
    (hz : U.IsCocycle S.X₁ (q + 1) z) (h : (h𝒰 U hU).cohomologyClass S.X₁ (q + 1) z hz = 0) :
    ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U),
      V.IsCoboundary S.X₁ (q + 1) ((S.X₁.obj.map (f.app (q + 1)).op).hom z) := by
  have := hS.epi_g
  obtain ⟨y, hy⟩ := (h𝒰 U hU).exists_cochainDifferential_eq_of_injective S.X₂ q _ (hz.map S.f)
  have hyb : U.IsCocycle S.X₃ q ((S.g.hom.app _).hom y) := by
    rw [IsCocycle, cochainDifferential_naturality_apply, hy, ShortComplex.app_g_app_f]
  have hext : ((h𝒰 U hU).cohomologyClass S.X₃ q _ hyb).comp hS.extClass rfl = 0 := by
    rw [← (h𝒰 U hU).cohomologyClass_extClass hS q y hyb z hy.symm hz, h]
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ _ hS _ rfl hext
  cases q with
  | zero =>
    obtain ⟨⟨s, hs⟩, rfl⟩ := ((h𝒰 U hU).bijective_cohomologyClass_zero S.X₂).2 t
    have hsy : (S.g.hom.app _).hom s = (S.g.hom.app _).hom y := by
      rw [← (h𝒰 U hU).cohomologyClass_map S.g 0 s hs] at ht
      exact congr_arg Subtype.val (((h𝒰 U hU).bijective_cohomologyClass_zero S.X₃).1
        (a₁ := ⟨_, hs.map S.g⟩) (a₂ := ⟨_, hyb⟩) ht)
    obtain ⟨b, hb⟩ := hS.exists_app_f_eq _ (y - s) (by rw [map_sub, hsy, sub_self])
    refine ⟨U, hU, 𝟙 U, b, ?_⟩
    apply hS.injective_app_f
    rw [restrict_id_apply, ← cochainDifferential_naturality_apply, hb, map_sub, hy, hs, sub_zero]
  | succ q =>
    rw [Ext.eq_zero_of_injective t, Ext.zero_comp] at ht
    obtain ⟨V, hV, f, b', hb'⟩ := ih U hU _ hyb ht.symm
    obtain ⟨V', hV', g, b, hb⟩ := hlift V hV q S.g b'
    obtain ⟨a, ha⟩ := hS.exists_app_f_eq _
      ((S.X₂.obj.map ((g ≫ f).app (q + 1)).op).hom y - (V'.cochainDifferential S.X₂.obj q).hom b)
      (by
        rw [map_sub, ← cochainDifferential_naturality_apply, hb, cochainDifferential_restrict_apply,
          hb', restrict_comp_apply, ← NatTrans.naturality_apply (S.g.hom),
          ← NatTrans.naturality_apply (S.g.hom), sub_self])
    refine ⟨V', hV', g ≫ f, a, ?_⟩
    apply hS.injective_app_f
    rw [← cochainDifferential_naturality_apply, ha, map_sub,
      cochainDifferential_cochainDifferential_apply, sub_zero, cochainDifferential_restrict_apply,
      hy, NatTrans.naturality_apply]

variable [EnoughInjectives (Sheaf J (ModuleCat.{max u v} R))] in
/-- **A cocycle with vanishing class is a coboundary after refinement** (blueprint
`corollary-cohomology-pro-etale-affine`). Under the assumptions of
`CategoryTheory.SemiSimplicialObject.exists_cohomologyClass_eq`, if the class of a cocycle `z`
on a hypercover `U ∈ 𝒰` vanishes, then its restriction to some refinement `V ⟶ U` in `𝒰` is a
coboundary. -/
theorem exists_isCoboundary_of_cohomologyClass_eq_zero (𝒰 : SemiSimplicialObject C → Prop)
    (h𝒰 : ∀ U, 𝒰 U → U.IsHypercover J)
    (hlift : ∀ U, 𝒰 U → ∀ (p : ℕ) {G Q : Sheaf J (ModuleCat.{max u v} R)} (φ : G ⟶ Q) [Epi φ]
      (w : Q.obj.obj (op (U.obj p))), ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U)
        (w' : G.obj.obj (op (V.obj p))), (φ.hom.app _).hom w' = (Q.obj.map (f.app p).op).hom w)
    (F : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) (U : SemiSimplicialObject C) (hU : 𝒰 U)
    (z : F.obj.obj (op (U.obj q))) (hz : U.IsCocycle F q z)
    (h : (h𝒰 U hU).cohomologyClass F q z hz = 0) :
    ∃ (V : SemiSimplicialObject C) (_ : 𝒰 V) (f : V ⟶ U),
      V.IsCoboundary F q ((F.obj.map (f.app q).op).hom z) := by
  induction q generalizing F U with
  | zero =>
    refine ⟨U, hU, 𝟙 U, ?_⟩
    have := ((h𝒰 U hU).bijective_cohomologyClass_zero F).1 (a₁ := ⟨z, hz⟩)
      (a₂ := ⟨0, isCocycle_zero⟩)
      (by simpa only [h] using ((h𝒰 U hU).cohomologyClass_eq_zero_of_isCoboundary F 0 0
        isCocycle_zero rfl).symm)
    rw [restrict_id_apply]
    exact congr_arg Subtype.val this
  | succ q ih =>
    exact exists_isCoboundary_succ 𝒰 h𝒰 hlift (S := ShortComplex.mk (Injective.ι F)
      (cokernel.π _) (cokernel.condition _))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) } q (ih _) U hU z
      hz h

end CategoryTheory.SemiSimplicialObject
