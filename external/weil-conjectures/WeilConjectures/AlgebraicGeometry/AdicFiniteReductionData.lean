/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionFinitePull
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
/-! # Canonical scalar maps for finite adic reductions

Source: Stacks Project, proetale.tex, Tag 09C2, with Tag 09AL for compatible etale origins
(auxiliary; not a blueprint node).

The input and both reduction categories use ConstantCompletion.D on the equivalent
coefficient-sized sites. The coefficient universe is independent of the scheme universe.
Index n means positive exponent n+1. All scalar units and composition comparisons below
are uniquely normalized by the ordinary scalar insertion and their K-flat computations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
attribute [local instance 10000] change_additive pull_additive SheafOfModules.instAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] derivedExtension derivedPull DerivedCategory.Q
  CategoryTheory.constantSheaf CategoryTheory.Functor.mapDerivedCategory

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsKFlatTensor
  CochainComplex.IsKFlatIndependentCoefficients

namespace AlgebraicGeometry.Scheme

variable {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}

@[instance_reducible, no_expose]
private def adicFiniteSectionModule (R : Sheaf T CommRingCat.{w})
    (M : Mod R) (U : Dᵒᵖ) : Module (R.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

attribute [local instance 10000] adicFiniteSectionModule

private structure AdicFiniteGood (R : Sheaf T CommRingCat.{w}) (K : Cx R) : Prop where
  kflat : K.IsKFlatTensor
  flat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q)

private theorem adicFiniteGood_resolution {R : Sheaf T CommRingCat.{w}} (K : Cx R) :
    ∃ (Y : Cx R) (q : Y ⟶ K), AdicFiniteGood R Y ∧ QuasiIso q := by
  obtain ⟨Y, q, hY, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  exact ⟨Y, q,
    ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Y).mp hY, hf⟩, hq⟩

private theorem adicFiniteGood_change {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (K : Cx R) (hK : AdicFiniteGood R K) :
    AdicFiniteGood S (((change f).mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨hk, hf⟩ := change_flat_kFlat f K hK.kflat hK.flat
  refine ⟨hk, ?_⟩
  simpa only [Functor.mapHomologicalComplex_obj_X] using hf

private theorem adicFiniteGood_pull
    {E : Type w} [SmallCategory E] {TE : GrothendieckTopology E}
    {L : Sheaf T (Type w) ⥤ Sheaf TE (Type w)} (F : InverseImageData L)
    (U : Sheaf TE (Type w) ⥤ Sheaf T (Type w)) (adj : L ⊣ U)
    [PreservesFiniteLimits L] {R : Sheaf T CommRingCat.{w}} {S : Sheaf TE CommRingCat.{w}}
    (c : F.rings.obj R ⟶ S) (K : Cx R) (hK : AdicFiniteGood R K) :
    AdicFiniteGood S (((pull F c).mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨hk, hf⟩ := pull_flat_kFlat F U adj c K hK.kflat hK.flat
  refine ⟨hk, ?_⟩
  simpa only [Functor.mapHomologicalComplex_obj_X] using hf

private theorem adicFiniteExtension_isIso {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (K : Cx R) (hK : K.IsKFlatTensor) :
    IsIso ((extendComparison f).app K) :=
  (derivedExtension f).computation K hK

private theorem adicFinitePull_isIso
    {E : Type w} [SmallCategory E] {TE : GrothendieckTopology E}
    {L : Sheaf T (Type w) ⥤ Sheaf TE (Type w)} {F : InverseImageData L}
    {R : Sheaf T CommRingCat.{w}} {S : Sheaf TE CommRingCat.{w}}
    {c : F.rings.obj R ⟶ S} (pa : DerivedPull F c) (K : Cx R)
    (hK : AdicFiniteGood R K) : IsIso (pa.comparison.app K) :=
  pa.computation K hK.kflat hK.flat

/-- The ordinary tensor unit is uniquely specified by insertion of 1 on sections.
Proof: scalar insertion is linear over the source ring, natural and compatible with
restrictions. Sheafification gives the map. The underlying-sheaf functor is faithful.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteOrdinaryUnit_existsUnique {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! e : 𝟭 (Mod R) ⟶ change f ⋙ res f,
      ∀ M : Mod R, (underlying R).map (e.app M) = insertion f M := by
  let e : 𝟭 (Mod R) ⟶ change f ⋙ res f := (SheafOfModules.tensorAdjunction f).unit
  have he (M : Mod R) : (underlying R).map (e.app M) = insertion f M := by
    apply (insertion_existsUnique f M).unique
    · exact SheafOfModules.tensorUnit_apply f M
    · exact (insertion_existsUnique f M).exists.choose_spec
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply NatTrans.ext
  funext M
  apply (underlying R).map_injective
  exact (he' M).trans (he M).symm

/-- The actual scalar insertion, retaining its unique sectionwise normalization.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteOrdinaryUnit {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    𝟭 (Mod R) ⟶ change f ⋙ res f :=
  (adicFiniteOrdinaryUnit_existsUnique f).exists.choose

/-- Apply scalar insertion termwise to a complex; all maps are those of the tensor unit.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteOrdinaryUnitComplex {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S)
    (P : Cx R) : P ⟶ ((res f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f i := (adicFiniteOrdinaryUnit f).app (P.X i)
  comm' i j _ := ((adicFiniteOrdinaryUnit f).naturality (P.d i j)).symm

/-- Apply an ordinary comparison square termwise, retaining the explicit composite
functors on complexes. This is exactly the usual termwise natural isomorphism.
Source: Stacks Tag 06YY (auxiliary; not a blueprint node). -/
def adicFiniteComplexSquare
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
    (o : F ⋙ G ≅ H ⋙ I) :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex o (.up ℤ)

private theorem adicFiniteUniqueGuard
    {E K : Type*} {G P Q : K → Prop} {V : K → Sort*}
    {l r : E → (k : K) → V k}
    (hin : ∀ k, P k → Q k → G k) (hout : ∀ k, G k → P k ∧ Q k)
    (h : ∃! e, ∀ k, G k → l e k = r e k) :
    ∃! e, ∀ k, P k → Q k → r e k = l e k := by
  obtain ⟨e, he, hu⟩ := h
  refine ⟨e, fun k hp hq ↦ (he k (hin k hp hq)).symm, ?_⟩
  intro e' he'
  apply hu e'
  intro k hk
  exact (he' k (hout k hk).1 (hout k hk).2).symm

private theorem adicFiniteModuleSquare
    {M₀ M₁ M₂ M₃ D₁ D₂ D₃ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃]
    [Abelian M₀] [HasDerivedCategory M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Category D₁] [Category D₂] [Category D₃]
    (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms]
    {dr : DerivedCategory M₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃}
    {db : DerivedCategory M₀ ⥤ D₂}
    (α : DerivedCategory.Q ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s)
    (δ : DerivedCategory.Q ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (P : CochainComplex M₀ ℤ → Prop)
    (hres : ∀ X : CochainComplex M₀ ℤ,
      ∃ (K : CochainComplex M₀ ℤ) (f : K ⟶ X), P K ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app ((r.mapHomologicalComplex (.up ℤ)).obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X))
    (hε : ∀ X, P X → IsIso (ε.app ((b.mapHomologicalComplex (.up ℤ)).obj X))) :
    ∃! e : dr ⋙ dp ≅ db ⋙ ds, ∀ X, P X →
      dp.map (α.app X) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₃.map ((adicFiniteComplexSquare γ).hom.app X) =
        e.hom.app (DerivedCategory.Q.obj X) ≫ ds.map (δ.app X) ≫
          ε.app ((b.mapHomologicalComplex (.up ℤ)).obj X) := by
  obtain ⟨e, he, hu⟩ := resolving_module_square_iso q₁ q₂ q₃ r s p b α β γ δ ε
    P hres hα hβ hδ hε
  exact ⟨e, he, hu⟩

/-- Ordinary restriction composition is the identity on underlying sections.
Proof: both actions precompose by the composite ring map, and the identity maps of
additive sheaves are linear. Their inverses are the same identities; faithfulness
of the underlying functor proves uniqueness.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteResComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : res g ⋙ res f ≅ res (f ≫ g),
      ∀ M : Mod V, (underlying R).map (e.hom.app M) = 𝟙 _ := by
  let i := resCompIso f g (f ≫ g) rfl
  have hi (M : Mod V) : (underlying R).map (i.hom.app M) = 𝟙 _ := by
    ext U m
    exact resCompIso_hom_apply f g (f ≫ g) rfl M U m
  refine ⟨i, hi, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (underlying R).map_injective
  exact (he M).trans (hi M).symm

/-- The sectionwise restriction composition isomorphism.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteResComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    res g ⋙ res f ≅ res (f ≫ g) :=
  (adicFiniteResComp_existsUnique f g).exists.choose

/-- Exact derived restriction composition, obtained from the sectionwise identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteDresComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    dres g ⋙ dres f ≅ dres (f ≫ g) :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod S)
  letI := HasDerivedCategory.standard (Mod V)
  letI := (siteRestrictScalars_exact f).1
  letI := (siteRestrictScalars_exact f).2
  letI := (siteRestrictScalars_exact g).1
  letI := (siteRestrictScalars_exact g).2
  letI := (siteRestrictScalars_exact (f ≫ g)).1
  letI := (siteRestrictScalars_exact (f ≫ g)).2
  Functor.mapDerivedCategoryCompIso (res g) (res f) ≪≫
    Functor.mapDerivedCategoryNatIso (adicFiniteResComp f g)

@[no_expose]
private def adicFiniteAdjunction
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) : change f ⊣ res f :=
  SheafOfModules.tensorAdjunction f

@[no_expose]
private def adicFiniteHomEquiv
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R) (N : Mod S) :
    ((change f).obj M ⟶ N) ≃ (M ⟶ (res f).obj N) :=
  (adicFiniteAdjunction f).homEquiv M N

private theorem adicFiniteHomEquiv_apply
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R) (N : Mod S)
    (a : (change f).obj M ⟶ N) (U : Cᵒᵖ) (m : M.val.obj U) :
    (adicFiniteHomEquiv f M N a).val.app U m =
      a.val.app U (tensorSection f M U 1 m) := by
  rfl

private theorem adicFiniteAdjunction_homEquiv {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N) :
    (adicFiniteAdjunction f).homEquiv M N a = adicFiniteHomEquiv f M N a := by
  rfl

private theorem adicFiniteAdjunction_unit {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) : (adicFiniteAdjunction f).unit = adicFiniteOrdinaryUnit f := by
  apply NatTrans.ext
  funext M
  apply (underlying R).map_injective
  have h : (underlying R).map ((adicFiniteAdjunction f).unit.app M) = insertion f M := by
    apply (insertion_existsUnique f M).unique
    · intro U m
      change ((adicFiniteAdjunction f).unit.app M).val.app U m = _
      rw [← Adjunction.homEquiv_id, adicFiniteAdjunction_homEquiv]
      rfl
    · exact (insertion_existsUnique f M).exists.choose_spec
  exact h.trans ((adicFiniteOrdinaryUnit_existsUnique f).exists.choose_spec M).symm

attribute [local irreducible] adicFiniteAdjunction
  Adjunction.ofNatIsoLeft Adjunction.leftAdjointUniq

@[no_expose]
private def adicFiniteLeftDerivedUnique
    {A B C : Type*} [Category A] [Category B] [Category C]
    {q : A ⥤ B} (W : MorphismProperty A) [q.IsLocalization W]
    {F : A ⥤ C} {L G : B ⥤ C} (α : q ⋙ L ⟶ F) (β : q ⋙ G ⟶ F)
    [L.IsLeftDerivedFunctor α W] [G.IsLeftDerivedFunctor β W] : L ≅ G :=
  Functor.leftDerivedUnique G L α β W

private theorem adicFiniteLeftDerivedUnique_fac
    {A B C : Type*} [Category A] [Category B] [Category C]
    {q : A ⥤ B} (W : MorphismProperty A) [q.IsLocalization W]
    {F : A ⥤ C} {L G : B ⥤ C} (α : q ⋙ L ⟶ F) (β : q ⋙ G ⟶ F)
    [L.IsLeftDerivedFunctor α W] [G.IsLeftDerivedFunctor β W] (X : A) :
    (adicFiniteLeftDerivedUnique W α β).hom.app (q.obj X) ≫ β.app X = α.app X := by
  simpa only [adicFiniteLeftDerivedUnique, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso_hom, Functor.leftDerivedNatTrans, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] using G.leftDerived_fac_app β W L α X

attribute [local irreducible] adicFiniteLeftDerivedUnique

private theorem adicFiniteDerivedUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (adj : E ⊣ R)
    (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X : CochainComplex A ℤ, ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
      P Y ∧ QuasiIso s)
    (hpres : ∀ {X Y : CochainComplex A ℤ} (f : X ⟶ Y), P X → P Y → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f))
    (LD : DerivedCategory A ⥤ DerivedCategory B)
    (β : DerivedCategory.Q ⋙ LD ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [LD.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso A (.up ℤ))]
    (hβ : ∀ X, P X → IsIso (β.app X))
    (ν : ∀ X : CochainComplex A ℤ,
      X ⟶ (R.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj X))
    (hν : ∀ X, (adj.mapHomologicalComplex (.up ℤ)).unit.app X = ν X) :
    ∃! η : 𝟭 (DerivedCategory A) ⟶ LD ⋙ R.mapDerivedCategory,
      ∀ X, P X → η.app (DerivedCategory.Q.obj X) ≫
        R.mapDerivedCategory.map (β.app X) = DerivedCategory.Q.map (ν X) ≫
          R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
  obtain ⟨_, L, ε, hu, _, d, hd⟩ :=
    Adjunction.exists_leftDerived_adjunction E R adj P hres hpres
  let : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) := hu
  let i : L ≅ LD := adicFiniteLeftDerivedUnique
    (HomologicalComplex.quasiIso A (.up ℤ)) ε β
  let d' : LD ⊣ R.mapDerivedCategory := d.ofNatIsoLeft i
  have hi (X : CochainComplex A ℤ) :
      i.hom.app (DerivedCategory.Q.obj X) ≫ β.app X = ε.app X :=
    adicFiniteLeftDerivedUnique_fac (HomologicalComplex.quasiIso A (.up ℤ)) ε β X
  have he (X : CochainComplex A ℤ) :
      d'.unit.app (DerivedCategory.Q.obj X) ≫ R.mapDerivedCategory.map (β.app X) =
        DerivedCategory.Q.map (ν X) ≫
          R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj X) := by
    have ht := (d'.homEquiv_unit _ _ (β.app X)).symm
    apply ht.trans
    change (d.ofNatIsoLeft i).homEquiv _ _ (β.app X) = _
    rw [Adjunction.homEquiv_ofNatIsoLeft_apply, hi]
    have h := hd X ((E.mapHomologicalComplex (.up ℤ)).obj X) (𝟙 _)
    simp only [Adjunction.homEquiv_id, hν] at h
    rw [(DerivedCategory.Q (C := B)).map_id] at h
    have hid := Category.comp_id (ε.app X)
    exact (congrArg (d.homEquiv (DerivedCategory.Q.obj X)
      ((E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).obj X)) hid).symm.trans h
  refine ⟨d'.unit, fun X _ ↦ he X, ?_⟩
  intro η hη
  apply resolving_nat_ext P hres η d'.unit
  intro Y hY
  let := hβ Y hY
  apply (cancel_mono (R.mapDerivedCategory.map (β.app Y))).1
  exact (hη Y hY).trans (he Y).symm

section

attribute [local irreducible] change pull

/-- The explicit normalization predicate, kept as a named API so choosing its unique
witness does not expand the cochain comparison formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteUnitFormula {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S)
    (e : 𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f) : Prop :=
  ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.app ((Q R).obj P) ≫ (dres f).map ((extendComparison f).app P) =
          (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
            (resFactors f).hom.app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- The derived quotient unit, uniquely specified on K-flat complexes.
Proof: derive the ordinary tensor/restriction adjunction. Exact restriction has the
resFactors comparison; on K-flat models the universal tensor comparison is invertible.
The displayed formula therefore determines the unit there and hence on all derived objects.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteUnit_existsUnique {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! e : 𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f,
      adicFiniteUnitFormula f e := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let : Abelian (Mod S) :=
    { (inferInstance : Abelian (Mod S)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  have hpres' {P Q : Cx R} (a : P ⟶ Q)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
      (ha : QuasiIso a) :
      QuasiIso (((change f).mapHomologicalComplex (.up ℤ)).map a) :=
    change_preserves_kFlat_quasiIso T f a
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mp hQ) ha
  let : (extend f).IsLeftDerivedFunctor (extendComparison f)
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := (derivedExtension f).universal
  exact adicFiniteDerivedUnit (change f) (res f) (adicFiniteAdjunction f)
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ by
      obtain ⟨Y, s, hY, _, hs, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
      exact ⟨Y, s, hY, hs⟩) hpres'
    (extend f) (extendComparison f)
    (fun P hP ↦ adicFiniteExtension_isIso f P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP))
    (adicFiniteOrdinaryUnitComplex f)
    (fun P ↦ by
      ext q
      simp only [Adjunction.mapHomologicalComplex_unit_app_f, adicFiniteAdjunction_unit]
      rfl)

/-- The canonical derived tensor unit, with the K-flat normalization retained.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteUnit {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    𝟭 (ConstantCompletion.D R) ⟶ extend f ⋙ dres f :=
  (adicFiniteUnit_existsUnique f).exists.choose

end

@[no_expose]
private def adicFiniteCompositeAdjunction {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) : change f ⋙ change g ⊣ res (f ≫ g) :=
  (adicFiniteAdjunction f).comp (adicFiniteAdjunction g)

private theorem adicFiniteCompositeAdjunction_homEquiv
    {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V)
    (M : Mod R) (N : Mod V) (a : (change f ⋙ change g).obj M ⟶ N) :
    (adicFiniteCompositeAdjunction f g).homEquiv M N a =
      adicFiniteHomEquiv f M ((res g).obj N)
        (adicFiniteHomEquiv g ((change f).obj M) N a) := by
  simp only [adicFiniteCompositeAdjunction]
  change (adicFiniteAdjunction f).homEquiv M _
    ((adicFiniteAdjunction g).homEquiv ((change f).obj M) N a) = _
  rw [adicFiniteAdjunction_homEquiv, adicFiniteAdjunction_homEquiv]

open scoped ChangeOfRings in
private theorem adicFiniteTensorSection_smul {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    tensorSection f M U s m = s • tensorSection f M U 1 m := by
  exact tensorSection_smul f M U s m

private theorem adicFiniteHomEquiv_apply_tensor {R S : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N)
    (U : Dᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    a.val.app U (tensorSection f M U s m) =
      s • (show N.val.obj U from (adicFiniteHomEquiv f M N a).val.app U m) := by
  rw [adicFiniteTensorSection_smul, adicFiniteHomEquiv_apply]
  exact (a.val.app U).hom.map_smul s _

attribute [local irreducible] adicFiniteCompositeAdjunction

/-- Ordinary tensor associativity fixed by pure tensors.
Proof: balancing sends v tensor (s tensor m) to v*g(s) tensor m, with inverse
v tensor m mapped to v tensor (1 tensor m). The formulas respect restrictions
and sheafification. Pure tensors generate locally, proving uniqueness.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteChangeComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : change f ⋙ change g ≅ change (f ≫ g),
      ∀ (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (v : V.obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (tensorSection g ((change f).obj M) U v (tensorSection f M U s m)) =
            tensorSection (f ≫ g) M U (v * (g.hom.app U) s) m := by
  let adj := adicFiniteCompositeAdjunction f g
  let e : change f ⋙ change g ≅ change (f ≫ g) :=
    adj.leftAdjointUniq (adicFiniteAdjunction (f ≫ g))
  have he0 (M : Mod R) (U : Dᵒᵖ) (m : M.val.obj U) :
      (e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)) =
          tensorSection (f ≫ g) M U 1 m := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj
      (adicFiniteAdjunction (f ≫ g)) M
    rw [← Adjunction.homEquiv_id] at h
    change (adicFiniteCompositeAdjunction f g).homEquiv M _ (e.hom.app M) = _ at h
    rw [adicFiniteCompositeAdjunction_homEquiv, adicFiniteAdjunction_homEquiv] at h
    have hh := congrArg (fun z ↦ z.val.app U m) h
    have h₁ := adicFiniteHomEquiv_apply f M ((res g).obj ((change (f ≫ g)).obj M))
      (adicFiniteHomEquiv g ((change f).obj M) ((change (f ≫ g)).obj M) (e.hom.app M)) U m
    have h₂ := adicFiniteHomEquiv_apply g ((change f).obj M) ((change (f ≫ g)).obj M)
      (e.hom.app M) U (tensorSection f M U 1 m)
    have h₃ := adicFiniteHomEquiv_apply (f ≫ g) M ((change (f ≫ g)).obj M) (𝟙 _) U m
    exact (h₁.trans h₂).symm.trans (hh.trans h₃)
  have he : ∀ (M : Mod R) (U : Dᵒᵖ) (s : S.obj.obj U) (v : V.obj.obj U)
      (m : M.val.obj U), (e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U v (tensorSection f M U s m)) =
          tensorSection (f ≫ g) M U (v * (g.hom.app U) s) m := by
    intro M U s v m
    erw [adicFiniteHomEquiv_apply_tensor g ((change f).obj M)
      ((change (f ≫ g)).obj M) (e.hom.app M) U v (tensorSection f M U s m)]
    erw [adicFiniteTensorSection_smul f M U s m]
    erw [(adicFiniteHomEquiv g _ _ (e.hom.app M)).val.app U |>.hom.map_smul]
    erw [adicFiniteHomEquiv_apply]
    change v • ((g.hom.app U s) •
      ((e.hom.app M).val.app U
        (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)))) = _
    rw [he0, smul_smul, ← adicFiniteTensorSection_smul]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adicFiniteHomEquiv g ((change f).obj M) _).injective
  apply (adicFiniteHomEquiv f M _).injective
  apply SheafOfModules.hom_ext
  ext U m
  simp only [adicFiniteHomEquiv_apply]
  change (e'.hom.app M).val.app U
      (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m)) =
    (e.hom.app M).val.app U
      (tensorSection g ((change f).obj M) U 1 (tensorSection f M U 1 m))
  rw [he', he0, map_one, mul_one]

/-- The ordinary balancing isomorphism, uniquely fixed by its pure-tensor formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteChangeComp {R S V : Sheaf T CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) :
    change f ⋙ change g ≅ change (f ≫ g) :=
  (adicFiniteChangeComp_existsUnique f g).exists.choose

section

attribute [local irreducible] change pull

private theorem adicFiniteDerivedComparison
    {A B : Type*} [Category A] [Category B] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ B) (L G : DerivedCategory A ⥤ B)
    (ε : DerivedCategory.Q ⋙ L ⟶ F) (β : DerivedCategory.Q ⋙ G ⟶ F)
    (hres : ∀ P : CochainComplex A ℤ,
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ P),
        QuasiIso s ∧ IsIso (ε.app Y) ∧ IsIso (β.app Y)) :
    ∃ i : G ≅ L, ∀ P : CochainComplex A ℤ,
      i.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P = β.app P := by
  let P (X : CochainComplex A ℤ) := IsIso (ε.app X) ∧ IsIso (β.app X)
  have hP (X : CochainComplex A ℤ) :
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s := by
    obtain ⟨Y, s, hs, hε, hβ⟩ := hres X
    exact ⟨Y, s, ⟨hε, hβ⟩, hs⟩
  obtain ⟨i, hi⟩ := resolving_comparison_iso G L F P hP β ε
    (fun _ h ↦ h.2) (fun _ h ↦ h.1)
  refine ⟨i, ?_⟩
  intro X
  obtain ⟨Y, s, hY, hs⟩ := hP X
  let := hs
  apply (cancel_epi (G.map (DerivedCategory.Q.map s))).1
  calc
    _ = (i.hom.app (DerivedCategory.Q.obj Y) ≫ L.map (DerivedCategory.Q.map s)) ≫
        ε.app X := by
      rw [← Category.assoc, i.hom.naturality]
    _ = (i.hom.app (DerivedCategory.Q.obj Y) ≫ ε.app Y) ≫ F.map s := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ i.hom.app (DerivedCategory.Q.obj Y) ≫ k) (ε.naturality s)
    _ = β.app Y ≫ F.map s := by rw [hi Y hY]
    _ = G.map (DerivedCategory.Q.map s) ≫ β.app X := (β.naturality s).symm

private theorem adicFiniteCompositionComparison
    {M C₁ C₂ D₁ D₂ : Type*} [Category M] [Abelian M] [HasDerivedCategory M]
    [Category C₁] [Category C₂] [Preadditive C₁] [Preadditive C₂]
    [Category D₁] [Category D₂]
    (r : M ⥤ C₁) (s : C₁ ⥤ C₂) (c : M ⥤ C₂)
    [r.Additive] [s.Additive] [c.Additive]
    (q₁ : CochainComplex C₁ ℤ ⥤ D₁) (q₂ : CochainComplex C₂ ℤ ⥤ D₂)
    (dr : DerivedCategory M ⥤ D₁) (ds : D₁ ⥤ D₂) (dt : DerivedCategory M ⥤ D₂)
    (α : DerivedCategory.Q ⋙ dr ⟶ r.mapHomologicalComplex (.up ℤ) ⋙ q₁)
    (β : q₁ ⋙ ds ⟶ s.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (γ : r ⋙ s ≅ c) (δ : DerivedCategory.Q ⋙ dt ⟶ c.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (P : CochainComplex M ℤ → Prop)
    (hres : ∀ X : CochainComplex M ℤ,
      ∃ (Y : CochainComplex M ℤ) (f : Y ⟶ X), P Y ∧ QuasiIso f)
    (hα : ∀ X, P X → IsIso (α.app X))
    (hβ : ∀ X, P X → IsIso (β.app ((r.mapHomologicalComplex (.up ℤ)).obj X)))
    (hδ : ∀ X, P X → IsIso (δ.app X)) :
    ∃ i : dr ⋙ ds ≅ dt,
      (∀ X, i.hom.app (DerivedCategory.Q.obj X) ≫ δ.app X =
        ds.map (α.app X) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.map ((Functor.mapHomologicalComplexCompIso γ (.up ℤ)).hom.app X)) ∧
      ∀ j : dr ⋙ ds ≅ dt,
        (∀ X, P X → j.hom.app (DerivedCategory.Q.obj X) ≫ δ.app X =
          ds.map (α.app X) ≫ β.app ((r.mapHomologicalComplex (.up ℤ)).obj X) ≫
          q₂.map ((Functor.mapHomologicalComplexCompIso γ (.up ℤ)).hom.app X)) → j = i := by
  let B : DerivedCategory.Q ⋙ (dr ⋙ ds) ⟶ c.mapHomologicalComplex (.up ℤ) ⋙ q₂ :=
    Functor.whiskerRight α ds ≫ Functor.whiskerLeft (r.mapHomologicalComplex (.up ℤ)) β ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso γ (.up ℤ)).hom q₂
  obtain ⟨i, hi⟩ := adicFiniteDerivedComparison
    (c.mapHomologicalComplex (.up ℤ) ⋙ q₂) dt (dr ⋙ ds) δ B (fun X ↦ by
    obtain ⟨Y, f, hY, hf⟩ := hres X
    let := hα Y hY
    let := hβ Y hY
    refine ⟨Y, f, hf, hδ Y hY, ?_⟩
    dsimp only [B, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance)
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Iso.ext
  apply resolving_nat_ext P hres j.hom i.hom
  intro Y hY
  let := hδ Y hY
  apply (cancel_mono (δ.app Y)).1
  exact (hj Y hY).trans (hi Y).symm

attribute [local irreducible] Functor.mapHomologicalComplex

/-- The explicit normalization predicate, kept as a named API so choosing its unique
witness does not expand the cochain comparison formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteExtendCompFormula {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V)
    (e : extend f ⋙ extend g ≅ extend (f ≫ g)) : Prop :=
  ∀ P : Cx R, CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
        e.hom.app ((Q R).obj P) ≫ (extendComparison (f ≫ g)).app P =
          (extend g).map ((extendComparison f).app P) ≫
            (extendComparison g).app
              (((change f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            (Q V).map ((Functor.mapHomologicalComplexCompIso (adicFiniteChangeComp f g)
              (ComplexShape.up ℤ)).hom.app P)

/-- Derived tensor associativity fixed by the ordinary balancing comparison.
Proof: scalar extension preserves K-flatness by balancing against each acyclic test
complex. Hence on K-flat models all three universal comparisons are invertible.
The displayed composite descends uniquely through localization, and its inverse
is the inverse ordinary balancing composite.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteExtendComp_existsUnique {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) :
    ∃! e : extend f ⋙ extend g ≅ extend (f ≫ g),
      adicFiniteExtendCompFormula f g e := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let : Abelian (Mod S) :=
    { (inferInstance : Abelian (Mod S)) with toPreadditive := inferInstance }
  let : Abelian (Mod V) :=
    { (inferInstance : Abelian (Mod V)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard (Mod V)
  let P (K : Cx R) := AdicFiniteGood R K
  have hres (K : Cx R) : ∃ (Y : Cx R) (q : Y ⟶ K), P Y ∧ QuasiIso q :=
    adicFiniteGood_resolution K
  have hf (K : Cx R) (hK : P K) : IsIso ((extendComparison f).app K) :=
    adicFiniteExtension_isIso f K hK.kflat
  have hg (K : Cx R) (hK : P K) :
      IsIso ((extendComparison g).app
        (((change f).mapHomologicalComplex (.up ℤ)).obj K)) :=
    adicFiniteExtension_isIso g _ (adicFiniteGood_change f K hK).kflat
  have hfg (K : Cx R) (hK : P K) : IsIso ((extendComparison (f ≫ g)).app K) :=
    adicFiniteExtension_isIso (f ≫ g) K hK.kflat
  obtain ⟨e, he, hu⟩ := adicFiniteCompositionComparison
      (change f) (change g) (change (f ≫ g))
      (Q S) (Q V) (extend f) (extend g) (extend (f ≫ g))
      (extendComparison f) (extendComparison g)
      (adicFiniteChangeComp f g) (extendComparison (f ≫ g)) P hres hf hg hfg
  refine ⟨e, fun K _ ↦ he K, ?_⟩
  intro e' he'
  apply hu e'
  intro K hK
  exact he' K ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mpr hK.kflat)

/-- Canonical derived balancing for a specified composite coefficient map.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteExtendComp {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (e : h = f ≫ g) :
    extend f ⋙ extend g ≅ extend h :=
  (adicFiniteExtendComp_existsUnique f g).exists.choose ≪≫
    eqToIso (congrArg extend e.symm)

end

/-- The algebraic lift of the recorded geometric comparison. Its universal specification
retains ring operations, module actions and the natural constant-coefficient isomorphisms.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteComparisonData (X : Scheme.{u}) :
    InverseImageData (smallModelComparisonPullback.{u, v} X) :=
  letI := smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  Classical.choice (inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X) (smallModelComparisonPushforward.{u, v} X)
    (smallModelProEtaleComparison.{u, v} X))

attribute [local irreducible] adicFiniteComparisonData

/-- The ordinary comparison inverse image with its canonical constant-ring map.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteOrdinaryPullback (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      Mod (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  pull (adicFiniteComparisonData.{u, v} X) (constantMap (adicFiniteComparisonData.{u, v} X) A)

/-- Additivity of the recorded module inverse image.
Source: Stacks Tags 03D2 and 09C2
(auxiliary; not a blueprint node). -/
instance adicFiniteOrdinaryPullbackAdditive (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (adicFiniteOrdinaryPullback.{u, v} X A).Additive :=
  pull_additive (adicFiniteComparisonData.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)

/-- The existing universal derived inverse image, shared by its functor and comparison.
This is the same derivedPull construction with its specified K-flat computation.
Source: Stacks Tags 06YY and 09C2
(auxiliary; not a blueprint node). -/
def adicFinitePullbackData (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    DerivedPull (adicFiniteComparisonData.{u, v} X)
      (constantMap (adicFiniteComparisonData.{u, v} X) A) :=
  derivedPull (hL := smallModelComparisonPullback_preservesFiniteLimits.{u, v} X)
    (adicFiniteComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) A)

attribute [local irreducible] adicFinitePullbackData

/-- The derived inverse image of the recorded geometric comparison, with its universal
K-flat computation, on constant coefficients of arbitrary size.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFinitePullback (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] :
    ConstantCompletion.D (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
      ConstantCompletion.D (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (adicFinitePullbackData.{u, v} X A).functor

/-- The universally specified comparison on complexes for the derived inverse image.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFinitePullbackComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Q (constant (smallModelComparisonEtaleTopology.{u, v} X) A) ⋙ adicFinitePullback.{u, v} X A ⟶
      (adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Q (constant (coefficientProEtaleModelTopology.{u, v} X) A) :=
  (adicFinitePullbackData.{u, v} X A).comparison

/-- The canonical map of constant coefficient sheaves.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteConstantMap {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D) :
    constant T R ⟶ constant T S :=
  (constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f)

section

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

-- The two routes round a coefficient square have the same right adjoint.
-- Identify their left adjoints, keeping track of tensor insertion throughout.
@[no_expose]
private noncomputable def adicFiniteRingData
    {C E : Type w} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
    (V : Sheaf JD (Type w) ⥤ Sheaf JC (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R : Sheaf JC CommRingCat.{w}} {S : Sheaf JD CommRingCat.{w}}
    (c : F.rings.obj R ⟶ S) :
    RingedToposMorphism.RingData (siteModuleRings S) (siteModuleRings R) := by
  let AI := F.algebra R
  exact
    { inverse := L
      direct := V
      adj := adj
      leftExact := inferInstance
      ringMap := AI.ringUnderlying.hom ≫ (sheafCompose JD (CategoryTheory.forget CommRingCat)).map c
      ring_zero := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 0
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringZero T z hz U t)).trans (map_zero _)
      ring_one := by
        intro T z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) = 1
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringOne T z hz U t)).trans (map_one _)
      ring_add := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) +
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringAdd T x y z hz U t)).trans (map_add _ _ _)
      ring_mul := by
        intro T x y z hz U t
        change (c.hom.app U).hom
          (AI.ringUnderlying.hom.hom.app U ((L.map z).hom.app U t)) =
          (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map x).hom.app U t)) *
            (c.hom.app U).hom
              (AI.ringUnderlying.hom.hom.app U ((L.map y).hom.app U t))
        exact (congrArg (fun a ↦ (c.hom.app U).hom a)
          (AI.ringMul T x y z hz U t)).trans (map_mul _ _ _) }

private theorem adicFiniteTensorUnit_eq
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (c : R ⟶ S) (M : Mod R) :
    SheafOfModules.tensorUnit c M = insertion c M := by
  ext U m
  exact (SheafOfModules.tensorUnit_apply c M U m).trans
    ((insertion_existsUnique c M).exists.choose_spec U m).symm

private theorem adicFiniteAdjunction_underlying
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S)
    (M : Mod R) (N : Mod S) (a : (change f).obj M ⟶ N) :
    (underlying R).map ((adicFiniteAdjunction f).homEquiv M N a) =
      insertion f M ≫ (underlying S).map a := by
  rw [adicFiniteAdjunction_homEquiv]
  ext U m
  change (adicFiniteHomEquiv f M N a).val.app U m =
    a.val.app U ((insertion f M).hom.app U m)
  rw [show (insertion f M).hom.app U m = tensorSection f M U 1 m from
    (insertion_existsUnique f M).exists.choose_spec U m]
  exact adicFiniteHomEquiv_apply f M N a U m

private theorem adicFiniteInsertion_apply
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (insertion f M).hom.app U m = tensorSection f M U 1 m :=
  (insertion_existsUnique f M).exists.choose_spec U m

private theorem adicFiniteChangeComp_insertion
    {C : Type w} [SmallCategory C] {JC : GrothendieckTopology C}
    {R S V : Sheaf JC CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ V) (M : Mod R) :
    insertion f M ≫ insertion g ((change f).obj M) ≫
      (underlying V).map ((adicFiniteChangeComp f g).hom.app M) = insertion (f ≫ g) M := by
  ext U m
  change ((adicFiniteChangeComp f g).hom.app M).val.app U
      ((insertion g _).hom.app U ((insertion f _).hom.app U m)) =
    (insertion (f ≫ g) _).hom.app U m
  erw [adicFiniteInsertion_apply, adicFiniteInsertion_apply, adicFiniteInsertion_apply]
  simpa only [map_one, mul_one] using!
    (adicFiniteChangeComp_existsUnique f g).exists.choose_spec M U 1 1 m

@[no_expose]
private def adicFiniteRestrictRingModules
    {C E : Type w} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
    (V : Sheaf JD (Type w) ⥤ Sheaf JC (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R S : Sheaf JC CommRingCat.{w}} {B : Sheaf JD CommRingCat.{w}}
    (f : R ⟶ S) (cB : F.rings.obj S ⟶ B) (c₀ : F.rings.obj R ⟶ B)
    (hs : L.map ((sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫
      (adicFiniteRingData V adj F cB).ringMap = (adicFiniteRingData V adj F c₀).ringMap)
    (md : (adicFiniteRingData V adj F cB).Modules) :
    (adicFiniteRingData V adj F c₀).Modules := by
  let dB := adicFiniteRingData V adj F cB
  let d₀ := adicFiniteRingData V adj F c₀
  let : md.modules.Additive := md.additive
  exact
    { modules := md.modules ⋙ res f
      additive := inferInstance
      underlying := md.underlying
      module_linear := by
        intro N T a x y z hz U t
        have h := md.module_linear N T
          (a ≫ (sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) x y z hz U t
        change _ = @Add.add (N.val.obj U) inferInstance
          (@SMul.smul (B.obj.obj U) (N.val.obj U) inferInstance
            ((L.map (a ≫ (sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫
              dB.ringMap).hom.app U t)
            (show N.val.obj U from
              ((dB.adj.homEquiv T _).symm (x ≫ md.underlying.hom.app N)).hom.app U t))
          (show N.val.obj U from
            ((dB.adj.homEquiv T _).symm (y ≫ md.underlying.hom.app N)).hom.app U t) at h
        erw [Functor.map_comp, Category.assoc, hs] at h
        exact h }

private theorem adicFiniteNormalizedAdjoints
    {C₀ C₁ W₀ W₁ : Type*} [Category C₀] [Category C₁] [Category W₀] [Category W₁]
    (L : W₀ ⥤ W₁) (V : W₁ ⥤ W₀) (adj : L ⊣ V)
    (U₀ : C₀ ⥤ W₀) [U₀.Faithful] (U₁ : C₁ ⥤ W₁)
    (G : C₁ ⥤ C₀) (e : G ⋙ U₀ ≅ U₁ ⋙ V)
    (F₀ F₁ : C₀ ⥤ C₁) (a₀ : F₀ ⊣ G) (a₁ : F₁ ⊣ G)
    (q₀ : ∀ M, L.obj (U₀.obj M) ⟶ U₁.obj (F₀.obj M))
    (q₁ : ∀ M, L.obj (U₀.obj M) ⟶ U₁.obj (F₁.obj M))
    (h₀ : ∀ M N (k : F₀.obj M ⟶ N), U₀.map (a₀.homEquiv M N k) ≫ e.hom.app N =
      adj.homEquiv _ _ (q₀ M ≫ U₁.map k))
    (h₁ : ∀ M N (k : F₁.obj M ⟶ N), U₀.map (a₁.homEquiv M N k) ≫ e.hom.app N =
      adj.homEquiv _ _ (q₁ M ≫ U₁.map k)) :
    ∃! i : F₀ ≅ F₁, ∀ M, q₀ M ≫ U₁.map (i.hom.app M) = q₁ M := by
  let i := a₀.leftAdjointUniq a₁
  have hi (M : C₀) : q₀ M ≫ U₁.map (i.hom.app M) = q₁ M := by
    apply (adj.homEquiv _ _).injective
    rw [← h₀]
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app a₀ a₁ M
    change a₀.homEquiv M _ (i.hom.app M) = _ at h
    rw [h, ← Adjunction.homEquiv_id]
    have hh := h₁ M _ (𝟙 _)
    rw [U₁.map_id, Category.comp_id] at hh
    exact hh
  refine ⟨i, hi, ?_⟩
  intro i' hi'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (a₀.homEquiv M _).injective
  apply U₀.map_injective
  apply (cancel_mono (e.hom.app _)).1
  rw [h₀, h₀]
  congr 1
  exact (hi' M).trans (hi M).symm

private theorem adicFiniteNormalizedTransport
    {C W E : Type*} [Category C] [Category W] [Category E]
    (U : E ⥤ W) (F₀ F₁ F₂ : C ⥤ E) (Z : C → W)
    (q₀ : ∀ M, Z M ⟶ U.obj (F₀.obj M))
    (q₁ : ∀ M, Z M ⟶ U.obj (F₁.obj M))
    (q₂ : ∀ M, Z M ⟶ U.obj (F₂.obj M))
    (j : F₀ ≅ F₁) (hj : ∀ M, q₀ M ≫ U.map (j.hom.app M) = q₁ M)
    (h : ∃! i : F₁ ≅ F₂, ∀ M, q₁ M ≫ U.map (i.hom.app M) = q₂ M) :
    ∃! i : F₀ ≅ F₂, ∀ M, q₀ M ≫ U.map (i.hom.app M) = q₂ M := by
  obtain ⟨i, hi, hu⟩ := h
  let e := j ≪≫ i
  have he (M : C) : q₀ M ≫ U.map (e.hom.app M) = q₂ M := by
    change q₀ M ≫ U.map (j.hom.app M ≫ i.hom.app M) = _
    rw [Functor.map_comp, ← Category.assoc, hj M, hi M]
  refine ⟨e, he, ?_⟩
  intro e' he'
  have hk : ∀ M, q₁ M ≫ U.map ((j.symm ≪≫ e').hom.app M) = q₂ M := by
    intro M
    rw [← hj M]
    change (q₀ M ≫ U.map (j.hom.app M)) ≫ U.map (j.inv.app M ≫ e'.hom.app M) = _
    calc
      _ = q₀ M ≫ U.map (j.hom.app M ≫ j.inv.app M ≫ e'.hom.app M) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = q₀ M ≫ U.map (e'.hom.app M) := by
        rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      _ = q₂ M := he' M
  have hki := hu (j.symm ≪≫ e') hk
  apply Iso.ext
  apply NatTrans.ext
  funext M
  change e'.hom.app M = j.hom.app M ≫ i.hom.app M
  have h := congrArg (fun z : F₁ ≅ F₂ ↦ j.hom.app M ≫ z.hom.app M) hki
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp] using h

private theorem adicFinitePullScalarSquare
    {C E : Type w} [SmallCategory C] [SmallCategory E]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology E}
    {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
    (V : Sheaf JD (Type w) ⥤ Sheaf JC (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    {R S : Sheaf JC CommRingCat.{w}} {A B : Sheaf JD CommRingCat.{w}}
    (f : R ⟶ S) (g : A ⟶ B) (cA : F.rings.obj R ⟶ A) (cB : F.rings.obj S ⟶ B)
    (hsq : F.rings.map f ≫ cB = cA ≫ g) :
    ∃! e : pull F cA ⋙ change g ≅ change f ⋙ pull F cB,
      ∀ M : Mod R,
        L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M) =
          pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) ≫
            (underlying B).map (e.hom.app M) := by
  let dB := adicFiniteRingData V adj F cB
  let d₀ := adicFiniteRingData V adj F (cA ≫ g)
  have hs : L.map ((sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫ dB.ringMap =
      d₀.ringMap := by
    change L.map ((sheafCompose JC (CategoryTheory.forget CommRingCat)).map f) ≫
      (F.algebra S).ringUnderlying.hom ≫
        (sheafCompose JD (CategoryTheory.forget CommRingCat)).map cB = _
    rw [← Category.assoc, F.ring_naturality f, Category.assoc,
      ← Functor.map_comp, hsq]
    rfl
  obtain ⟨md⟩ := SheafOfModules.ringData_inducedModules B S dB
  let : md.modules.Additive := md.additive
  let md₀ : d₀.Modules := adicFiniteRestrictRingModules V adj F f cB (cA ≫ g) hs md
  let b := dB.withModules md
  let b₀ := d₀.withModules md₀
  have hcB : (sheafCompose JD (CategoryTheory.forget CommRingCat)).map cB =
      (F.algebra S).ringUnderlying.inv ≫ b.ringMap := by
    change _ = _ ≫ ((F.algebra S).ringUnderlying.hom ≫ _)
    rw [Iso.inv_hom_id_assoc]
  have hc₀ : (sheafCompose JD (CategoryTheory.forget CommRingCat)).map (cA ≫ g) =
      (F.algebra R).ringUnderlying.inv ≫ b₀.ringMap := by
    change _ = _ ≫ ((F.algebra R).ringUnderlying.hom ≫ _)
    rw [Iso.inv_hom_id_assoc]
  obtain ⟨aB, haB⟩ := supplied_module_adjunction b (F.rings.obj S) (F.algebra S) cB hcB
  obtain ⟨a₀, ha₀⟩ := supplied_module_adjunction b₀ (F.rings.obj R)
    (F.algebra R) (cA ≫ g) hc₀
  change pull F cB ⊣ md.modules at aB
  change pull F (cA ≫ g) ⊣ md.modules ⋙ res f at a₀
  have hB (M : Mod S) (N : Mod B) (k : (pull F cB).obj M ⟶ N) :
      (underlying S).map (aB.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (pullInsertion F cB M ≫ (underlying B).map k) := by
    simpa only [pullInsertion, adicFiniteTensorUnit_eq, Category.assoc] using! haB M N k
  have h₀ (M : Mod R) (N : Mod B) (k : (pull F (cA ≫ g)).obj M ⟶ N) :
      (underlying R).map (a₀.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (pullInsertion F (cA ≫ g) M ≫ (underlying B).map k) := by
    simpa only [pullInsertion, adicFiniteTensorUnit_eq, Category.assoc] using! ha₀ M N k
  let a : change f ⋙ pull F cB ⊣ b₀.modules := (adicFiniteAdjunction f).comp aB
  have ha (M : Mod R) (N : Mod B) (k : (change f ⋙ pull F cB).obj M ⟶ N) :
      (underlying R).map (a.homEquiv M N k) ≫ md.underlying.hom.app N =
        adj.homEquiv _ _ (L.map (insertion f M) ≫
          pullInsertion F cB ((change f).obj M) ≫ (underlying B).map k) := by
    change (underlying R).map ((adicFiniteAdjunction f).homEquiv M _
      (aB.homEquiv _ N k)) ≫ md.underlying.hom.app N = _
    have h₁ := adicFiniteAdjunction_underlying f M _ (aB.homEquiv _ N k)
    have h₂ := hB ((change f).obj M) N k
    exact (congrArg (· ≫ md.underlying.hom.app N) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (insertion f M ≫ ·) h₂).trans
          (adj.homEquiv_naturality_left _ _).symm))
  have hnormalized : ∃! i : pull F (cA ≫ g) ≅ change f ⋙ pull F cB,
      ∀ M : Mod R, pullInsertion F (cA ≫ g) M ≫ (underlying B).map (i.hom.app M) =
        L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M) := by
    apply adicFiniteNormalizedAdjoints L V adj (underlying R) (underlying B)
      b₀.modules md.underlying (pull F (cA ≫ g)) (change f ⋙ pull F cB) a₀ a
      (fun M ↦ pullInsertion F (cA ≫ g) M)
      (fun M ↦ L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M)) h₀
    intro M N k
    simpa only [Category.assoc] using! ha M N k
  let j : pull F cA ⋙ change g ≅ pull F (cA ≫ g) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.algebra R).modules (adicFiniteChangeComp cA g)
  have hj (M : Mod R) :
      pullInsertion F cA M ≫ insertion g ((pull F cA).obj M) ≫
        (underlying B).map (j.hom.app M) = pullInsertion F (cA ≫ g) M := by
    change (F.algebra R).moduleUnderlying.inv.app M ≫
        insertion cA ((F.algebra R).modules.obj M) ≫
        insertion g ((change cA).obj ((F.algebra R).modules.obj M)) ≫
        (underlying B).map ((adicFiniteChangeComp cA g).hom.app
          ((F.algebra R).modules.obj M)) =
      (F.algebra R).moduleUnderlying.inv.app M ≫
        insertion (cA ≫ g) ((F.algebra R).modules.obj M)
    exact congrArg ((F.algebra R).moduleUnderlying.inv.app M ≫ ·)
      (adicFiniteChangeComp_insertion cA g ((F.algebra R).modules.obj M))
  obtain ⟨e, he, hu⟩ := adicFiniteNormalizedTransport (underlying B)
    (pull F cA ⋙ change g) (pull F (cA ≫ g)) (change f ⋙ pull F cB)
    (fun M ↦ L.obj ((underlying R).obj M))
    (fun M ↦ pullInsertion F cA M ≫ insertion g ((pull F cA).obj M))
    (fun M ↦ pullInsertion F (cA ≫ g) M)
    (fun M ↦ L.map (insertion f M) ≫ pullInsertion F cB ((change f).obj M))
    j (fun M ↦ by simpa only [Category.assoc] using hj M) hnormalized
  refine ⟨e, ?_, ?_⟩
  · intro M
    simpa only [Category.assoc] using (he M).symm
  · intro e' he'
    apply hu e'
    intro M
    simpa only [Category.assoc] using (he' M).symm

end

/-- The explicit normalization predicate, kept as a named API so choosing its unique
witness does not expand the cochain comparison formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteOrdinaryComparisonFormula (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B)
    (e : adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X B) : Prop :=
  ∀ M : Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        (smallModelComparisonPullback.{u, v} X).map
            (insertion (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) M) ≫
          pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) B)
            ((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).obj M) =
        pullInsertion (adicFiniteComparisonData.{u, v} X)
            (constantMap (adicFiniteComparisonData.{u, v} X) A) M ≫
          insertion (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
            ((adicFiniteOrdinaryPullback.{u, v} X A).obj M) ≫
          (underlying (constant (coefficientProEtaleModelTopology.{u, v} X) B)).map
            (e.hom.app M)

/-- Ordinary comparison commutes with scalar extension, normalized by tensor insertion.
Proof: inverse image preserves the tensor coequalizer. Both sides send a scalar and
a module section to the same sheafified pure tensor. The displayed insertion equation
determines the isomorphism on local generators; the inverse balancing map gives its inverse.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteOrdinaryComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X B,
      adicFiniteOrdinaryComparisonFormula X f e := by
  let : PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) :=
    smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  exact adicFinitePullScalarSquare
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (adicFiniteComparisonData.{u, v} X)
    (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
    (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
    (constantMap (adicFiniteComparisonData.{u, v} X) A)
    (constantMap (adicFiniteComparisonData.{u, v} X) B)
    ((adicFiniteComparisonData.{u, v} X).constants.hom.naturality (CommRingCat.ofHom f))

/-- The ordinary scalar/pullback comparison with its insertion normalization.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteOrdinaryComparison (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    adicFiniteOrdinaryPullback.{u, v} X A ⋙
      change (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
    change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
      adicFiniteOrdinaryPullback.{u, v} X B :=
  (adicFiniteOrdinaryComparison_existsUnique.{u, v} X f).exists.choose

section

attribute [local irreducible] change pull

attribute [local irreducible] Functor.mapHomologicalComplex

private theorem adicFinitePullChangeComparison
    {E : Type w} [SmallCategory E] {TE : GrothendieckTopology E}
    {L : Sheaf T (Type w) ⥤ Sheaf TE (Type w)} (F : InverseImageData L)
    (U : Sheaf TE (Type w) ⥤ Sheaf T (Type w)) (adj : L ⊣ U)
    [PreservesFiniteLimits L] {R S : Sheaf T CommRingCat.{w}}
    {V W : Sheaf TE CommRingCat.{w}} (f : R ⟶ S) (g : V ⟶ W)
    (cA : F.rings.obj R ⟶ V) (cB : F.rings.obj S ⟶ W)
    (pa : DerivedPull F cA) (pb : DerivedPull F cB)
    (o : pull F cA ⋙ change g ≅ change f ⋙ pull F cB) :
    ∃! e : pa.functor ⋙ extend g ≅ extend f ⋙ pb.functor,
      ∀ P : Cx R, P.IsKFlatIndependentCoefficients →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        e.hom.app ((Q R).obj P) ≫ pb.functor.map ((extendComparison f).app P) ≫
          pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj P) =
        (extend g).map (pa.comparison.app P) ≫
          (extendComparison g).app (((pull F cA).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (Q W).map ((adicFiniteComplexSquare o).hom.app P) := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let : Abelian (Mod S) :=
    { (inferInstance : Abelian (Mod S)) with toPreadditive := inferInstance }
  let : Abelian (Mod V) :=
    { (inferInstance : Abelian (Mod V)) with toPreadditive := inferInstance }
  let : Abelian (Mod W) :=
    { (inferInstance : Abelian (Mod W)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard (Mod V)
  let := HasDerivedCategory.standard (Mod W)
  let P (K : Cx R) := AdicFiniteGood R K
  have hres (K : Cx R) : ∃ (Y : Cx R) (q : Y ⟶ K), P Y ∧ QuasiIso q :=
    adicFiniteGood_resolution K
  have hpa (K : Cx R) (hK : P K) : IsIso (pa.comparison.app K) :=
    adicFinitePull_isIso pa K hK
  have hleft (K : Cx R) (hK : P K) :
      IsIso ((extendComparison g).app
        (((pull F cA).mapHomologicalComplex (.up ℤ)).obj K)) :=
    adicFiniteExtension_isIso g _ (adicFiniteGood_pull F U adj cA K hK).kflat
  have hf (K : Cx R) (hK : P K) : IsIso ((extendComparison f).app K) :=
    adicFiniteExtension_isIso f K hK.kflat
  have hpb (K : Cx R) (hK : P K) :
      IsIso (pb.comparison.app (((change f).mapHomologicalComplex (.up ℤ)).obj K)) :=
    adicFinitePull_isIso pb _ (adicFiniteGood_change f K hK)
  apply adicFiniteUniqueGuard (G := P)
  · intro K hk hf
    exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mp hk, hf⟩
  · intro K hK
    exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).mpr hK.kflat,
      hK.flat⟩
  · exact adicFiniteModuleSquare
      (Q V) (Q S) (Q W) (pull F cA) (pull F cB) (change g) (change f)
      pa.comparison (extendComparison g) o (extendComparison f) pb.comparison
      P hres hpa hleft hf hpb

/-- The explicit normalization predicate, kept as a named API so choosing its unique
witness does not expand the cochain comparison formula.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteComparisonFormula (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B)
    (e : adicFinitePullback.{u, v} X A ⋙
        extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFinitePullback.{u, v} X B) : Prop :=
  ∀ P : Cx (constant (smallModelComparisonEtaleTopology.{u, v} X) A),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := constant (smallModelComparisonEtaleTopology.{u, v} X) A) P →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        e.hom.app ((Q _).obj P) ≫
          (adicFinitePullback.{u, v} X B).map
            ((extendComparison (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).app P) ≫
          (adicFinitePullbackComparison.{u, v} X B).app
            (((change (adicFiniteConstantMap f
              (smallModelComparisonEtaleTopology.{u, v} X))).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) =
        (extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))).map
            ((adicFinitePullbackComparison.{u, v} X A).app P) ≫
          (extendComparison (adicFiniteConstantMap f
            (coefficientProEtaleModelTopology.{u, v} X))).app
            (((adicFiniteOrdinaryPullback.{u, v} X A).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          (Q _).map ((adicFiniteComplexSquare
            (adicFiniteOrdinaryComparison.{u, v} X f)).hom.app P)

/-- The derived scalar/pullback comparison is specified on flat-term K-flat models.
Proof: exact geometric inverse image preserves flat terms and K-flatness. Scalar
extension preserves K-flatness. All four universal comparisons in the displayed
square are therefore invertible. Descend the uniquely normalized ordinary comparison
through K-flat localization; the ordinary inverse descends too, and uniqueness follows
from the universal localization property.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
theorem adicFiniteComparison_existsUnique (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    ∃! e : adicFinitePullback.{u, v} X A ⋙
        extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
      extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFinitePullback.{u, v} X B,
      adicFiniteComparisonFormula X f e := by
  let : PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) :=
    smallModelComparisonPullback_preservesFiniteLimits.{u, v} X
  exact adicFinitePullChangeComparison
    (adicFiniteComparisonData.{u, v} X) (smallModelComparisonPushforward.{u, v} X)
    (smallModelProEtaleComparison.{u, v} X)
    (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
    (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
    (constantMap (adicFiniteComparisonData.{u, v} X) A)
    (constantMap (adicFiniteComparisonData.{u, v} X) B)
    (adicFinitePullbackData.{u, v} X A)
    (adicFinitePullbackData.{u, v} X B)
    (adicFiniteOrdinaryComparison.{u, v} X f)

/-- The canonical derived scalar/pullback balancing comparison.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteComparison (X : Scheme.{u})
    {A B : Type (max v (u + 1))} [CommRing A] [CommRing B] (f : A →+* B) :
    adicFinitePullback.{u, v} X A ⋙
      extend (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)) ≅
    extend (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
      adicFinitePullback.{u, v} X B :=
  (adicFiniteComparison_existsUnique.{u, v} X f).exists.choose

end

/-- The existing positive-power quotient, with no change of coefficient ring.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
abbrev adicFiniteCoeff {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :=
  A ⧸ J ^ (n + 1)

/-- The quotient homomorphism at positive exponent n+1.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteQuotient {A : Type w} [CommRing A] (J : Ideal A) (n : ℕ) :
    A →+* adicFiniteCoeff J n := Ideal.Quotient.mk _

/-- The canonical quotient factor homomorphism.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteFactor {A : Type w} [CommRing A] (J : Ideal A)
    {m n : ℕ} (h : n ≤ m) : adicFiniteCoeff J m →+* adicFiniteCoeff J n :=
  Ideal.Quotient.factorPow J (Nat.add_le_add_right h 1)

/-- The quotient-factor identity is the existing ideal quotient identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteQuotientComp {A : Type w} [CommRing A] (J : Ideal A)
    {m n : ℕ} (h : n ≤ m) :
    adicFiniteQuotient J n = (adicFiniteFactor J h).comp (adicFiniteQuotient J m) :=
  (Ideal.Quotient.factor_comp_mk
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))).symm

/-- The quotient-factor cocycle is the existing factor composition identity.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteFactorComp {A : Type w} [CommRing A] (J : Ideal A)
    {r m n : ℕ} (hnm : n ≤ m) (hmr : m ≤ r) :
    adicFiniteFactor J (hnm.trans hmr) =
      (adicFiniteFactor J hnm).comp (adicFiniteFactor J hmr) :=
  (Ideal.Quotient.factor_comp
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hmr 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).symm

/-- Scalar extension in the existing standard localization of a small ringed site.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteExtension {A B : Type w} [CommRing A] [CommRing B]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D) (f : A →+* B) :
    ConstantCompletion.D (constant T A) ⥤ ConstantCompletion.D (constant T B) :=
  extend (adicFiniteConstantMap f T)

/-- Functoriality of the existing constant-sheaf construction on ring homomorphisms.
Source: Stacks Tags 06YY and 09C2
(auxiliary; not a blueprint node). -/
def adicFiniteConstantComp {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteConstantMap h T = adicFiniteConstantMap f T ≫ adicFiniteConstantMap g T :=
  (congrArg (fun k ↦ adicFiniteConstantMap k T) e).trans
    ((constantSheaf T CommRingCat.{w}).map_comp
      (CommRingCat.ofHom f) (CommRingCat.ofHom g))

/-- Canonical scalar reassociation for a specified equality of constant ring maps.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteExtensionComp {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    {D : Type w} [SmallCategory D] (T : GrothendieckTopology D)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteExtension T f ⋙ adicFiniteExtension T g ≅ adicFiniteExtension T h :=
  adicFiniteExtendComp (adicFiniteConstantMap f T) (adicFiniteConstantMap g T)
    (adicFiniteConstantMap h T)
    (adicFiniteConstantComp T f g h e)

/-- The standard derived category of the constant pro-etale coefficient ring on the
equivalent coefficient-sized site.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
abbrev adicFiniteAmbient (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  ConstantCompletion.D (constant (coefficientProEtaleModelTopology.{u, v} X) A)

/-- Local derived completeness for the kernel of the actual residue quotient.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteComplete (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) : Prop :=
  IsComplete (quotient (coefficientProEtaleModelTopology.{u, v} X) A J 0) N

/-- The existing etale derived category over a positive quotient on the equivalent model.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
abbrev adicFiniteEtale (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (n : ℕ) :=
  ConstantCompletion.D
    (finite (smallModelComparisonEtaleTopology.{u, v} X) A J n)

/-- Derived tensor with the actual positive quotient, using the universal scalar extension.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteReduction (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteAmbient.{u, v} X (adicFiniteCoeff J n) :=
  (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteQuotient J n)).obj N

/-- Canonical balancing after a repeated quotient reduction.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteRho (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) {m n : ℕ} (h : n ≤ m) :
    (adicFiniteExtension (coefficientProEtaleModelTopology.{u, v} X)
      (adicFiniteFactor J h)).obj (adicFiniteReduction.{u, v} X J N m) ≅
        adicFiniteReduction.{u, v} X J N n :=
  (adicFiniteExtensionComp (coefficientProEtaleModelTopology.{u, v} X)
    (adicFiniteQuotient J m) (adicFiniteFactor J h) (adicFiniteQuotient J n)
    (adicFiniteQuotientComp J h)).app N

/-- The quotient reduction with coefficients restricted to the original ring.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteUnderlying (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) : adicFiniteAmbient.{u, v} X A :=
  (dres (quotient (coefficientProEtaleModelTopology.{u, v} X) A J n)).obj
    (adicFiniteReduction.{u, v} X J N n)

/-- The actual quotient transition, from the normalized derived tensor unit, balancing
and exact restriction composition. No transition map is supplied as a parameter.
Source: Stacks Tags 06YY, 09C2 and 09AL
(auxiliary; not a blueprint node). -/
def adicFiniteTransition (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    adicFiniteUnderlying.{u, v} X J N (n + 1) ⟶ adicFiniteUnderlying.{u, v} X J N n :=
  let T := coefficientProEtaleModelTopology.{u, v} X
  let f := quotient T A J (n + 1)
  let g := adicFiniteConstantMap (adicFiniteFactor J (Nat.le_succ n)) T
  (dres f).map ((adicFiniteUnit g).app (adicFiniteReduction.{u, v} X J N (n + 1)) ≫
      (dres g).map (adicFiniteRho.{u, v} X J N (Nat.le_succ n)).hom) ≫
    (adicFiniteDresComp f g).hom.app (adicFiniteReduction.{u, v} X J N n) ≫
    (eqToIso (congrArg (fun k ↦ (dres k).obj (adicFiniteReduction.{u, v} X J N n))
      (adicFiniteConstantComp T (adicFiniteQuotient J (n + 1))
        (adicFiniteFactor J (Nat.le_succ n)) (adicFiniteQuotient J n)
        (adicFiniteQuotientComp J (Nat.le_succ n))).symm)).hom

end AlgebraicGeometry.Scheme
