/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Relative torsor extensions and normalized supported cohomology

The comparison is uniquely specified on every resolution cocycle by evaluation at one
and the inclusion into the signed cone with zero open coordinate. The relative torsor
class is the negative of the existing raw lifting-cocycle equivalence.

## References

* Stacks Project, Tags 03AJ, 06XR, 06XV and 0A45, relative refinement
* Stacks Tag 03AJ, relative refinement using Tag 0A45
* Stacks Tag 0A45, closed base change
* Stacks Tag 03AJ, pullback of framed torsors
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

private local instance (priority := 3000) additiveSelfForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := ⟨𝟭 _, rfl⟩



private local instance (priority := 3000) integralWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

private local instance (priority := 3000) integralLocallyBijective (T : Scheme.{u}) :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance

private theorem framedQuotient_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (e : S.X₃ ≅ T.X₂) (h : T.X₁ ⟶ S.X₂) (hh : h ≫ S.g ≫ e.hom = T.f) :
    let a := S.f ≫ cokernel.π h
    let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g)
      (by calc
        h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
          simp only [Category.assoc]
        _ = 0 := by rw [hh, T.zero])
    ∃ hz : a ≫ b = 0, (ShortComplex.mk a b hz).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := hT.mono_f
  have := hT.epi_g
  have hzcomp : h ≫ (S.g ≫ e.hom ≫ T.g) = 0 := by
    calc
      h ≫ (S.g ≫ e.hom ≫ T.g) = (h ≫ S.g ≫ e.hom) ≫ T.g := by
        simp only [Category.assoc]
      _ = 0 := by rw [hh, T.zero]
  let a := S.f ≫ cokernel.π h
  let b := cokernel.desc h (S.g ≫ e.hom ≫ T.g) hzcomp
  have hb : cokernel.π h ≫ b = S.g ≫ e.hom ≫ T.g := cokernel.π_desc _ _ _
  have hab : a ≫ b = 0 := by
    dsimp only [a]
    rw [Category.assoc, hb, ← Category.assoc, S.zero, zero_comp]
  have : Mono h := mono_of_mono_fac hh
  have hhc : (ShortComplex.mk h (cokernel.π h) (cokernel.condition h)).ShortExact :=
    { exact := ShortComplex.exact_cokernel h }
  have ha : Mono a := by
    apply Abelian.mono_of_kernel_ι_eq_zero
    let k := kernel.ι a
    have hk : (k ≫ S.f) ≫ cokernel.π h = 0 := by
      rw [Category.assoc]
      exact kernel.condition a
    let r := hhc.fIsKernel.lift (KernelFork.ofι (k ≫ S.f) hk)
    have hr : r ≫ h = k ≫ S.f := hhc.fIsKernel.fac _ WalkingParallelPair.zero
    have hrt : r ≫ T.f = 0 := by
      calc
        r ≫ T.f = (r ≫ h) ≫ S.g ≫ e.hom := by rw [← hh]; simp only [Category.assoc]
        _ = 0 := by rw [hr, Category.assoc, reassoc_of% S.zero, zero_comp, comp_zero]
    have hrzero : r = 0 := (cancel_mono T.f).1 (by simpa using hrt)
    have hka : k ≫ S.f = 0 := by rw [← hr, hrzero, zero_comp]
    exact (cancel_mono S.f).1 (by simpa using hka)
  have hbepi : Epi b := epi_of_epi_fac hb
  have hbCoker : IsColimit (CokernelCofork.ofπ b hab) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro M f hf
    have hSf : S.f ≫ (cokernel.π h ≫ f) = 0 := by
      rw [← Category.assoc]
      exact hf
    let q := hS.gIsCokernel.desc (CokernelCofork.ofπ (cokernel.π h ≫ f) hSf)
    have hq : S.g ≫ q = cokernel.π h ≫ f := hS.gIsCokernel.fac _ WalkingParallelPair.one
    have htq : T.f ≫ (e.inv ≫ q) = 0 := by
      calc
        T.f ≫ (e.inv ≫ q) = h ≫ (S.g ≫ q) := by
          rw [← hh]
          simp only [Category.assoc, e.hom_inv_id_assoc]
        _ = 0 := by rw [hq, ← Category.assoc, cokernel.condition, zero_comp]
    let r := hT.gIsCokernel.desc (CokernelCofork.ofπ (e.inv ≫ q) htq)
    have hr : T.g ≫ r = e.inv ≫ q := hT.gIsCokernel.fac _ WalkingParallelPair.one
    refine ⟨r, ?_⟩
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, hb, Category.assoc, Category.assoc, hr,
      ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp, hq]
  exact ⟨hab, { exact := ShortComplex.exact_of_g_is_cokernel _ hbCoker }⟩

attribute [local irreducible] relativeFiberMap relativeTorsorEquiv

/-- The relative extension characterization, including its equivariant framed lift. -/
def RelativeExtensionRepresents {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1) : Prop :=
  ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1}),
    (∀ (V : T.Etaleᵒᵖ) (g : G.obj.obj V) (t : P.1.sheaf.obj.obj V),
      @id (E.obj.obj V) (f.app V (P.1.vadd V g t)) =
        @id (E.obj.obj V) (f.app V t) + a.hom.app V g) ∧
    (∀ (V : T.Etaleᵒᵖ) (t : P.1.sheaf.obj.obj V),
      b.hom.app V (f.app V t) = (supportedIntegralUnit i).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩)) ∧
    @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0 ∧ β = hE.extClass

/-- Existence and uniqueness of the framed supported extension class. -/
theorem relativeExtension_existsUnique {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    ∃! β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant Z)) G 1, RelativeExtensionRepresents i P β := by
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  exact Sheaf.Torsor.relative_extension_existsUnique T P.1
    (Scheme.Etale.mk i.openComplement.ι) P.2 t (supportedIntegralUnit i)
    ht hT η hη hηt

/-- The class determined uniquely by the relative extension characterization. -/
def relativeExtension {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (i : Z ⟶ T) [IsClosedImmersion i]
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι)) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) G 1 :=
  Classical.choose (relativeExtension_existsUnique i P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem relativeExtension_morphism {T Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})] (i : Z ⟶ T)
    [IsClosedImmersion i] {G G' Q' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (φ : G ⟶ G') (E' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a' : G' ⟶ E') (b' : E' ⟶ Q') (hab' : a' ≫ b' = 0)
    (r : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z) ⟶ Q')
    (f' : P.1.sheaf.obj ⟶ E'.obj ⋙ forget AddCommGrpCat.{u + 1})
    (hf'a : ∀ V g t, f'.app V (P.1.vadd V g t) =
      (show E'.obj.obj V from f'.app V t) + (φ ≫ a').hom.app V g)
    (hf'b : ∀ V t, b'.hom.app V (f'.app V t) =
      (supportedIntegralUnit i ≫ r).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
    (hf'τ : (show E'.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)) from
      f'.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2) = 0) :
    ∃ (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact),
      relativeExtension i P = hE.extClass ∧
        ∃ α : E ⟶ E', a ≫ α = φ ≫ a' ∧ α ≫ b' = b ≫ r := by
  classical
  let U := Scheme.Etale.mk i.openComplement.ι
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    exists_integral_openClosed_sections i i.openComplement rfl
  obtain ⟨E⟩ : Nonempty (Sheaf.Torsor.ExtensionPresentation.{u, u} T P.1) :=
    Sheaf.Torsor.nonempty_extensionPresentation T P.1
  let S := ShortComplex.mk E.inclusion E.projection E.inclusion_projection
  have hS : S.ShortExact := Sheaf.Torsor.extension_presentation_shortExact T E
  let h := (η E.middle).symm (E.generator (op U) P.2)
  have hp : h ≫ E.projection = t := by
    apply (η (supportedIntegralConstant T)).injective
    rw [hη, AddEquiv.apply_symm_apply, hηt]
    exact E.projection_generator _ _
  obtain ⟨hab, hE⟩ := framedQuotient_shortExact S
    (ShortComplex.mk t (supportedIntegralUnit i) ht) hS hT
    (by exact CategoryTheory.Iso.refl (supportedIntegralConstant T)) h (by
      change h ≫ E.projection ≫ 𝟙 _ = t
      simpa using hp)
  let a := E.inclusion ≫ cokernel.π h
  let b := cokernel.desc h (E.projection ≫ supportedIntegralUnit i)
    (by rw [← Category.assoc, hp]; exact ht)
  change (ShortComplex.mk a b hab).ShortExact at hE
  let f : P.1.sheaf.obj ⟶ (cokernel h).obj ⋙ forget AddCommGrpCat.{u + 1} :=
    { app V := TypeCat.ofHom fun z ↦ (cokernel.π h).hom.app V (E.generator V z)
      naturality V V' k := by
        ext z
        change (cokernel.π h).hom.app V' (E.generator V' (P.1.sheaf.obj.map k z)) =
          (cokernel h).obj.map k ((cokernel.π h).hom.app V (E.generator V z))
        rw [← E.generator_natural]
        exact ConcreteCategory.congr_hom ((cokernel.π h).hom.naturality k) _ }
  have hfa V g z : f.app V (P.1.vadd V g z) =
      (show (cokernel h).obj.obj V from f.app V z) + a.hom.app V g := by
    change (cokernel.π h).hom.app V (E.generator V (P.1.vadd V g z)) = _
    rw [E.generator_vadd, map_add]
    rfl
  have hfb V z : b.hom.app V (f.app V z) = (supportedIntegralUnit i).hom.app V
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩) := by
    change ((cokernel.π h ≫ b).hom.app V) (E.generator V z) = _
    rw [cokernel.π_desc]
    change (supportedIntegralUnit i).hom.app V
      (E.projection.hom.app V (E.generator V z)) = _
    rw [E.projection_generator]
  have hfτ : (show (cokernel h).obj.obj (op U) from f.app (op U) P.2) = 0 := by
    change (cokernel.π h).hom.app (op U) (E.generator (op U) P.2) = 0
    have hh := hη (cokernel.π h) h
    have he : (η E.middle) h = E.generator (op U) P.2 := AddEquiv.apply_symm_apply _ _
    rw [cokernel.condition, map_zero, he] at hh
    exact hh.symm
  have hβ : relativeExtension i P = hE.extClass := by
    exact ((Classical.choose_spec (relativeExtension_existsUnique i P)).2 _
      ⟨_, a, b, hab, hE, f, hfa, hfb, hfτ, rfl⟩).symm
  obtain ⟨α, ⟨hαa, hαf⟩, _⟩ := E.universal E' (φ ≫ a')
    (fun V z ↦ f'.app V z)
    (fun V V' k z ↦ (ConcreteCategory.congr_hom (f'.naturality k) z).symm) hf'a
  have hαb : α ≫ b' = E.projection ≫ supportedIntegralUnit i ≫ r := by
    obtain ⟨l, hl, huniq⟩ := E.universal Q' 0
      (fun V _ ↦ (supportedIntegralUnit i ≫ r).hom.app V
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V ⟨1⟩))
      (by
        intro V V' k z
        rw [← ConcreteCategory.comp_apply, ← (supportedIntegralUnit i ≫ r).hom.naturality,
          ConcreteCategory.comp_apply]
        congr 1
        exact (ConcreteCategory.congr_hom
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality k)
          ⟨1⟩).symm)
      (by intro V g z; change _ = _ + 0; exact (add_zero _).symm)
    apply (huniq _ ⟨by rw [← Category.assoc, hαa, Category.assoc, hab', comp_zero], ?_⟩).trans
      (huniq _ ⟨by rw [← Category.assoc, E.inclusion_projection, zero_comp], ?_⟩).symm
    · intro V z
      change b'.hom.app V (α.hom.app V (E.generator V z)) = _
      rw [hαf, hf'b]
    · intro V z
      change (supportedIntegralUnit i ≫ r).hom.app V
        (E.projection.hom.app V (E.generator V z)) = _
      rw [E.projection_generator]
  have hhα : h ≫ α = 0 := by
    apply (η E').injective
    rw [hη, map_zero]
    change α.hom.app (op U) ((η E.middle) ((η E.middle).symm _)) = 0
    rw [AddEquiv.apply_symm_apply, hαf]
    exact hf'τ
  let α' := cokernel.desc h α hhα
  have hα'a : a ≫ α' = φ ≫ a' := by
    rw [Category.assoc, cokernel.π_desc]
    exact hαa
  have hα'b : α' ≫ b' = b ≫ r := by
    apply (cancel_epi (cokernel.π h)).1
    rw [← Category.assoc, cokernel.π_desc, ← Category.assoc, cokernel.π_desc]
    exact hαb
  exact ⟨_, a, b, hab, hE, hβ, α', hα'a, hα'b⟩

set_option backward.isDefEq.respectTransparency false in
private def integerSectionEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (supportedIntegralConstant T ⟶ F) ≃+
      F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

set_option backward.isDefEq.respectTransparency false in
private lemma integerSectionEquiv_eval (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : supportedIntegralConstant T ⟶ F) :
    integerSectionEquiv T F a =
      a.hom.app (op (Scheme.Etale.mk (𝟙 T))) (supportedIntegralOne T) := by
  change ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homEquiv _ F a) ⟨1⟩ = _
  rw [Adjunction.homEquiv_unit]
  rfl

private lemma integerSectionEquiv_restrict (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : supportedIntegralConstant T ⟶ F) (U : T.Etaleᵒᵖ) :
    a.hom.app U ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) =
    F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
      (integerSectionEquiv T F a) := by
  rw [integerSectionEquiv_eval]
  have h := ConcreteCategory.congr_hom (a.hom.naturality
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op)
      (supportedIntegralOne T)
  simp only [ConcreteCategory.comp_apply] at h
  have hn := ConcreteCategory.congr_hom ((toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op) ⟨1⟩
  have hn' : (supportedIntegralConstant T).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
        (supportedIntegralOne T) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩ :=
    hn.symm
  rw [hn'] at h
  exact h

/-- Canonical closed exchange on integral coefficients, with the constant comparison. -/
def relativeExtensionExchange {T Z T' Z' : Scheme.{u}} (i : Z ⟶ T) (i' : Z' ⟶ T')
    (h : T' ⟶ T) (w : Z' ⟶ Z) (sq : CommSq w i' i h) :
    (upperStar AddCommGrpCat.{u + 1} h).obj
        ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant Z)) ⟶
      (lowerStar AddCommGrpCat.{u + 1} i').obj (supportedIntegralConstant Z') :=
  (baseChangeMap AddCommGrpCat.{u + 1} sq).app (supportedIntegralConstant Z) ≫
    (lowerStar AddCommGrpCat.{u + 1} i').map
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} w).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom

/-- The pulled frame, including the identification of the two complementary opens. -/
def relativeExtensionPulledFrame {T Z T' Z' : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (i' : Z' ⟶ T') [IsClosedImmersion i']
    (h : T' ⟶ T) (hW : i'.openComplement = h ⁻¹ᵁ i.openComplement)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (Q : Sheaf.Torsor G')
    (b : P.1.sheaf.obj ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj) :
    Sheaf.Torsor.WithSection G' (Scheme.Etale.mk i'.openComplement.ι) :=
  ⟨Q, Q.sheaf.obj.map ((eqToHom (congrArg (fun W : T'.Opens ↦ Scheme.Etale.mk W.ι) hW)) ≫
      openSectionPullback h i.openComplement).op
        (b.app (op (Scheme.Etale.mk i.openComplement.ι)) P.2)⟩

private theorem integralConstantComposition {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (k : X ⟶ Z) (hk : k = g ≫ f) :
    (upperStarComp AddCommGrpCat.{u + 1} g f k hk).hom.app (supportedIntegralConstant Z) ≫
      (upperStar AddCommGrpCat.{u + 1} g).map
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  subst k
  exact Scheme.upperStarConstantSheafIso_comp AddCommGrpCat.{u + 1} g f
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralBaseChangeUnit {T' T D' D : Scheme.{u}}
    (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (hD : D' ⟶ D) (sq : CommSq hD i' i h) :
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
      (upperStar AddCommGrpCat.{u + 1} h).map (supportedIntegralUnit i) ≫
        relativeExtensionExchange i i' h hD sq = supportedIntegralUnit i' := by
  let P := supportedIntegralConstant T
  let H := upperStar AddCommGrpCat.{u + 1} h
  let HD := upperStar AddCommGrpCat.{u + 1} hD
  let L := lowerStar AddCommGrpCat.{u + 1} i'
  let c {X Y : Scheme.{u}} (f : X ⟶ Y) := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    f).hom.app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hc : (squareUpperStarIso AddCommGrpCat.{u + 1} sq).hom.app P ≫
      HD.map (c i) ≫ c hD = (upperStar AddCommGrpCat.{u + 1} i').map (c h) ≫ c i' := by
    dsimp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [Scheme.upperStarConstantSheafIso_comp]
    apply (cancel_epi ((upperStarComp AddCommGrpCat.{u + 1} i' h (hD ≫ i) sq.w).hom.app P)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    exact (integralConstantComposition i' h (hD ≫ i) sq.w).symm
  simp only [supportedIntegralUnit, relativeExtensionExchange, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  change (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} h).inv.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ H.map ((upperStarLowerStarAdjunction
        AddCommGrpCat.{u + 1} i).unit.app P) ≫ H.map ((lowerStar
          AddCommGrpCat.{u + 1} i).map (c i)) ≫
      (baseChangeMap AddCommGrpCat.{u + 1} sq).app (supportedIntegralConstant D) ≫
        L.map (c hD) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i').unit.app
      (supportedIntegralConstant T') ≫ L.map (c i')
  rw [reassoc_of% (baseChangeMap_naturality AddCommGrpCat.{u + 1} sq (c i)),
    reassoc_of% (map_unit_baseChangeMap_app AddCommGrpCat.{u + 1} sq P)]
  rw [← L.map_comp, ← L.map_comp, hc]
  simp only [L.map_comp]
  have hn := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i').unit.naturality
    (c h)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp [c]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralUnit_section {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (V : Y.Etale) (m : ULift.{u + 1} ℤ) :
    (supportedIntegralUnit g).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (AddCommGrpCat.{u + 1}) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (AddCommGrpCat.{u + 1}) g
  let adj := Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g
  have key : (adjY.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
      ((sheafSections Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≫
      e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      adjZ.unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (AddCommGrpCat.{u + 1})] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      f.op)).hom m)).symm
  let θ := supportedIntegralUnit g
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (AddCommGrpCat.{u + 1})).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology
        ((Functor.const Y.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((Scheme.upperStarConstantSheafIso (AddCommGrpCat.{u + 1}) g).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem openSectionPullback_isIso {T T' : Scheme.{u}}
    (h : T' ⟶ T)
    (W : T.Opens) : IsIso (openSectionPullback h W) := by
  let e : Scheme.Etale.mk (h ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk W.ι) :=
    MorphismProperty.Over.isoMk (isPullback_morphismRestrict h W).isoPullback
      (isPullback_morphismRestrict h W).isoPullback_hom_snd
  have he : e.hom = openSectionPullback h W := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (isPullback_morphismRestrict h W).isoPullback.hom ≫ pullback.fst W.ι h =
        pullback.lift (morphismRestrict h W) (h ⁻¹ᵁ W).ι (morphismRestrict_ι h W) ≫
          pullback.fst W.ι h
      rw [pullback.lift_fst]
      exact (isPullback_morphismRestrict h W).isoPullback_hom_fst
    · change (isPullback_morphismRestrict h W).isoPullback.hom ≫ pullback.snd W.ι h =
        pullback.lift (morphismRestrict h W) (h ⁻¹ᵁ W).ι (morphismRestrict_ι h W) ≫
          pullback.snd W.ι h
      rw [pullback.lift_snd]
      exact (isPullback_morphismRestrict h W).isoPullback_hom_snd
  rw [← he]
  infer_instance


end AlgebraicGeometry.Etale
