/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.Integral.IntegralWindowCoproductComparison
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.CompactObjectsThick
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-!
# Integral constructible complexes are compact

The assertion bundle expands the three clauses with the actual ambient module category.
`H.ind` is the full replete filtered-colimit image IndCons; Dic is expanded cohomologically.
The realization is characterized as the filtered-colimit-preserving extension of the
inclusion along Ind.yoneda. Thus it sends every formal filtered diagram to its ambient
colimit, including the induced maps. No unconstrained realization functor is assumed.
All coproducts and truncations are in the ordinary unbounded derived category.
-/

@[expose] public noncomputable section

set_option linter.privateModule false

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem coproductSmallSupport
    {D : Type u} [Category.{v} D] [Preadditive D]
    {I : Type w} (K : I → D) (c : Cofan K) (hc : IsColimit c) :
    Small.{v} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : c.pt ⟶ K i := hc.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : c.inj j ≫ p i =
      Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    hc.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective.{v} (β := c.pt ⟶ c.pt)
    (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ c.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ c.inj i.val ≫ f ≫ p i.val) hij
  have hi : c.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : c.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

private theorem closedUnderCoproducts_of_small
    {D : Type u} [Category.{v} D] [Preadditive D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (hsmall : ∀ I : Type v, P.IsClosedUnderColimitsOfShape (Discrete I))
    (I : Type w) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
  classical
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let K : I → D := fun i ↦ F.obj ⟨i⟩
  let c : Cofan K := Cofan.mk (colimit F) (fun i ↦ colimit.ι F ⟨i⟩)
  have hc : IsColimit c := by
    let e : Discrete.functor K ≅ F := Discrete.natIso (fun _ ↦ Iso.refl _)
    apply IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv e (colimit.cocone F)).symm (colimit.isColimit F))
    exact Cocone.ext (Iso.refl _) (fun i ↦ by simp [e, c])
  have : Small.{v} {i // ¬ IsZero (K i)} := coproductSmallSupport K c hc
  let J := {i // ¬ IsZero (K i)}
  let r : Cofan (fun i : J ↦ K i.val) := Cofan.mk c.pt (fun i ↦ c.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ hc.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change c.ι.app ⟨i⟩ ≫ _ = _
      rw [hc.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply hc.hom_ext
      intro ⟨i⟩
      rw [hc.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  let : P.IsClosedUnderColimitsOfShape (Discrete (Shrink.{v} J)) := hsmall _
  let : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J)).symm
  exact P.prop_of_isColimit (J := Discrete J) hr (fun i ↦ hF ⟨i.as.val⟩)

private theorem compact_reflects
    {C : Type u} {D : Type w} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasCoproducts.{v} C] [HasCoproducts.{v} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) F]
    (K : C) (hK : IsCompactObject (F.obj K)) : IsCompactObject K := by
  classical
  intro I A
  let e (L : C) : (K ⟶ L) ≃+ (F.obj K ⟶ F.obj L) :=
    AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩
  let ds := DirectSum.congrAddEquiv (fun i ↦ e (A i))
  let s := sigmaComparison F A
  let post : (F.obj K ⟶ F.obj (∐ A)) ≃+ (F.obj K ⟶ ∐ fun i ↦ F.obj (A i)) :=
    { toEquiv := Iso.homCongr (Iso.refl _) (asIso s).symm
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.add_comp] }
  let φ := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let ψ := DirectSum.toAddMonoid
    (fun i ↦ Preadditive.rightComp (F.obj K) (Sigma.ι (fun i ↦ F.obj (A i)) i))
  have hcomm : (post.toAddMonoidHom.comp (e (∐ A)).toAddMonoidHom).comp φ =
      ψ.comp ds.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    change post (e (∐ A) (φ (DirectSum.of _ i f))) =
      ψ (ds (DirectSum.of _ i f))
    rw [show φ (DirectSum.of _ i f) = f ≫ Sigma.ι A i from
      DirectSum.toAddMonoid_of
        (fun i ↦ Preadditive.rightComp K (Sigma.ι A i)) i f]
    rw [show ds (DirectSum.of _ i f) = DirectSum.of _ i (e (A i) f) from
      DirectSum.map_of (fun i ↦ (e (A i)).toAddMonoidHom) i f]
    rw [show ψ (DirectSum.of _ i (e (A i) f)) =
        e (A i) f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i from
      DirectSum.toAddMonoid_of
        (fun i ↦ Preadditive.rightComp (F.obj K) (Sigma.ι (fun i ↦ F.obj (A i)) i)) i _]
    dsimp [post, e, Iso.homCongr, AddEquiv.ofBijective]
    simp only [Category.id_comp]
    change F.map (f ≫ Sigma.ι A i) ≫ inv s =
      F.map f ≫ Sigma.ι (fun i ↦ F.obj (A i)) i
    rw [Functor.map_comp, Category.assoc, map_ι_comp_inv_sigmaComparison]
  have hb : Function.Bijective (fun x ↦ post (e (∐ A) (φ x))) := by
    have heq : (fun x ↦ post (e (∐ A) (φ x))) = (fun x ↦ ψ (ds x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [heq]
    exact (hK I (fun i ↦ F.obj (A i))).comp ds.bijective
  constructor
  · intro x y hxy
    exact hb.1 (congrArg (fun z ↦ post (e (∐ A) z)) hxy)
  · intro f
    obtain ⟨x, hx⟩ := hb.2 (post (e (∐ A) f))
    exact ⟨x, (e (∐ A)).injective (post.injective hx)⟩

private theorem compact_devissage_and_restrict
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [HasCoproducts.{v} (DerivedCategory A)]
    (H : ObjectProperty A) [H.IsClosedUnderIsomorphisms]
    (P L : ObjectProperty (DerivedCategory A))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [L.IsTriangulated] [L.IsClosedUnderIsomorphisms]
    [∀ I : Type v, P.IsClosedUnderColimitsOfShape (Discrete I)]
    [∀ I : Type v, L.IsClosedUnderColimitsOfShape (Discrete I)]
    (hLP : L ≤ P)
    (hsingle : ∀ C : A, H C →
      ∃ hC : P ((DerivedCategory.singleFunctor A 0).obj C),
        IsCompactObject.{v}
          (ObjectProperty.FullSubcategory.mk ((DerivedCategory.singleFunctor A 0).obj C) hC))
    (K : L.FullSubcategory)
    (hK : DerivedCategory.TStructure.t.bounded K.obj ∧
      ∀ n : ℤ, H ((DerivedCategory.homologyFunctor A n).obj K.obj)) :
    IsCompactObject.{v} K := by
  let : HasCoproducts.{v} P.FullSubcategory := fun I ↦ inferInstance
  let : HasCoproducts.{v} L.FullSubcategory := fun I ↦ inferInstance
  let R : ObjectProperty P.FullSubcategory := fun K ↦ IsCompactObject.{v} K
  let : R.IsTriangulated := (compactObjects_isThick (C := P.FullSubcategory)).1
  let : R.IsStableUnderRetracts := (compactObjects_isThick (C := P.FullSubcategory)).2
  let Q := R.map P.ι
  have hQ : Q K.obj := by
    apply DerivedCategory.prop_of_bounded Q H ?_ K.obj hK.1 hK.2
    intro C hC
    obtain ⟨h, hc⟩ := hsingle C hC
    exact ⟨⟨_, h⟩, hc, ⟨Iso.refl _⟩⟩
  let F : L.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift L.ι (fun K ↦ hLP K.obj K.property)
  have hpres (I : Type v) : PreservesColimitsOfShape (Discrete I) F := by
    have : PreservesColimitsOfShape (Discrete I) (F ⋙ P.ι) :=
      preservesColimitsOfShape_of_natIso (P.liftCompιIso L.ι _).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves F P.ι
  let := hpres
  obtain ⟨J, hJ, ⟨e⟩⟩ := hQ
  let e' : J ≅ F.obj K := P.fullyFaithfulι.preimageIso e
  have : IsCompactObject (F.obj K) := R.prop_of_iso e' hJ
  exact compact_reflects F K this

end AlgebraicGeometry.ProEtale
