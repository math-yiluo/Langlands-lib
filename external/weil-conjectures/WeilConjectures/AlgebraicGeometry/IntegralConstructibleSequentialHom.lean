/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Category.ULift

/-! # Bounded-below sequential Hom continuity for integral constructible complexes -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
  {I : Type v} [SmallCategory I] [IsFiltered I]
omit [IsFiltered I] in
private theorem homColimit_iso (D : I ⥤ DerivedCategory C) (c : Cocone D)
    {K L : DerivedCategory C} (e : K ≅ L)
    (h : homColimitProperty D c L) : homColimitProperty D c K := by
  intro n
  let eF := Functor.isoWhiskerLeft (shiftFunctor _ n)
    (preadditiveCoyoneda.mapIso e.symm.op)
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (h n)
  exact ⟨IsColimit.mapCoconeEquiv eF.symm hc⟩

omit [IsFiltered I] in
private theorem homColimit_zero (D : I ⥤ DerivedCategory C) (c : Cocone D)
    (K : DerivedCategory C) (hzero : IsZero K) : homColimitProperty D c K := by
  intro m
  let H := shiftFunctor (DerivedCategory C) m ⋙ preadditiveCoyoneda.obj (op K)
  have hobj (L : DerivedCategory C) : IsZero (H.obj L) := by
    let : Subsingleton (H.obj L) := ⟨fun f g ↦ hzero.eq_of_src f g⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hp : IsZero (H.obj c.pt) := hobj c.pt
  have hc : IsZero (colimit (D ⋙ H)) :=
    (colimit.isColimit (D ⋙ H)).isZero_pt
      ((D ⋙ H).isZero_iff.2 (fun i ↦ hobj (D.obj i)))
  exact ⟨⟨0, hc.eq_of_src _ _, hp.eq_of_src _ _⟩⟩

private theorem homColimit_bounded (D : I ⥤ DerivedCategory C) (c : Cocone D)
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ M, P M → homColimitProperty D c ((DerivedCategory.singleFunctor C 0).obj M))
    (K : DerivedCategory C) (hK : DerivedCategory.TStructure.t.bounded K)
    (hKP : ∀ q, P ((DerivedCategory.homologyFunctor C q).obj K)) :
    homColimitProperty D c K := by
  let Q := homColimitProperty D c
  let : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ homColimit_iso D c e.symm h⟩
  let : Q.ContainsZero := ⟨0, isZero_zero _, homColimit_zero D c _ (isZero_zero _)⟩
  let : Q.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦
        { le_shift := fun K h ↦ homColimitProperty_shift D c K h n } }
  let : Q.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    homColimitProperty_extensions D c T hT h₁ h₃)
  let : Q.IsTriangulated := {}
  exact DerivedCategory.prop_of_bounded Q P hP K hK hKP
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- A map from an integral bounded constructible complex to a sequential colimit of
complexes with a common cohomological lower bound factors through a finite stage.
Source: Bhatt--Scholze, Lemma 6.8.12, with the sequential telescope argument.
(auxiliary; not a blueprint node)

Proof. Lift the sequence along the equivalence with AsSmall(ℕ), preserving its
colimit cocone and common lower bound. Shifted Hom continuity is known for each
constructible cohomology sheaf of K by the sheaf-source lemma. For a fixed cocone,
this continuity property is closed under isomorphisms, shifts and distinguished
extensions and contains zero. The bounded Postnikov devissage theorem therefore
gives it for K itself. At shift zero its Hom cocone is a filtered colimit of abelian
groups. Every element of this colimit has a representative at one stage. Apply this
to the specified morphism f, and use naturality of the shift-zero isomorphism to
remove the zero shift. The indexing equivalence identifies that stage's cocone leg
with exactly the original leg Q(c.ι_n), giving the asserted equation. -/
theorem integralConstructible_hom_sequential_colimit (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] (K : integralConstructible ℓ E X)
    (D : ℕ ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) ℤ)
    (c : Cocone D) (hc : Nonempty (IsColimit c))
    (hD : ∃ a : ℤ, ∀ n : ℕ, (DerivedCategory.Q.obj (D.obj n)).IsGE a)
    (f : K.obj ⟶ DerivedCategory.Q.obj c.pt) :
    ∃ (n : ℕ) (g : K.obj ⟶ DerivedCategory.Q.obj (D.obj n)),
      g ≫ DerivedCategory.Q.map (c.ι.app n) = f := by
  let e : ℕ ≌ AsSmall.{u + 1} ℕ := AsSmall.equiv
  let D' := e.inverse ⋙ D
  let c' := c.whisker e.inverse
  obtain ⟨hc⟩ := hc
  have hc' : IsColimit c' := hc.whiskerEquivalence e.symm
  have hD' : ∃ a : ℤ, ∀ n, (DerivedCategory.Q.obj (D'.obj n)).IsGE a := by
    obtain ⟨a, ha⟩ := hD
    exact ⟨a, fun n ↦ ha (e.inverse.obj n)⟩
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X)) :=
    ⟨fun e hM ↦ _root_.constructible_of_iso e hM⟩
  have hK : homColimitProperty (D' ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone c') K.obj := by
    apply homColimit_bounded _ _
      (IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X))
    · intro M hM
      exact integralConstructible_sheaf_hom_colimit ℓ E X M hM D' c' ⟨hc'⟩ hD'
    · exact K.property.1
    · exact K.property.2
  let H := shiftFunctor _ (0 : ℤ) ⋙ preadditiveCoyoneda.obj (op K.obj)
  obtain ⟨hcolim⟩ : Nonempty (IsColimit
      (H.mapCocone (DerivedCategory.Q.mapCocone c'))) :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 (hK 0)
  let e0 := shiftFunctorZero (DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))) ℤ
  let f0 := f ≫ e0.inv.app (DerivedCategory.Q.obj c.pt)
  obtain ⟨i, g, hg⟩ := Concrete.isColimit_exists_rep
    ((D' ⋙ DerivedCategory.Q) ⋙ H) hcolim f0
  let g' : K.obj ⟶ (DerivedCategory.Q.obj (D.obj (e.inverse.obj i))) ⟦(0 : ℤ)⟧ := g
  have hg' : g' ≫ (shiftFunctor _ (0 : ℤ)).map
      (DerivedCategory.Q.map (c.ι.app (e.inverse.obj i))) = f0 := hg
  refine ⟨e.inverse.obj i,
    g' ≫ e0.hom.app (DerivedCategory.Q.obj (D.obj (e.inverse.obj i))), ?_⟩
  have h := congrArg (fun v ↦ v ≫ e0.hom.app (DerivedCategory.Q.obj c.pt)) hg'
  dsimp only [f0] at h
  erw [Category.assoc, e0.hom.naturality] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_map] at h
  erw [Category.comp_id] at h
  simpa only [Category.assoc] using h

end AlgebraicGeometry.ProEtale.CondensedRing
