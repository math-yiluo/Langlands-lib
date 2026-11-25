/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnionTriangles
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
/-! # The counit factorization at a supplied union complex

Source: Stacks Project, Tag 0DJ9, relative Mayer--Vietoris induction.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem unionEquation_isIso_biprod_map
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {S T S' T' : C} {f : S ⟶ S'} {g : T ⟶ T'}
    (hf : IsIso f) (hg : IsIso g) : IsIso (biprod.map f g) := by
  let := hf
  let := hg
  change IsIso (biprod.mapIso (asIso f) (asIso g)).hom
  infer_instance

private theorem unionEquation_isIso_of_eq
    {C : Type*} [Category C] {S T : C} {f g : S ⟶ T}
    (h : f = g) (hf : IsIso f) : IsIso g := h ▸ hf

private theorem unionEquation_factor
    {C : Type*} [Category C] {S T W Z : C}
    (f : S ⟶ T) (c : T ⟶ W) (m : S ⟶ Z)
    (hf : IsIso f) (hc : IsIso c) (hm : IsIso m) :
    ∃ t : W ≅ Z, m = f ≫ c ≫ t.hom := by
  let := hf
  let := hc
  let := hm
  let a := asIso f ≪≫ asIso c
  refine ⟨a.symm ≪≫ asIso m, ?_⟩
  simpa only [a, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc] using
    (Iso.hom_inv_id_assoc a m).symm

set_option linter.unusedVariables false in
-- Preserve the original names of the nondependent forall proof binders.
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Naturality of the Mayer--Vietoris cone supplies the remaining pullback and
counit data for a bounded flat union complex (Stacks, Tag 0DJ9).
(blueprint: new-pc-standard-single-flat-counit-union-equation).

Proof: Restrict N to U, V and their intersection. Open restriction preserves
quasi-coherence and relative flatness, so the three hypotheses supply flat
presentations of these restrictions. Their bounded-above flat complexes are
K-flat. The universal derived-pullback counit is therefore invertible on each;
its identification with the pinned counit follows from uniqueness of the
left-derived functor. The presentation equations imply that the three canonical
base-change comparisons are isomorphisms. Relative Mayer--Vietoris for the
cover of U union V, and for its inverse-image cover, gives a morphism of
triangles: the squares commute by naturality of the adjunction comparisons,
including the boundary square. To obtain that square without compactness
assumptions, represent the two direct images by K-injective complexes with
injective terms. The sectionwise open counit square commutes before derivation;
its degreewise restriction-difference version is a map of short exact
Mayer--Vietoris complexes. Naturality of the short-exact-sequence boundary,
followed by the adjunction Hom equivalence and its shift compatibility,
identifies the boundary composites. No quasi-coherent direct-image refinement
of Mayer--Vietoris is required. The second and third components are the above
isomorphisms, so the first, namely the canonical comparison for N, is an
isomorphism by the two-out-of-three theorem for distinguished triangles.
The supplied K is itself bounded above and flat, so its pinned counit is also
invertible. Let a be the composite of the derived pullback of e.hom with this
counit. Define t to be the isomorphism with hom a inverse followed by the
canonical comparison. Then a followed by t.hom is the canonical comparison,
by cancellation of a with its inverse. This proves exactly the displayed
equation for the supplied K and e, without selecting a different complex. -/
theorem standardSingleFlatCounitUnionEquation
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∀ (K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i))
    (e : (schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)),
    ∃ t : DerivedCategory.Qh.obj
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
      (schemeDerivedDirectImage (pullback.snd ((U ⊔ V).ι ≫ p) g)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst ((U ⊔ V).ι ≫ p) g) N)),
      standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g =
        (derivedPullback g).map e.hom ≫
          (SingleComplexBaseChange.counit g).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫ t.hom := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard A.Modules
  let := HasDerivedCategory.standard B.Modules
  intro K hbounded hflat e
  obtain ⟨d₁, d₂, d₃, d₁', d₂', d₃', hT, hT', φ, h₁, h₂, h₃, hU, hV, hUV⟩ :=
    standardSingleFlatCounitUnionTriangles p g U V N hN hPU hPV hPUV
  have hm := unionEquation_isIso_of_eq h₂.symm (unionEquation_isIso_biprod_map hU hV)
  have ho := unionEquation_isIso_of_eq h₃.symm hUV
  have hbc := unionEquation_isIso_of_eq h₁
    (Pretriangulated.isIso₁_of_isIso₂₃ φ hT hT' hm ho)
  have hK := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    B.toRingedSpace K hbounded hflat
  have hc := SingleComplexBaseChange.counit_isIso_kFlat g K hK
  exact unionEquation_factor ((derivedPullback g).map e.hom)
    ((SingleComplexBaseChange.counit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K))
    (standardSingleBaseChangeMap ((U ⊔ V).ι ≫ p) N g) (by infer_instance) hc hbc
end AlgebraicGeometry
