/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.AffinePerfectGradedHomDescent
import WeilConjectures.Algebra.Homology.AffinePerfectChainMapEqualityDetection

/-! # Descent of homotopies between affine perfect chain maps

Source: Stacks Project, Tag 09RE, affine case (1).
(blueprint: lem-pc-affine-perfect-homotopy-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private instance extendScalars_additive
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} r).Additive :=
  (ModuleCat.extendRestrictScalarsAdj r).left_adjoint_additive

private theorem scalarExtensionHom_sub
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f g : ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj Q) :
    scalarExtensionHom r s t hc P Q (f - g) =
      scalarExtensionHom r s t hc P Q f - scalarExtensionHom r s t hc P Q g := by
  simp only [scalarExtensionHom, Functor.map_sub, Preadditive.comp_sub,
    Preadditive.sub_comp]

private theorem scalarExtensionHom_zero
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    scalarExtensionHom r s t hc P Q 0 = 0 := by
  simp only [scalarExtensionHom, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

private noncomputable def scalarExtensionHom_homotopy
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f g : ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj Q)
    (h : Homotopy f g) :
    Homotopy (scalarExtensionHom r s t hc P Q f)
      (scalarExtensionHom r s t hc P Q g) := by
  let h₁ := (ModuleCat.extendScalars s).mapHomotopy h
  let h₂ := h₁.compLeft
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp r s) (.up ℤ)).hom.app P)
  let h₃ := h₂.compLeft (eqToHom (congrArg (fun x ↦
    ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj P) hc))
  let h₄ := h₃.compRight
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp r s) (.up ℤ)).inv.app Q)
  exact h₄.compRight (eqToHom (congrArg (fun x ↦
    ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj Q) hc.symm))

private theorem scalarExtensionHom_nullHomotopicMap'
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (t : R →+* T) (hc : t = s.comp r)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (k : ∀ m n : ℤ, (ComplexShape.up ℤ).Rel n m →
      ((((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj P).X m ⟶
        (((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj Q).X n)) :
    let L := eqToHom (congrArg (fun x ↦
        ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj P) hc) ≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp r s) (.up ℤ)).hom.app P
    let R' := (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp r s) (.up ℤ)).inv.app Q ≫
      eqToHom (congrArg (fun x ↦
        ((ModuleCat.extendScalars x).mapHomologicalComplex (.up ℤ)).obj Q) hc.symm)
    scalarExtensionHom r s t hc P Q (Homotopy.nullHomotopicMap' k) =
      Homotopy.nullHomotopicMap' (fun m n hmn ↦
        L.f m ≫ (ModuleCat.extendScalars s).map (k m n hmn) ≫ R'.f n) := by
  dsimp only
  simp only [scalarExtensionHom, Homotopy.map_nullHomotopicMap',
    Homotopy.comp_nullHomotopicMap', Homotopy.nullHomotopicMap'_comp,
    HomologicalComplex.comp_f, Category.assoc]

/-- A homotopy between two stage chain maps after extension to the colimit
exists already after extension to a sufficiently late stage.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 for finite-presentation descent.
Proof: Choose the homotopy over the colimit. Its degree-minus-one components have
source `E₀` after base change, and only finitely many source degrees are nonzero.
Descend these components by finite presentation and take one common stage above `i`.
At that stage form the degree-zero maps given by the differential of this graded
family. Their equality to `f - g` holds over the colimit by the original homotopy
identity. Detect each of these finitely many equalities at a later stage, and take
one common upper bound. Set the remaining graded components to zero. The shape
condition and homotopy identities then hold in every degree, giving the asserted
homotopy. Canonical scalar-extension associativity identifies all extended maps
with `scalarExtensionHom`; proof irrelevance identifies the composition witnesses.
For a preorder, pass to its posetal reflection: identify mutually comparable
indices and choose representatives. Between mutually comparable indices `F` gives
inverse ring isomorphisms, since their composites are identities in the thin index
category. Thus the representative diagram is equivalent to the original diagram,
and their colimits and scalar extensions are canonically identified. Apply the
partial-order finite-presentation descent theorem to this representative diagram,
then transport back and choose an upper bound with the requested original index.
Alternatively its presentation-matrix proof works verbatim with directedness alone,
using the filtered-ring elementwise criterion, which requires no antisymmetry.
(blueprint: lem-pc-affine-perfect-homotopy-descent) -/
theorem affine_perfect_homotopy_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (f g : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (h : Nonempty (Homotopy
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm) E₀ K₀ f)
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm) E₀ K₀ g))) :
    ∃ (j : Set.Ici i₀) (hij : i ≤ j), Nonempty (Homotopy
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
        (F.map (homOfLE j.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hij))) E₀ K₀ f)
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
        (F.map (homOfLE j.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hij))) E₀ K₀ g)) := by
  classical
  have hEfp (n : ℤ) : Module.FinitePresentation (F.obj i₀) (E₀.X n) := by
    have := (hE.2 n).1
    have := (hE.2 n).2
    exact Module.finitePresentation_of_projective (F.obj i₀) (E₀.X n)
  have hKfp (n : ℤ) : Module.FinitePresentation (F.obj i₀) (K₀.X n) := by
    have := (hK.2 n).1
    have := (hK.2 n).2
    exact Module.finitePresentation_of_projective (F.obj i₀) (K₀.X n)
  obtain ⟨h⟩ := h
  let s := fun m n (_hmn : (ComplexShape.up ℤ).Rel n m) ↦ h.hom m n
  have hs : Homotopy.nullHomotopicMap' s =
      scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
        E₀ K₀ (f - g) := by
    rw [scalarExtensionHom_sub]
    apply HomologicalComplex.Hom.ext
    funext n
    simp only [HomologicalComplex.sub_f_apply]
    rw [Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
      (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)]
    have hn := h.comm n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at hn
    exact (eq_sub_iff_add_eq.mpr hn.symm)
  obtain ⟨j, hij, t, ht⟩ :=
    affine_perfect_gradedHom_descent F i₀ E₀ K₀ hE.1 hEfp hKfp i s
  have ht' : scalarExtensionHom
      (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
      (colimit.ι F i₀).hom
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property)).symm)
      E₀ K₀ (Homotopy.nullHomotopicMap' t) = Homotopy.nullHomotopicMap' s := by
    rw [scalarExtensionHom_nullHomotopicMap']
    congr 1
    funext m n hmn
    exact ht m n hmn
  obtain ⟨k, hik, hjk, heq⟩ := affine_perfect_chainMap_equality_detection
    F i₀ E₀ K₀ hE.1 hEfp hKfp i j (f - g) (Homotopy.nullHomotopicMap' t) (hs.symm.trans ht'.symm)
  refine ⟨k, hik, ⟨Homotopy.equivSubZero.symm ?_⟩⟩
  rw [← scalarExtensionHom_sub, heq]
  have htzero := scalarExtensionHom_homotopy
    (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
    (F.map (homOfLE k.property)).hom
    (congrArg CommRingCat.Hom.hom (F.map_comp
      (homOfLE j.property) (homOfLE hjk))) E₀ K₀ _ _ (Homotopy.nullHomotopy' t)
  rwa [scalarExtensionHom_zero] at htzero

end CochainComplex
