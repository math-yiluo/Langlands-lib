/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The bounded-above flat tensor argument vanishes in one fixed degree.
This is the bounded-above case in Stacks Project, Cohomology on Sites,
Lemma 21.17.8 (Tag 06YQ), proved here by finite-column total comparison.
(blueprint: lem-pc-bounded-above-flat-tensor-acyclic-degree)

Proof: flip the tensor double complex so its columns are A tensored with a term of P.
Flatness makes these columns acyclic. Both degreewise upper bounds give uniform bounds
on the flipped double complex. Apply the bounded-above columnwise quasi-isomorphism
comparison to its map from zero, then transport exactness along the signed flip
isomorphism of total complexes. The comparison theorem uses finite column truncations
and their degreewise stabilization, so no spectral-sequence construction is needed. -/
theorem isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf
    (A P : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hAbounded : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (A.X i))
    (hPbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hPflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
    (hA : A.Acyclic) (n : ℤ) :
    (letI := SheafOfModules.monoidalCategory R
     HomologicalComplex.ExactAt (mapBifunctor A P (curriedTensor _)) n) := by
  let := SheafOfModules.monoidalCategory R
  -- The flipped columns are the images of A under exact tensor-right functors.
  let K := (((curriedTensor _).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A).obj P
  obtain ⟨a, ha⟩ := hAbounded
  obtain ⟨b, hb⟩ := hPbounded
  have hrows (j : ℤ) : (K.flip.X j).Acyclic := by
    have hflat := hPflat j
    change exactFunctor _ _ (tensorRight (P.X j)) at hflat
    have : PreservesFiniteLimits (tensorRight (P.X j)) := hflat.1
    have : PreservesFiniteColimits (tensorRight (P.X j)) := hflat.2
    have : (tensorRight (P.X j)).Additive :=
      Functor.additive_of_preserves_binary_products _
    exact hA.map (tensorRight (P.X j))
  have hright (i : ℤ) : IsStrictlyLE (K.flip.X i) a := by
    rw [isStrictlyLE_iff]
    intro j hj
    exact (tensorRight (P.X i)).map_isZero (ha j hj)
  have htop : IsStrictlyLE K.flip b := by
    rw [isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    ext j : 1
    exact (tensorLeft (A.X j)).map_isZero (hb i hi) |>.eq_of_src _ _
  let Z : HomologicalComplex₂
    (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) := HasZeroObject.zero.choose
  have : IsStrictlyLE Z b := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
  have (i : ℤ) : IsStrictlyLE (Z.X i) a := by
    rw [isStrictlyLE_iff]
    intro j hj
    exact (HomologicalComplex.eval _ _ j).map_isZero
      ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))
  have : K.flip.HasTotal (ComplexShape.up ℤ) :=
    K.flip.hasTotal_of_isStrictlyLE b a
  have : Z.HasTotal (ComplexShape.up ℤ) := Z.hasTotal_of_isStrictlyLE b a
  -- The source comparison truncates to finitely many columns in each fixed degree.
  let f : Z ⟶ K.flip := 0
  have hf (i : ℤ) : QuasiIso (f.f i) := by
    rw [quasiIso_iff]
    intro j
    apply (quasiIsoAt_iff_exactAt (f.f i) j ?_).2 (hrows i j)
    exact HomologicalComplex.acyclic_of_isZero (Z.X i)
      ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)) j
  have : QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) :=
    HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE f b a hf
  have hz : (Z.total (ComplexShape.up ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _
      (HomologicalComplex₂.total.isZero Z (ComplexShape.up ℤ) (isZero_zero _))
  have htotal : (K.flip.total (ComplexShape.up ℤ)).ExactAt n :=
    (quasiIsoAt_iff_exactAt
      (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) n (hz n)).1 inferInstance
  exact htotal.of_iso (K.totalFlipIso (ComplexShape.up ℤ))

end CochainComplex
