/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Universal tensor acyclicity implies K-flatness

Source: Stacks Project, More on Algebra, Tag 0E8F,
`lemma-universally-acyclic-K-flat`, specialized to commutative rings
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CochainComplex

private lemma acyclic_of_filtered_colimit
    {D I : Type*} [Category* D] [Abelian D] [Category* I]
    [Limits.HasColimitsOfShape I D] [HasExactColimitsOfShape I D]
    (F : I ⥤ CochainComplex D ℤ) (c : Limits.Cocone F) (hc : Limits.IsColimit c)
    (hF : ∀ j, (F.obj j).Acyclic) : c.pt.Acyclic := by
  intro i
  let S : ShortComplex (I ⥤ D) :=
    (ShortComplex.functorEquivalence I D).inverse.obj
      (F ⋙ HomologicalComplex.shortComplexFunctor D (.up ℤ) i)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro j
    exact Limits.IsZero.of_iso ((hF j i).isZero_homology)
      (S.mapHomologyIso ((evaluation I D).obj j)).symm
  have hc₁ := Limits.isColimitOfPreserves
    (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc
  have hc₂ := Limits.isColimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i) hc
  have hc₃ := Limits.isColimitOfPreserves
    (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).next i)) hc
  exact Limits.colim.exact_mapShortComplex hS hc₁ hc₂ hc₃
    (c.pt.d _ i) (c.pt.d i _)
    (fun j ↦ (c.ι.app j).comm _ _) (fun j ↦ (c.ι.app j).comm _ _)

private lemma acyclic_of_iso {D : Type*} [Category* D] [Abelian D]
    {K L : CochainComplex D ℤ} (e : K ≅ L) (hK : K.Acyclic) : L.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Limits.IsZero.of_iso (hK i).isZero_homology
    ((HomologicalComplex.homologyFunctor D (.up ℤ) i).mapIso e).symm

private lemma acyclic_all_of_single
    {A : Type u} [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ)
    (Fh : HomotopyCategory (ModuleCat.{u} A) (.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{u} A) (.up ℤ))
    [Fh.CommShift ℤ] [Fh.IsTriangulated] [Limits.PreservesColimitsOfShape ℤ F]
    (e : HomotopyCategory.quotient _ _ ⋙ Fh ≅ F ⋙ HomotopyCategory.quotient _ _)
    (h : ∀ M : ModuleCat.{u} A,
      (F.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)).Acyclic)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) : (F.obj K).Acyclic := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_shrink _
  let P := (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} A)).inverseImage Fh
  have hb (L : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
      [L.IsStrictlyGE a] [L.IsStrictlyLE b] : (F.obj L).Acyclic := by
    have hL : P ((HomotopyCategory.quotient _ _).obj L) := by
      apply HomotopyCategory.mem_subcategory_of_strictly_bounded P L a b
      intro n _ _
      apply (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
        (Fh.mapIso ((HomotopyCategory.singleFunctorPostcompQuotientIso
          (ModuleCat.{u} A) 0).symm.app (L.X n)))
      apply (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
        (e.symm.app ((HomologicalComplex.single _ (.up ℤ) 0).obj (L.X n)))
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
        (h (L.X n))
    apply (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (e.app L) hL
  have hle (L : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
      [L.IsStrictlyLE b] : (F.obj L).Acyclic := by
    let c := L.coconeStupidFiltrationGE.whisker Int.opEquivalence.symm.functor
    have hc : Limits.IsColimit c :=
      L.isColimitCoconeStupidFiltrationGE.whiskerEquivalence Int.opEquivalence.symm
    apply acyclic_of_filtered_colimit _ (F.mapCocone c) (Limits.isColimitOfPreserves F hc)
    intro j
    exact hb (L.stupidTrunc (ComplexShape.embeddingUpIntGE (-j))) (-j) b
  apply acyclic_of_filtered_colimit _ (F.mapCocone K.filtrationLECocone)
    (Limits.isColimitOfPreserves F K.isColimitFiltrationLECocone)
  intro j
  exact hle (K.truncLE j) j

/-- If tensoring an arbitrary module complex with every finitely presented module
in degree zero is acyclic, the complex is K-flat. There is no boundedness or
termwise flatness hypothesis.

Source: Stacks Project, More on Algebra, Tag 0E8F,
`lemma-universally-acyclic-K-flat`
(auxiliary; not a blueprint node).

Proof:
1. Filtered colimits of acyclic module complexes are acyclic: represent a cycle
   at one stage, pass to a later stage where its differential vanishes, and use
   acyclicity there to obtain a primitive. Use
   lem-weil-pbc-filtered-colimit-modules-elementwise.
2. Total tensor commutes with degreewise directed colimits. Tensor commutes with
   colimits by lem-weil-pbc-tensor-commutes-with-colimits, and coproducts commute
   with colimits. The comparison preserves both signed differential terms.
3. Express any module as a directed colimit of finitely presented modules using
   lem-trf-module-finitely-presented-directed-colimit. Steps 1 and 2 extend the
   hypothesis to every module. Interchange the degree-zero module and the other
   factor; this introduces no sign.
4. A complex supported in one degree has acyclic total tensor by step 3: shifting
   only multiplies the differential by a sign and reindexes the degrees. The
   zero complex also has zero tensor.
5. Induct on the length of a finite supporting interval. The brutal truncation
   sequence separating its bottom degree is split degreewise, so remains exact
   after tensoring and totalization. Apply the homology long exact sequence
   lem-weil-pbc-complex-ses-homology-long-exact and the induction hypothesis.
6. Any bounded-above complex is the degreewise directed colimit of its bounded
   brutal lower truncations. Steps 1, 2 and 5 prove tensor acyclicity for it;
   acyclicity of the brutal truncations themselves is unnecessary.
7. Any complex is the degreewise directed colimit of its canonical upper
   truncations: in the top degree use the kernel of the outgoing differential.
   At each fixed degree the system is eventually constant. Steps 1, 2 and 6
   give tensor acyclicity for an arbitrary complex.
8. In particular the total tensor with every acyclic complex is acyclic, exactly
   def-pc-module-kflat-complex. The recorded predicate expresses the equivalent
   preservation of quasi-isomorphisms on both sides, by cones and symmetry. -/
theorem kFlat_of_acyclic_tensor_finitePresentation
    {A : Type u} [CommRing A] (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (hE : ∀ (M : ModuleCat.{u} A), Module.FinitePresentation A M →
      (mapBifunctor E
        ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj M)
        (curriedTensor (ModuleCat.{u} A))).Acyclic) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat E := by
  let T := ((curriedTensor (ModuleCat.{u} A)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).obj E
  have hsingle (M : ModuleCat.{u} A) :
      (T.obj ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj M)).Acyclic := by
    obtain ⟨I, p, hn, hd, F, hF, c, he, ⟨hc⟩⟩ :=
      Module.exists_directed_colimit_finitePresentation A M
    let := p
    have := hn
    have := hd
    let G := HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0 ⋙ T
    have h := acyclic_of_filtered_colimit (F ⋙ G) (G.mapCocone c)
      (Limits.isColimitOfPreserves G hc) (fun j ↦ hE (F.obj j) (hF j))
    change (G.obj c.pt).Acyclic at h
    rw [he] at h
    exact acyclic_of_iso
      (T.mapIso ((HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).mapIso
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).toModuleIso)) h
  let Q := HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let B := (curriedTensor (ModuleCat.{u} A)).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)
  have hall (K : CochainComplex (ModuleCat.{u} A) ℤ) : (T.obj K).Acyclic :=
    acyclic_all_of_single T (B.obj (Q.obj E)) (Iso.refl _) hsingle K
  let T' := ((curriedTensor (ModuleCat.{u} A)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj E
  have hsingle' (M : ModuleCat.{u} A) :
      (T'.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)).Acyclic := by
    apply acyclic_of_iso
      (mapBifunctorSingle₂Iso (curriedTensor (ModuleCat.{u} A)) M E ≪≫
        (NatIso.mapHomologicalComplex
          (BraidedCategory.tensorLeftIsoTensorRight M).symm (.up ℤ)).app E ≪≫
        (mapBifunctorSingle₁Iso (curriedTensor (ModuleCat.{u} A)) M E).symm)
    exact hsingle M
  have hall' (K : CochainComplex (ModuleCat.{u} A) ℤ) : (T'.obj K).Acyclic :=
    acyclic_all_of_single T' (B.flip.obj (Q.obj E))
      (Iso.refl _) hsingle' K
  change HomologicalComplex.preservesQuasiIso T ∧ HomologicalComplex.preservesQuasiIso T'
  constructor
  · apply (Functor.preservesQuasiIso_iff_of_factors
      (F' := B.obj (Q.obj E)) (Iso.refl _)).1
    rw [HomotopyCategory.preservesQuasiIso_iff_preserves_acyclic]
    intro Z _
    obtain ⟨K, rfl⟩ := Z.quotient_obj_surjective
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hall K)
  · apply (Functor.preservesQuasiIso_iff_of_factors
      (F' := B.flip.obj (Q.obj E)) (Iso.refl _)).1
    rw [HomotopyCategory.preservesQuasiIso_iff_preserves_acyclic]
    intro Z _
    obtain ⟨K, rfl⟩ := Z.quotient_obj_surjective
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hall' K)

end CochainComplex
