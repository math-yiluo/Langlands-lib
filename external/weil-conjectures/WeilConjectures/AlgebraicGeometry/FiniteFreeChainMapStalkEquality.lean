/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Int.Interval
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapEquality

/-! # Detecting equality of bounded finite free chain maps near a point

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix equations after shrinking.
(blueprint: lem-pc-finite-free-chain-map-stalk-equality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private lemma restrict_eq_of_le {Y : Scheme.{u}} {U V W : Y.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) {M N : U.toScheme.Modules} (f g : M ⟶ N)
    (h : (restrictFunctor (Y.homOfLE hVU)).map f =
      (restrictFunctor (Y.homOfLE hVU)).map g) :
    (restrictFunctor (Y.homOfLE (hWV.trans hVU))).map f =
      (restrictFunctor (Y.homOfLE (hWV.trans hVU))).map g := by
  let e := restrictFunctorCongr (Y.homOfLE_homOfLE hWV hVU).symm ≪≫
    restrictFunctorComp (Y.homOfLE hWV) (Y.homOfLE hVU)
  apply (cancel_mono (e.hom.app N)).mp
  rw [e.hom.naturality f, e.hom.naturality g]
  exact congrArg (fun k ↦ e.hom.app M ≫
    (restrictFunctor (Y.homOfLE hWV)).map k) h

/-- Equality of two fixed chain maps at the stalk holds on a smaller open.

Source: lem-pc-finite-free-stalk-homotopy-p-only, step 3, expanding the finite
calculation in lemma-coherent-base-change-invertible-sheaves--3 (first two proof paragraphs).
(blueprint: lem-pc-finite-free-chain-map-stalk-equality)

Proof: Use the finite bases of P and their images under restriction, identified by
restrictFunctorIsoPullback and pullbackFreeIso. The degreewise differences a.f n-b.f n
are matrices of sections on U. Outside [0,d] their source is zero, so their components
are zero without shrinking. Within [0,d] there are finitely many entries. The equality
of the pulled-back chain maps says that the germs of these entries at y vanish, by
freeMatrix_pullback and the structure-ring stalk comparison for fromSpecStalkOfMem.
For each entry use the germ equality criterion to find an open containing y inside U
where it is zero. Intersect these finitely many opens, obtaining W. Restriction carries
the matrix to its restricted entries, so all component differences are zero on W.
Extensionality of morphisms of homological complexes gives the required equality.
The extra restriction through V merely transports the chosen bases; it imposes no
condition on a or b. The zero complex, rank zero, d=0, and U=V are covered by the same
argument, with an empty intersection taken to be U. -/
theorem exists_shrink_chainMap_eq_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U)
    (a b :
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)) ⟶
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)))
    (heq : ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a =
      ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map b) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      ((restrictFunctor (Y.homOfLE hWU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a =
      ((restrictFunctor (Y.homOfLE hWU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map b := by
  classical
  let K := ((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
    (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hn (n : ℤ) : ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      (restrictFunctor (Y.homOfLE hWU)).map (a.f n) =
        (restrictFunctor (Y.homOfLE hWU)).map (b.f n) := by
    obtain ⟨r, ⟨e⟩⟩ := hfree n
    let e' : K.X n ≅ (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) :=
      (restrictFunctor (Y.homOfLE hUV)).mapIso
        ((restrictFunctor V.ι).mapIso e ≪≫ restrictFreeIso V.ι _) ≪≫
        restrictFreeIso (Y.homOfLE hUV) _ ≪≫ (restrictFreeIso U.ι _).symm
    exact exists_restrict_eq_of_pullback_eq r y U hyU (K.X n) (K.X n)
      ⟨e'⟩ (a.f n) (b.f n) (congrArg (fun f ↦ f.f n) heq) U le_rfl hyU
  have hs (s : Finset ℤ) : ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      ∀ n ∈ s, (restrictFunctor (Y.homOfLE hWU)).map (a.f n) =
        (restrictFunctor (Y.homOfLE hWU)).map (b.f n) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨U, le_rfl, hyU, by simp⟩
    | @insert n s hns ih =>
      obtain ⟨W, hWU, hyW, hW⟩ := ih
      obtain ⟨T, hTU, hyT, hT⟩ := hn n
      refine ⟨W ⊓ T, inf_le_left.trans hWU, ⟨hyW, hyT⟩, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact restrict_eq_of_le hTU inf_le_right (a.f i) (b.f i) hT
      · exact restrict_eq_of_le hWU inf_le_left (a.f i) (b.f i) (hW i hi)
  obtain ⟨W, hWU, hyW, hW⟩ := hs (Finset.Icc 0 (d : ℤ))
  refine ⟨W, hWU, hyW, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n ∈ Finset.Icc 0 (d : ℤ)
  · exact hW n hn
  · have : P.IsStrictlyGE 0 := hge
    have : P.IsStrictlyLE (d : ℤ) := hle
    have hz : IsZero (K.X n) := by
      by_cases h : 0 ≤ n
      · have hdn : (d : ℤ) < n := by
          by_contra hdn
          exact hn (Finset.mem_Icc.mpr ⟨h, le_of_not_gt hdn⟩)
        exact CochainComplex.isZero_of_isStrictlyLE K d n hdn
      · exact CochainComplex.isZero_of_isStrictlyGE K 0 n (lt_of_not_ge h)
    exact congrArg (fun f ↦ (restrictFunctor (Y.homOfLE hWU)).map f)
      (hz.eq_of_src (a.f n) (b.f n))

end AlgebraicGeometry.Scheme.Modules
