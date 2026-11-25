/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.FiniteFreeApproximationTriangle
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Algebra.Homology.BoundedComplexTermAmplitude
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite free approximation in one homology degree

Source: Stacks Project, Tag 0944, and the current scalar-extension blueprint
clause (2), bpq #46. (blueprint: lem-sp-finite-free-approximation-homology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w x y z
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
/-- Bounded complexes are finite iterated extensions of their terms placed in their
actual degrees. Source: Stacks 066H
(blueprint: lem-sp-finite-free-approximation-homology).
Proof: induct on the length of the support, using the degreewise split stupid
truncation triangle. A single supported degree is the single complex, and an empty
support is zero. This reuses the source-library bounded-term induction. -/
theorem bounded_mem_of_single_terms
    {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D] [HasZeroObject D]
    (S : ObjectProperty (HomotopyCategory D (.up ℤ)))
    [S.IsTriangulatedClosed₂] [S.IsClosedUnderIsomorphisms] [S.ContainsZero]
    (K : CochainComplex D ℤ) (r s : ℤ) [K.IsStrictlyGE r] [K.IsStrictlyLE s]
    (hK : ∀ n : ℤ, r ≤ n → n ≤ s → S ((HomotopyCategory.singleFunctor D n).obj (K.X n))) :
    S ((HomotopyCategory.quotient D _).obj K) := by
  by_cases h₀ : r ≤ s
  · obtain ⟨n, hn⟩ := Int.le.dest h₀
    clear h₀
    revert K hn r s
    induction n with
    | zero =>
        intro K r s _ _ hK hrs
        obtain rfl : r = s := by simpa using hrs
        exact S.prop_of_iso
          ((HomotopyCategory.singleFunctorPostcompQuotientIso D r).app _ ≪≫
            ((HomotopyCategory.quotient D _).mapIso (K.isoSingle r)).symm)
          (hK r (by rfl) (by rfl))
    | succ n ih =>
        intro K r s _ _ hK hrs
        apply S.ext_of_isTriangulatedClosed₂ _
          (HomotopyCategory.trianglehOfDegreewiseSplit_distinguished _
            (K.shortComplexStupidTruncSplitting
              (ComplexShape.Embedding.embeddingUpInt_areComplementary (r + n) s (by omega))))
        · dsimp
          refine @ih _ (r + 1) s
            (CochainComplex.isStrictlyGE_of_ge _ _ s (by omega)) inferInstance
            (fun m h₁ h₂ ↦ ?_) (by omega)
          obtain h₃ | rfl := h₂.lt_or_eq
          · apply S.prop_of_isZero
            apply Functor.map_isZero
            exact CochainComplex.isZero_of_isStrictlyGE _ s _ h₃
          · obtain ⟨k, hk⟩ := Int.le.dest h₂
            exact S.prop_of_iso ((HomotopyCategory.singleFunctor D m).mapIso
              ((CategoryTheory.Iso.ofIsIso
                (K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE m) (i := k)
                  (by dsimp; omega))).symm))
              (hK m (by omega) h₂)
        · dsimp
          refine @ih _ r (r + n) inferInstance inferInstance (fun m h₁ h₂ ↦ ?_) rfl
          obtain ⟨k, hk⟩ := Int.le.dest h₂
          exact S.prop_of_iso ((HomotopyCategory.singleFunctor D m).mapIso
            (CategoryTheory.Iso.ofIsIso
              (K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE (r + n)) (i := k)
                (by dsimp; omega))))
            (hK m h₁ (by omega))
  · have hzero : IsZero K := by
      rw [IsZero.iff_id_eq_zero]
      ext n
      apply IsZero.eq_of_src
      by_cases hn : r ≤ n
      · exact K.isZero_of_isStrictlyLE s n (by omega)
      · exact K.isZero_of_isStrictlyGE r n (by omega)
    exact S.prop_of_isZero ((HomotopyCategory.quotient D _).map_isZero hzero)


end CochainComplex

namespace DerivedCategory

/-- Finite free terms map into a triangulated class once the rank-one term does.
Source: Stacks 0944 (blueprint: lem-sp-finite-free-approximation-homology).
Proof: a finite free module is a finite power of R, including the zero-ring case.
An additive functor preserves finite products. The image of a single in degree i
is the shift by -i of its image in degree zero. -/
theorem triangulatedImage_single_free
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {A : Type v} [Category.{x} A] [Abelian A] [HasDerivedCategory.{y} A]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory A)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedCategory A))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (hR : P (F.obj ((singleFunctor _ 0).obj (ModuleCat.of R R))))
    (M : ModuleCat.{u} R) (i : ℤ) [Module.Free R M] [Module.Finite R M] :
    P (F.obj ((singleFunctor _ i).obj M)) := by
  classical
  have hcoords : ∃ n : ℕ, Nonempty (M ≅ ModuleCat.of R (Fin n → R)) := by
    by_cases h : Nontrivial R
    · let := h
      exact ⟨Module.finrank R M, ⟨(Module.finBasis R M).equivFun.toModuleIso⟩⟩
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
      have : Subsingleton M := Module.subsingleton R M
      exact ⟨0, ⟨(LinearEquiv.ofSubsingleton (R := R) M (Fin 0 → R)).toModuleIso⟩⟩
  obtain ⟨n, ⟨em⟩⟩ := hcoords
  let G := singleFunctor (ModuleCat.{u} R) 0 ⋙ F
  let N : Fin n → ModuleCat.{u} R := fun _ ↦ ModuleCat.of R R
  let e : M ≅ ∏ᶜ N := em ≪≫ (ModuleCat.piIsoPi N).symm
  have h₀ : P (F.obj ((singleFunctor _ 0).obj M)) :=
    P.prop_of_iso (G.mapIso e ≪≫ PreservesProduct.iso G N).symm
      (P.prop_product (fun _ ↦ hR))
  exact P.prop_of_iso ((F.commShiftIso (-i)).symm.app _ ≪≫
    F.mapIso (((singleFunctors (ModuleCat.{u} R)).shiftIso (-i) i 0 (by omega)).app M))
      (P.le_shift (-i) _ h₀)

/-- A triangulated functor with a uniform upper bound admits finite-free comparisons
in every homology degree at every finitely presented module over a Noetherian ring.
Source: Stacks 0944; blueprint scalar extension (2), bpq #46
(blueprint: lem-sp-finite-free-approximation-homology).
Proof: choose a bounded finite-free approximation to M[0] whose error cone is at most
r-d-2. Its image cone is at most r-2. The long exact homology sequence makes the
comparison invertible in degree r. The approximation image lies in P by the bounded-term
induction, since each finite-free single term lies there. This is the finite iterated
cone and stupid truncation argument; no stratification or Noetherian scheme is used. -/
theorem finiteModuleImage_homology_approximation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {A : Type v} [Category.{x} A] [Abelian A] [HasDerivedCategory.{y} A]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory A)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedCategory A))
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
    (d : ℤ)
    (hbound : ∀ (N : DerivedCategory (ModuleCat.{u} R)) (c : ℤ),
      N.IsLE c → (F.obj N).IsLE (c + d))
    (hfree : ∀ (M : ModuleCat.{u} R) (i : ℤ),
      Module.Free R M → Module.Finite R M → P (F.obj ((singleFunctor _ i).obj M)))
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] (r : ℤ) :
    ∃ V : DerivedCategory A, P V ∧ Nonempty
      ((homologyFunctor A r).obj V ≅
        (homologyFunctor A r).obj (F.obj ((singleFunctor _ 0).obj M))) := by
  obtain ⟨E, a, b, T, hEa, hEb, hfreeE, hT, hT₁, hT₂, hT₃⟩ :=
    exists_finiteFree_approximation_triangle R M (r - d - 2)
  let := hEa
  let := hEb
  let S := P.inverseImage (Qh ⋙ F)
  have hV : P (F.obj (Q.obj E)) := by
    have h : S ((HomotopyCategory.quotient (ModuleCat.{u} R) _).obj E) := by
      apply CochainComplex.bounded_mem_of_single_terms S E a b
      intro i _ _
      let e := Qh.mapIso ((HomotopyCategory.singleFunctorPostcompQuotientIso
        (ModuleCat.{u} R) i).app (E.X i)) ≪≫ (quotientCompQhIso (ModuleCat.{u} R)).app
          ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) i).obj (E.X i))
      change P (F.obj (Qh.obj ((HomotopyCategory.singleFunctor _ i).obj (E.X i))))
      apply P.prop_of_iso (F.mapIso e).symm
      obtain ⟨n, ⟨en⟩⟩ := hfreeE i
      have hfr : Module.Free R (E.X i) := Module.Free.of_equiv en.symm.toLinearEquiv
      have hfi : Module.Finite R (E.X i) := Module.Finite.equiv en.symm.toLinearEquiv
      exact hfree _ i hfr hfi
    exact P.prop_of_iso (F.mapIso ((quotientCompQhIso _).app E)) h
  let U := F.mapTriangle.obj T
  have hU := F.map_distinguished T hT
  have hb : U.obj₃.IsLE (r - 2) := by
    convert hbound T.obj₃ (r - d - 2) hT₃ using 1 <;> congr 1
    omega
  have hz (i : ℤ) (hi : r - 2 < i) : IsZero ((homologyFunctor A i).obj U.obj₃) :=
    (isLE_iff U.obj₃ (r - 2)).1 hb i hi
  have hepi : Epi ((homologyFunctor A r).map U.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff U hU r).2
      ((hz r (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((homologyFunctor A r).map U.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff U hU (r - 1) r).2
      ((hz (r - 1) (by omega)).eq_of_src _ _)
  let := hepi
  let := hmono
  have : IsIso ((homologyFunctor A r).map U.mor₁) := isIso_of_mono_of_epi _
  let e := asIso ((homologyFunctor A r).map U.mor₁)
  refine ⟨F.obj (Q.obj E), hV, ⟨?_⟩⟩
  exact (homologyFunctor A r).mapIso (F.mapIso (eqToIso hT₁).symm) ≪≫ e ≪≫
    (homologyFunctor A r).mapIso (F.mapIso (eqToIso hT₂))

end DerivedCategory
