/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.CategoryTheory.CartanEilenbergConeFiltration
import WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Quasi-isomorphism of the augmented total

Source: Stacks Project, Homology, Tag 0133 (Lemma 12.25.4), and Derived
Categories, Tag 015J, proof remark (3).
(blueprint: lem-sp-cartan-eilenberg-augmentation-quasi-iso).
-/

@[expose] public section

universe uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Exact augmented columns give a quasi-isomorphism to their bounded-diagonal total.
No injectivity hypothesis is needed, and the augmentation is supplied as a chain map.
Source: Stacks Project, Homology, Tag 0133 (Lemma 12.25.4); Derived Categories,
Tag 015J, proof remark (3).
(blueprint: lem-sp-cartan-eilenberg-augmentation-quasi-iso).

Proof.
1. Choose b with I zero in complex degrees below b. Extend resolution degree by zero.
The diagonal in total degree n has only the finitely many terms with 0 <= r <= n-b.
For the cone, choose also a lower bound for K: hrows identifies K^s with the
zeroth cohomology of I^{s,bullet}, so K^s is zero for s < b.
2. Augment each resolution column by K^s in resolution degree -1 with differential
(a.f s).f 0. These columns are acyclic: hrows says their unaugmented columns have
only degree-zero cohomology, identified with K^s by a.f s. Horizontal differentials
commute with the augmentation because a is a bicomplex map.
3. Totalize the augmented bicomplex after exchanging the indices. In total degree n,
its objects are Tot(I)^n plus K^{n+1}. Multiply the K summands by the usual cone
signs to identify its differential with that of mappingCone aug. The equation haug
identifies the off-diagonal part with this particular aug, not merely an arbitrary
map inducing abstract cohomology isomorphisms.
4. Filter the augmented total by complex degree s. This filtration is finite in each
cochain degree, and its graded complexes are shifts of the acyclic augmented columns.
The associated spectral sequence has zero first page. For a fixed cohomology degree n,
choose a page beyond all filtration bounds in degrees n-1, n and n+1. The cycle and
boundary subquotients have then stabilized to the graded pieces of cohomology.
They are zero, so the finite exhaustive separated filtration of H^n is zero.
5. The cone is acyclic in every degree. The acyclic-cone criterion gives QuasiIso aug.
This argument also covers empty diagonals and the zero bicomplex. -/
theorem cartanEilenberg_augmentation_quasiIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hrows : ∀ s : ℤ, QuasiIso (a.f s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n)) :
    QuasiIso aug := by
  obtain ⟨b, hb⟩ := hbelow
  have hKbelow (s : ℤ) (hs : s < b) : IsZero (K.X s) := by
    have : QuasiIso (a.f s) := hrows s
    have hi : IsZero ((I.X s).homology 0) :=
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) 0).map_isZero (hb s hs)
    have hk := (asIso (HomologicalComplex.homologyMap (a.f s) 0)).isZero_iff.mpr hi
    exact (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.up ℕ) 0 (K.X s)).isZero_iff.mp hk
  obtain ⟨F, _, hbounds, hgraded⟩ := cartanEilenberg_cone_filtration
    K I a b hb hKbelow aug haug
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic aug).mpr
  apply degreewiseFiltered_acyclic (CochainComplex.mappingCone aug) F
    (fun n ↦ ⟨b, n + 2, hbounds n⟩)
  intro p n
  obtain ⟨e⟩ := hgraded p n
  have : QuasiIso (a.f p) := hrows p
  have hcone := (CochainComplex.mappingCone.quasiIso_iff_acyclic
    (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).mp
      (inferInstance : QuasiIso _)
  exact ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
    (e.isZero_iff.mpr (hcone (n - p)).isZero_homology)

end CategoryTheory.Functor
