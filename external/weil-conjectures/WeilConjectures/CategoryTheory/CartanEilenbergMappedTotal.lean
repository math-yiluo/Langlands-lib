/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Additive functors commute with the finite Cartan--Eilenberg diagonals

Source: blueprint thm-sp-if-e1, proof paragraph 2, finite diagonal sums.
(blueprint: lem-sp-cartan-eilenberg-mapped-total).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor commutes with this totalization because each diagonal has
only finitely many nonzero terms. The comparison is fixed on the diagonal inclusions.
Source: blueprint thm-sp-if-e1, proof paragraph 2, finite diagonal sums.
(blueprint: lem-sp-cartan-eilenberg-mapped-total).

Proof.
1. Choose b below which I vanishes. In total degree n, extension by zero leaves only
indices (m,s) with 0 <= m and b <= s and m+s=n. This is a finite set, empty when n<b.
The full diagonal coproduct is canonically the finite coproduct on these indices;
the omitted summands are zero and have unique maps to every object.
2. An additive functor between abelian categories preserves finite biproducts and
zero objects. Hence the diagonal coproduct comparison is an isomorphism. Compose
it with the canonical extension-by-zero comparison in each summand. The resulting
maps satisfy precisely the displayed formula, including all zero summands.
3. On every diagonal summand the total differential is the sum of the two signed
bicomplex differentials. Additivity preserves sums and integer signs. Naturality
of extension and of the diagonal comparison proves commutation with this differential.
The degreewise isomorphisms therefore assemble into the asserted complex isomorphism. -/
theorem cartanEilenberg_mapped_total_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s)) :
    ∃ e : (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
          (ComplexShape.up ℤ)),
          (∀ (m : ℕ) (s n : ℤ) (h : (m : ℤ) + s = n),
            (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
                (ComplexShape.up ℤ) (m : ℤ) s n h ≫ e.hom.f n =
              (HomologicalComplex.extendXIso
                ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
                ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).hom ≫
              F.map ((HomologicalComplex.extendXIso
                  (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
                  ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
                  (ComplexShape.up ℤ) (m : ℤ) s n h)) := by
  classical
  let J := (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip)
  let JF := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip)
  obtain ⟨b, hb⟩ := hbelow
  have hz (r s : ℤ) (h : r < 0 ∨ s < b) : IsZero ((J.X r).X s) := by
    rcases h with h | h
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
    · exact (HomologicalComplex.eval A (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor A).map_isZero (hb s h))
  let κ (n : ℤ) : J.CoreHasTotal (ComplexShape.up ℤ) n :=
    { J := { s : ℤ // s ∈ Finset.Icc b n }
      φ₁ := fun s ↦ n - s
      φ₂ := fun s ↦ s
      π_φ := fun s ↦ by dsimp [ComplexShape.π]; omega
      hφ := by
        intro s t h
        apply Subtype.ext
        exact congrArg (fun x : ℤ × ℤ ↦ x.2) h
      isZero := by
        intro r s h hrs
        have hbounds : 0 ≤ r ∧ b ≤ s := by
          constructor <;> by_contra hbad
          · exact hrs (hz r s (Or.inl (by omega)))
          · exact hrs (hz r s (Or.inr (by omega)))
        refine ⟨⟨s, Finset.mem_Icc.mpr ⟨hbounds.2, ?_⟩⟩, ?_, rfl⟩
        · dsimp [ComplexShape.π] at h; omega
        · dsimp [ComplexShape.π] at h; dsimp; omega }
  let : F.PreservesTotalComplex J (ComplexShape.up ℤ) :=
    fun n ↦ (κ n).preserves F
  let eTotal := HomologicalComplex₂.mapTotalIso F J (ComplexShape.up ℤ)
  let j₀ := (NatIso.mapHomologicalComplex
    (ComplexShape.embeddingUpNat.mapExtendFunctorNatIso F) (ComplexShape.up ℤ)).app I
  let j := ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).mapIso j₀).symm
  let j' : JF ≅ (F.mapHomologicalComplex₂ (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj J := j
  let e := HomologicalComplex₂.total.mapIso j' (ComplexShape.up ℤ) ≪≫ eTotal
  refine ⟨e, ?_⟩
  intro m s n h
  dsimp [e]
  change _ ≫ (HomologicalComplex₂.total.map j'.hom (ComplexShape.up ℤ)).f n ≫
    (HomologicalComplex₂.mapTotalXIso F J (ComplexShape.up ℤ) n).hom = _
  rw [← Category.assoc,
    HomologicalComplex₂.ιTotal_map, Category.assoc,
    HomologicalComplex₂.ι_mapTotalXIso_hom]
  dsimp [j', j, j₀]
  have hr : ComplexShape.embeddingUpNat.r (m : ℤ) = some m :=
    ComplexShape.embeddingUpNat.r_f m
  have hx := HomologicalComplex.mapExtendX_hom_eq (I.X s) F hr
  simp only [HomologicalComplex₂.flipFunctor, NatIso.mapHomologicalComplex,
    ComplexShape.Embedding.mapExtendFunctorNatIso, HomologicalComplex.mapExtendIso]
  change (HomologicalComplex.mapExtendX (I.X s) F
    (ComplexShape.embeddingUpNat.r (m : ℤ))).inv ≫ _ = _
  rw [hx]
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
    eqToIso, F.map_comp, eqToHom_map]
  rw [← Category.assoc, eqToHom_trans]

end CategoryTheory.Functor
