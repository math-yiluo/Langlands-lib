/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-! # Concrete restricted Cartan--Eilenberg totals

Source: Stacks Project, Tags 015J and 0133.
(blueprint: def-weil-pbc-etale-restricted-total-construction).
-/

@[expose] public section

universe uA vA uB vB u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- The finite-diagonal comparison, constructed from coproduct comparison maps and
extension by zero. No isomorphism is chosen from an existence statement.
Source: Stacks, Tag 015J; finite diagonals of the CE total.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleCEMappedTotalIso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s)) :
    (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
          (ComplexShape.up ℤ)) := by
  classical
  let J := (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip)
  let JF := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip)
  let b := hbelow.choose
  have hb := hbelow.choose_spec
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
  exact e

/-- Restrict complex degree to s ≥ q and extend by zero, retaining resolution degree.
Source: Stacks, Tag 015J, proof remark (3).
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleRestrictedBicomplex (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  T.I.stupidTrunc (ComplexShape.embeddingUpIntGE q)

/-- The actual sheaf-valued restricted total, before global sections.
Source: Stacks, Tags 015J and 0133.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleRestrictedTotal (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  (((CartanEilenbergPresentation.mappedFunctor
    (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).obj
      (etaleRestrictedBicomplex X K T q)).flip).total (ComplexShape.up ℤ)

/-- The restricted total is zero below q: the retained rows have s ≥ q.
Source: Stacks, Tags 015J and 0133. Proof: below q the outer stupid truncation
is a zero complex, since no nonnegative index is sent to s < q.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
theorem etaleRestrictedBicomplex_below (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero ((etaleRestrictedBicomplex X K T q).X s) := by
  refine ⟨q, ?_⟩
  intro s hs
  exact T.I.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE q) s
    (fun i hi ↦ by change q + (i : ℤ) = s at hi; omega)

/-- The explicit degree-zero summand map into the restricted total. It is zero
when n < q and is the row augmentation when n ≥ q.
Source: Stacks, Tag 015J and Tag 0133, augmented total construction.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleRestrictedAugmentationComponent (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q)).X n ⟶
      (etaleRestrictedTotal X K T q).X n :=
  (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f n ≫ (T.a.f n).f 0 ≫
    (T.I.πStupidTruncf (ComplexShape.embeddingUpIntGE q) n).f 0 ≫
    (HomologicalComplex.extendXIso
      (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((etaleRestrictedBicomplex X K T q).X n))
      ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor
      (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).obj
        (etaleRestrictedBicomplex X K T q)).flip).ιTotal
      (ComplexShape.up ℤ) 0 n n (zero_add n)

/-- Inclusion of the restricted mapped total into the full mapped total.
Source: Stacks, Tag 015J; totalization of the column inclusion.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleRestrictedMappedInclusion (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{u + 1}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).map
            (T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))) (ComplexShape.up ℤ)

/-- The inclusion from Γ of the restricted sheaf total, using the finite-diagonal
comparison in the inverse direction. Source: Stacks, Tag 015J.
(blueprint: def-weil-pbc-etale-restricted-total-construction). -/
noncomputable def etaleRestrictedSectionsInclusion (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  (etaleCEMappedTotalIso (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (etaleRestrictedBicomplex X K T q) (etaleRestrictedBicomplex_below X K T q)).inv ≫
      etaleRestrictedMappedInclusion X K T q

end AlgebraicGeometry.Etale
