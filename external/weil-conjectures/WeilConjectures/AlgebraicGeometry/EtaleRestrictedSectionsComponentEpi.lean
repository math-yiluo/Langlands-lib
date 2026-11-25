/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsFactors

/-! # Degreewise epimorphism of the restricted sections lift

Source: Stacks Project, Tag 015J, total-complex comparison and column filtration.
(blueprint: lem-weil-pbc-etale-restricted-sections-component-epi).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The restricted sections factor map is epimorphic in every degree.
Source: Stacks Project, Tag 015J, proof remark (3), finite diagonal comparison.
(blueprint: lem-weil-pbc-etale-restricted-sections-component-epi).
Proof: Write J for the full mapped bicomplex after flipping. The second-filtration
step in degree n is the finite supremum of the images of its coprojections at
(n-s,s), q ≤ s ≤ n. For each retained s the stupid-truncation inclusion is an
isomorphism on the resolution complex in degree s. Applying sections and extension
by zero therefore identifies the restricted summand with the full summand.
The total inclusion composed with its restricted coprojection is the full
coprojection under this identification. The full coprojection thus factors through
the total inclusion, so each generating image lies in the image of that inclusion.
Conversely every restricted coprojection maps into one of those generating images:
if s < q or n-s < 0 its source is zero; otherwise q ≤ s ≤ n. The total coproduct
universal property gives the converse image containment. Hence this image is
exactly the finite supremum. The explicit comparison is an isomorphism and does
not change the image on precomposition. T.filtration_formula identifies the image
with the degree-n step. Evaluating factorThru_arrow gives the factorization through
that step, which is therefore epic in AddCommGrpCat. If n < q the supremum and
restricted total are zero. Negative q and zero summands satisfy the same argument. -/
theorem etaleRestrictedSectionsLift_component_epi
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    Epi (((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
      (etaleRestrictedSections_factors X K T q)).f n) := by
  classical
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj T.I).flip
  let R := ((CartanEilenbergPresentation.mappedFunctor F).obj
    (etaleRestrictedBicomplex X K T q)).flip
  let f := (etaleRestrictedSectionsInclusion X K T q).f n
  let m := (etaleRestrictedMappedInclusion X K T q).f n
  let g := ((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
    (etaleRestrictedSections_factors X K T q)).f n
  let a := (T.L.step q).arrow.f n
  have hg : g ≫ a = f := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun h ↦ h.f n) ((T.L.step q).factorThru_arrow
        (etaleRestrictedSectionsInclusion X K T q)
        (etaleRestrictedSections_factors X K T q))
  have him : imageSubobject f = imageSubobject m := by
    dsimp [f, etaleRestrictedSectionsInclusion]
    exact imageSubobject_iso_comp _ _
  have hle : imageSubobject f ≤ Subobject.mk a :=
    imageSubobject_le_mk a f g hg
  have hge : Subobject.mk a ≤ imageSubobject f := by
    change Subobject.mk ((T.L.step q).arrow.f n) ≤ imageSubobject f
    rw [← imageSubobject_mono, ← DecreasingFiltration.complexStep,
      T.filtration_formula]
    change (Finset.Icc q n).sup (fun s ↦ imageSubobject
      (J.ιTotalOrZero (ComplexShape.up ℤ) (n - s) s n)) ≤ imageSubobject f
    apply Finset.sup_le
    intro s hs
    have hqs : q ≤ s := (Finset.mem_Icc.mp hs).1
    have he : (ComplexShape.embeddingUpIntGE q).f (s - q).toNat = s := by
      change q + ((s - q).toNat : ℤ) = s
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have : IsIso ((T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f s) :=
      T.I.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE q) he
    have : IsIso ((G.map ((T.I.ιStupidTrunc
        (ComplexShape.embeddingUpIntGE q)).f s)).f (n - s)) := inferInstance
    have hdiag : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (n - s, s) = n := by
      change (n - s) + s = n
      omega
    have hcomp : R.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag ≫ m =
        (G.map ((T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)).f s)).f (n - s) ≫
          J.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag := by
      dsimp [m, etaleRestrictedMappedInclusion]
      rw [HomologicalComplex₂.ιTotal_map]
      rfl
    rw [J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - s) s n hdiag, him]
    calc
      imageSubobject (J.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag) =
          imageSubobject (R.ιTotal (ComplexShape.up ℤ) (n - s) s n hdiag ≫ m) := by
        rw [hcomp, imageSubobject_iso_comp]
      _ ≤ imageSubobject m := imageSubobject_comp_le _ _
  have heq : imageSubobject f = Subobject.mk a := le_antisymm hle hge
  let g' := g ≫ (Subobject.underlyingIso a).inv
  have : Epi g' := epi_of_imageSubobject_comp_arrow_eq g' (by
    simpa [g', hg] using heq)
  have : Epi (g' ≫ (Subobject.underlyingIso a).hom) := inferInstance
  simpa only [g', Category.assoc, Iso.inv_hom_id, Category.comp_id] using this

end AlgebraicGeometry.Etale
