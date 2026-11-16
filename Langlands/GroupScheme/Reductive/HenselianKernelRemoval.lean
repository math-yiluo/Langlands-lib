import Langlands.GroupScheme.Reductive.FiniteKernelPart
import Langlands.GroupScheme.Reductive.StrictHenselianDvrKernelRemovalStatement
import Langlands.GroupScheme.Torus.IsomorphismLocus

/-! # Kernel removal conditional on Henselian finite-part existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A residue-fibre isomorphism remains an isomorphism at any field-valued
point lying above that residue point. -/
theorem isIso_fieldPoint_of_residueFibre
    {S : Scheme.{u}} {G H : GroupScheme S} (f : G ⟶ H)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hf : IsIso ((baseChange
      (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).map f)) :
    IsIso ((baseChange b).map f) := by
  let s := b (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo b)
  have : IsIso ((baseChange (S.fromSpecResidueField s)).map f) := hf
  have h := (TorusIsomorphismLocus.isIso_comp_baseChange_iff
    (S.fromSpecResidueField s) (Spec.map φ) f).mpr inferInstance
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S b
  rwa [hfactor] at h

namespace HenselianKernelRemoval

variable (hfinite : Langlands.AlgebraicGeometry.HenselianFinitePartStatement.{u})
  {R : Type u} [CommRing R] [HenselianLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
  (hf : IsFibrewiseIsogeny f)

/-- Choose an actual finite clopen part of the full kernel, using precisely
the supplied general Henselian existence hypothesis. -/
def finitePart :
    {U : (kernel f).X.left.Opens //
      Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart (kernel f).X.hom U} := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom H.X.hom := hH.isAffineHom
  have hcomp : (kernelι f).hom.hom.left ≫ G.X.hom = (kernel f).X.hom :=
    Over.w (kernelι f).hom.hom
  have : IsAffineHom (kernel f).X.hom := by
    rw [← hcomp]
    infer_instance
  have : LocallyOfFiniteType (kernel f).X.hom := by
    rw [← hcomp]
    infer_instance
  have : LocallyQuasiFinite f.hom.hom.left :=
    locallyQuasiFinite_of_isogeny_fibres f hf
  have : LocallyQuasiFinite (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) inferInstance
  have hex := hfinite R (kernel f).X.left (kernel f).X.hom
    inferInstance inferInstance inferInstance inferInstance
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- The actual reductive quotient and remaining map obtained from Henselian
finite-part existence. Its specified canonical closed fibre is invertible. -/
def reductiveQuotient :
    ReductiveKernelQuotientFactorization f
      (FiniteKernelPart.inclusion f (finitePart hfinite hG hH f hf).property)
      ((Spec (CommRingCat.of R)).fromSpecResidueField (IsLocalRing.closedPoint R)) :=
  FiniteKernelPart.reductiveQuotient f
    (finitePart hfinite hG hH f hf).property hG hH hf

/-- The same remaining map is invertible on the special fibre defined by
the quotient map from the local ring to its residue field. -/
theorem isIso_specialFibre :
    IsIso ((baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).map
      (reductiveQuotient hfinite hG hH f hf).remaining) := by
  apply isIso_fieldPoint_of_residueFibre
  have hb : (Spec.algebraMap R (IsLocalRing.ResidueField R))
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
        IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  rw [hb]
  exact (reductiveQuotient hfinite hG hH f hf).isIso

end HenselianKernelRemoval

/-- General Henselian finite-part existence supplies the exact kernel-removal
statement over strictly Henselian discrete valuation rings. -/
theorem strictHenselianDvrKernelRemoval_of_henselianFinitePart
    (hfinite : Langlands.AlgebraicGeometry.HenselianFinitePartStatement.{u}) :
    StrictHenselianDvrKernelRemovalStatement.{u} := by
  intro R _ _ _ _ _ G H hG hH f hf
  let d := HenselianKernelRemoval.reductiveQuotient hfinite hG hH f hf
  refine ⟨d.quotient.quotient, d.quotient.projection, d.remaining,
    d.quotient.reductive,
    ⟨d.quotient.finite, d.quotient.isFppfQuotient.1,
      d.quotient.isFppfQuotient.2.1⟩,
    d.fac, d.fibrewise, ?_⟩
  exact HenselianKernelRemoval.isIso_specialFibre hfinite hG hH f hf

end Langlands.GroupScheme
