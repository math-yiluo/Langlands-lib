import Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientTransport
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent

/-! # Reductive quotients along an actual residue recovery isomorphism -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace SpecialFibreQuotientData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsLocalRing R] [IsLocalRing A] [IsLocalHom (algebraMap R A)]
  {H : GroupScheme (Spec (CommRingCat.of L))}
  {D : RelativeComponentModelData R K G}
  {E : RelativeComponentModelData A L H}

local notation "resExt" =>
  algebraBaseMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)

/-- Change residue coefficients and recover on the specified upper special
fibre, keeping the literal residue base change of the original quotient. -/
def baseChangeSpecialFibreIso (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre) : SpecialFibreQuotientData E :=
  (Q.baseChange A L).transportSpecialFibreIso
    ((specialFibreSquareIso A D.neutral.group).symm ≪≫ e)

@[simp]
theorem baseChangeSpecialFibreIso_quotient (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre) :
    (Q.baseChangeSpecialFibreIso A L e).quotient =
      (GroupScheme.baseChange resExt).obj Q.quotient := rfl

@[simp]
theorem baseChangeSpecialFibreIso_projection (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre) :
    (Q.baseChangeSpecialFibreIso A L e).projection =
      e.inv ≫ (GroupScheme.baseChange resExt).map Q.projection := by
  simp only [baseChangeSpecialFibreIso, transportSpecialFibreIso_projection,
    baseChange_projection, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- The full reductive-quotient predicate is preserved by separable algebraic
residue extension and the supplied actual special-fibre isomorphism. -/
theorem isReductiveQuotient_baseChangeSpecialFibreIso
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)]
    (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre)
    (hQ : Q.IsReductiveQuotient) :
    (Q.baseChangeSpecialFibreIso A L e).IsReductiveQuotient :=
  (Q.baseChange A L).isReductiveQuotient_transportSpecialFibreIso _
    (Q.isReductiveQuotient_baseChange A L hQ)

/-- The recovered projection forms the exact residue coefficient square. -/
@[simp, reassoc]
theorem baseChangeSpecialFibreIso_hom_projection (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre) :
    e.hom ≫ (Q.baseChangeSpecialFibreIso A L e).projection =
      (GroupScheme.baseChange resExt).map Q.projection := by
  rw [baseChangeSpecialFibreIso_projection, Iso.hom_inv_id_assoc]

/-- A supplied torus square gives the literal base change of the original
torus-to-quotient map. -/
theorem baseChangeSpecialFibreIso_torus_projection (Q : SpecialFibreQuotientData D)
    (e : (GroupScheme.baseChange resExt).obj D.neutral.specialFibre ≅
      E.neutral.specialFibre)
    {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    {T' : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField A)))}
    (t : T.toGrp ⟶ D.neutral.specialFibre)
    (t' : T'.toGrp ⟶ E.neutral.specialFibre)
    (s : (GroupScheme.baseChange resExt).obj T.toGrp ⟶ T'.toGrp)
    (ht : s ≫ t' = (GroupScheme.baseChange resExt).map t ≫ e.hom) :
    s ≫ t' ≫ (Q.baseChangeSpecialFibreIso A L e).projection =
      (GroupScheme.baseChange resExt).map (t ≫ Q.projection) := by
  rw [← Category.assoc, ht, Category.assoc,
    baseChangeSpecialFibreIso_hom_projection, Functor.map_comp]

end SpecialFibreQuotientData
end Langlands.BruhatTits.IntegralModels
