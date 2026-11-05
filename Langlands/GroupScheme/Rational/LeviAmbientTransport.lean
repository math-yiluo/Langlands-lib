import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport

/-! # Transport of actual rational Levi subgroups through ambient isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {L U P P' : GroupScheme S}

/-- The actual multiplication morphism commutes with postcomposition by an
ambient group homomorphism. -/
theorem subgroupMultiplication_postcomp (l : L ⟶ P) (r : U ⟶ P) (f : P ⟶ P') :
    subgroupMultiplication (l ≫ f) (r ≫ f) =
      subgroupMultiplication l r ≫ f.hom.hom := by
  simp only [subgroupMultiplication, Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc]

end Scheme

variable {k : Type u} [Field k]
  {L U P P' : GroupScheme (Spec (CommRingCat.of k))}

/-- The specified geometric unipotent radical transports through an ambient
group-scheme isomorphism. -/
theorem LeviSubgroup.IsGeometricUnipotentRadical.comp_iso {r : U ⟶ P}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (e : P ≅ P') :
    LeviSubgroup.IsGeometricUnipotentRadical (r ≫ e.hom) := by
  refine ⟨hr.1.comp_iso e, ?_⟩
  simpa only [Functor.map_comp, Functor.mapIso_hom] using
    hr.2.comp_iso ((GroupScheme.baseChange (toAlgebraicClosure k)).mapIso e)

/-- An ambient group-scheme isomorphism transports a rational Levi while
retaining its actual Levi-first multiplication isomorphism. -/
theorem IsRationalLeviSubgroup.comp_iso {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) (e : P ≅ P') :
    IsRationalLeviSubgroup (l ≫ e.hom) := by
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  have hPa : IsAffineHom P'.X.hom := by
    rw [← Over.w e.inv.hom.hom]
    let : IsAffineHom P.X.hom := hl.isAffineHom
    infer_instance
  refine ⟨hPa, hl.isClosedSubgroup.comp_iso e, hl.isConnectedReductive, ?_⟩
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  refine ⟨U, r ≫ e.hom, hr.comp_iso e, ?_⟩
  rw [subgroupMultiplication_postcomp]
  let : IsIso (subgroupMultiplication l r) := hmul
  infer_instance

end Langlands.GroupScheme
