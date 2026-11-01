import Langlands.AlgebraicGeometry.FieldPointTangentLocalRegularityStatement
import Langlands.AlgebraicGeometry.SectionTangentDerivations
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Proof: tangent and local cotangent dimensions at a rational point over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

open Langlands.CommutativeAlgebra.PointDerivation SectionPoint

/-- The published statement `FieldPointTangentLocalRegularityStatement` holds. -/
theorem fieldPointTangentLocalRegularity : FieldPointTangentLocalRegularityStatement.{u} := by
  intro k _ X e hX x R T
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  let τ : (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.presheaf.stalk pt ≃+* k :=
    (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hbij : Function.Bijective
      (((τ : _ →+* k).comp (e.left.stalkMap pt).hom).comp (baseMap X.hom e.left pt)) := by
    have h : ⇑(((τ : _ →+* k).comp (e.left.stalkMap pt).hom).comp (baseMap X.hom e.left pt)) =
        ⇑(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom := by
      funext c
      rw [RingHom.coe_comp, Function.comp_apply, RingHom.coe_comp, Function.comp_apply]
      change τ (e.left.stalkMap pt (baseMap X.hom e.left pt c)) = _
      rw [stalkMap_baseMap]
      exact ConcreteCategory.congr_hom (germ_stalkClosedPointIso_hom (CommRingCat.of k)) c
    rw [h]
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.bijective
  have hi : Function.Bijective (fun c : k =>
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.presheaf.germ ⊤ pt trivial
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) :=
    (germ_bijective pt (V := ⊤) trivial).comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.bijective
  have r1 : Module.rank k T =
      Module.rank _ (derivations (baseMap X.hom e.left pt) (e.left.stalkMap pt).hom) :=
    rank_eq_of_equiv_equiv _
      { tangentDerivationEquiv X e pt with map_add' := tangentDerivationEquiv_add X e pt } hi
      (fun c t => tangentDerivationEquiv_smul X e pt _ t)
  have r2 := rank_eq_of_equiv_equiv τ
    (derivationsCongr (ι := baseMap X.hom e.left pt) (π := (e.left.stalkMap pt).hom) τ)
    τ.bijective (derivationsCongr_smul τ)
  have r3 := rank_derivations hbij
  have r4 : Module.rank (IsLocalRing.ResidueField R)
      (Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) =
        Module.rank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
    rw [Module.dual_rank_eq, Cardinal.lift_id]
  have hrank : Module.rank k T =
      Module.rank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    r1.trans (r2.trans (r3.trans r4))
  have hfin : FiniteDimensional k T :=
    Module.rank_lt_aleph0_iff.mp (hrank ▸ Module.rank_lt_aleph0 _ _)
  have hfinrank : Module.finrank k T =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
    unfold Module.finrank
    rw [hrank]
  refine ⟨hfin, hfinrank, fun g hg hgdim => ?_⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hfinrank]
  exact le_trans (by exact_mod_cast hg) hgdim

end Langlands.Scheme
