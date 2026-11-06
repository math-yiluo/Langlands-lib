import Langlands.GroupScheme.Reductive.IntegralWeylOpposition
import Langlands.GroupScheme.Reductive.RootDatumWeylComparison
import Langlands.GroupScheme.Reductive.RegularWeightCentralizer
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy

/-! # Rational normalizer representatives of integral rho opposition -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ G} [Mono j.hom.hom.left]
    {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))

namespace IsRootDatumOf

variable {P} (hP : IsRootDatumOf j P)

include hP

/-- Every abstract Weyl element of a supplied root datum has a rational
normalizer representative with its exact action on the entire character lattice. -/
theorem exists_weylRepresentative (w : P.weylGroup) :
    ∃ n : normalizerPoints j,
      weylAction j n = RootPairing.Equiv.weightHom P w.val := by
  apply hP.abstractWeylImage_le
  exact ⟨w.val, w.property, rfl⟩

/-- A rational normalizer representative of an abstract Weyl element. -/
def weylRepresentative (w : P.weylGroup) : normalizerPoints j :=
  (hP.exists_weylRepresentative w).choose

/-- The chosen rational representative has the prescribed full character action. -/
theorem weylAction_weylRepresentative (w : P.weylGroup) :
    weylAction j (hP.weylRepresentative w) = RootPairing.Equiv.weightHom P w.val :=
  (hP.exists_weylRepresentative w).choose_spec

end IsRootDatumOf

variable [Fintype J]

/-- A rational Weyl representative reversing a weight also reverses its
integral polarization under the inverse normalizing automorphism. -/
theorem polarization_comp_normalizingAut_inv_eq_neg
    (hP : IsRootDatumOf j P) (x : characterLattice T)
    (n : normalizerPoints j) (w : P.weylGroup)
    (hw : weylAction j n = RootPairing.Equiv.weightHom P w.val)
    (hanti : weylAction j n x = -x) :
    P.Polarization x ≫ (normalizingAut j n).inv = -P.Polarization x := by
  have hanti' : w • x = -x := by
    change RootPairing.Equiv.weightHom P w.val x = -x
    rw [← hw]
    exact hanti
  apply P.flip.toPerfPair.injective
  apply LinearMap.ext
  intro y
  change P.toLinearMap y (P.Polarization x ≫ (normalizingAut j n).inv) =
    P.toLinearMap y (-P.Polarization x)
  have he := RootPairing.InvariantForm.apply_weylGroup_smul P
    (B := P.toInvariantForm) w x y
  change P.RootForm (w • x) (w • y) = P.RootForm x y at he
  rw [hanti', map_neg, LinearMap.neg_apply] at he
  calc
    P.toLinearMap y (P.Polarization x ≫ (normalizingAut j n).inv) =
        latticePairing T y (P.Polarization x ≫ (normalizingAut j n).inv) := by
      rw [hP.1]
    _ = latticePairing T (weylAction j n y) (P.Polarization x) :=
      (latticePairing_weylAction j n y (P.Polarization x)).symm
    _ = P.toLinearMap (w • y) (P.Polarization x) := by
      rw [← hP.1, hw]
      rfl
    _ = P.RootForm x (w • y) := P.toLinearMap_apply_apply_Polarization x (w • y)
    _ = -P.RootForm x y := by omega
    _ = P.toLinearMap y (-P.Polarization x) := by
      rw [map_neg, P.toLinearMap_apply_apply_Polarization]

/-- The forward normalizing action reverses the same polarized cocharacter. -/
theorem cocharacterAut_polarization_eq_neg
    (hP : IsRootDatumOf j P) (x : characterLattice T)
    (n : normalizerPoints j) (w : P.weylGroup)
    (hw : weylAction j n = RootPairing.Equiv.weightHom P w.val)
    (hanti : weylAction j n x = -x) :
    cocharacterAut (normalizingAut j n) (P.Polarization x) = -P.Polarization x := by
  have hi := polarization_comp_normalizingAut_inv_eq_neg P hP x n w hw hanti
  have he := congrArg (fun zeta : cocharacterLattice T =>
    zeta ≫ (normalizingAut j n).hom) hi
  have he' : P.Polarization x =
      -(cocharacterAut (normalizingAut j n) (P.Polarization x)) := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Preadditive.neg_comp, cocharacterAut_apply] using he
  exact (neg_eq_iff_eq_neg.mpr he').symm

namespace IsRootDatumOf

variable {P} (hP : IsRootDatumOf j P) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    [P.IsReduced]

include hP

/-- An actual rational normalizer point reversing integral rho. -/
def oppositionRepresentative : normalizerPoints j :=
  hP.weylRepresentative (IntegralWeylVector.opposition P b hspan).val

/-- The representative acts on rho by its additive negative. -/
theorem oppositionRepresentative_rho :
    weylAction j (hP.oppositionRepresentative b hspan) (IntegralWeylVector.rho P b hspan) =
      -IntegralWeylVector.rho P b hspan := by
  rw [oppositionRepresentative, hP.weylAction_weylRepresentative]
  exact (IntegralWeylVector.opposition P b hspan).property

/-- The identical normalizing automorphism sends negative rho to rho. -/
theorem oppositionRepresentative_neg_rho :
    characterAut (normalizingAut j (hP.oppositionRepresentative b hspan))
        (-IntegralWeylVector.rho P b hspan) = IntegralWeylVector.rho P b hspan := by
  change weylAction j (hP.oppositionRepresentative b hspan)
    (-IntegralWeylVector.rho P b hspan) = _
  rw [map_neg, hP.oppositionRepresentative_rho b hspan, neg_neg]

omit [Mono j.hom.hom.left] [P.IsReduced] in
/-- The polarized rho is generic for the original torus embedding. -/
theorem polarization_rho_isGeneric :
    IsGenericCocharacter j (P.Polarization (IntegralWeylVector.rho P b hspan)) := by
  apply polarization_isGenericCocharacter P hP
  exact IntegralWeylVector.pairing_rho_coroot_ne_zero P b hspan

/-- The rational normalizer point reverses this actual generic cocharacter. -/
theorem oppositionRepresentative_cocharacter :
    cocharacterAut (normalizingAut j (hP.oppositionRepresentative b hspan))
        (P.Polarization (IntegralWeylVector.rho P b hspan)) =
      -P.Polarization (IntegralWeylVector.rho P b hspan) := by
  apply cocharacterAut_polarization_eq_neg P hP _ _
    (IntegralWeylVector.opposition P b hspan).val
  · exact hP.weylAction_weylRepresentative _
  · exact hP.oppositionRepresentative_rho b hspan

/-- Inner conjugation by the chosen point carries the ambient cocharacter
into its exact opposite, with the original torus embedding retained. -/
theorem oppositionRepresentative_conjugate_cocharacter :
    (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j) ≫
        (G.innerIso (hP.oppositionRepresentative b hspan).val).hom =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom
        (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j) := by
  rw [← groupHom_cocharacterAut_comp, hP.oppositionRepresentative_cocharacter,
    groupHom_neg_comp_eq_oppositeCocharacter]

/-- Every supplied representative of this dynamic parabolic yields the
opposite representative by conjugating with the constructed rational point. -/
theorem oppositionRepresentative_parabolic {H : GroupScheme (Spec (CommRingCat.of k))}
    {i : H ⟶ G}
    (hi : (Dynamic.parabolic (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j)).IsRepresentedBy i) :
    (Dynamic.parabolic (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom
      (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j))).IsRepresentedBy
        (i ≫ (G.innerIso (hP.oppositionRepresentative b hspan).val).hom) := by
  let chi := CommGroupScheme.groupHom
    (P.Polarization (IntegralWeylVector.rho P b hspan)) ≫ j
  let e := G.innerIso (hP.oppositionRepresentative b hspan).val
  have he := Dynamic.parabolic_eq_comap_of_iso (chi ≫ e.hom) e.symm
  change Dynamic.parabolic (chi ≫ e.hom) =
    (Dynamic.parabolic ((chi ≫ e.hom) ≫ e.inv)).comap e.inv at he
  rw [Dynamic.comp_hom_comp_inv] at he
  have hc : chi ≫ e.hom = Dynamic.oppositeCocharacter chi :=
    hP.oppositionRepresentative_conjugate_cocharacter b hspan
  rw [hc] at he
  rw [he]
  exact hi.comp_iso e

end IsRootDatumOf

end Langlands.GroupScheme
