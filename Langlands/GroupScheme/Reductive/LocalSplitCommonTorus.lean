import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Moving a fibrewise root datum to a common coordinate torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable (S : Scheme.{u}) {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I]
  [DecidableEq I']

/-- The isomorphism of coordinate split tori `T_I ≅ T_{I'}` attached to a lattice
isomorphism `e : (I → ℤ) ≃ (I' → ℤ)`; it pulls the character with exponent `e m` back to the
character with exponent `m`. -/
def exponentEquivIso (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) :
    commGroupScheme S I ≅ commGroupScheme S I' where
  hom := exponentHom S I I' e.symm.toLinearMap
  inv := exponentHom S I' I e.toLinearMap
  hom_inv_id := by
    rw [exponentHom_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext m
      simp
    rw [he, exponentHom_id]
  inv_hom_id := by
    rw [exponentHom_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext m
      simp
    rw [he, exponentHom_id]

theorem congr_exponentEquivIso (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) (m : I → ℤ) :
    characterLattice.congr (exponentEquivIso S e) (exponentCharacter S I m) =
      exponentCharacter S I' (e m) := by
  rw [characterLattice.congr_apply]
  exact exponentHom_comp_exponentCharacter S I' I e.toLinearMap m

theorem baseChange_groupHom_exponentEquivIso {S' : Scheme.{u}} (b : S' ⟶ S)
    (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) :
    (GroupScheme.baseChange b).map (CommGroupScheme.groupHom (exponentEquivIso S e).hom) =
      (baseChangeIso b I).hom ≫ CommGroupScheme.groupHom (exponentEquivIso S' e).hom ≫
        (baseChangeIso b I').inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact (congrArg CommGroupScheme.groupHom
    (exponentHom_baseChange S I I' b e.symm.toLinearMap)).symm

end splitTorus

namespace LocalSplitCell

open CoordinateRootDatum

variable {R : Type u} [CommRing R] {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I]
  [DecidableEq I'] {H : GroupScheme (Spec (CommRingCat.of R))}

/-- The torus map `T_I ≅ T_{I'} ⟶ H` obtained from `i'` and a lattice isomorphism `e`. -/
abbrev precompTorus (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) :
    splitTorus (Spec (CommRingCat.of R)) I ⟶ H :=
  CommGroupScheme.groupHom (splitTorus.exponentEquivIso _ e).hom ≫ i'

theorem baseChangeHom_precompTorus (K : Type u) [CommRing K] [Algebra R K]
    [IsAffineHom H.X.hom] (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H) :
    splitTorus.baseChangeHom (K := K) H I (precompTorus e i') =
      CommGroupScheme.groupHom (splitTorus.exponentEquivIso _ e).hom ≫
        splitTorus.baseChangeHom (K := K) H I' i' := by
  rw [splitTorus.baseChangeHom, splitTorus.baseChangeHom, precompTorus, Functor.map_comp,
    splitTorus.baseChange_groupHom_exponentEquivIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The underlying isomorphism of group schemes of the torus isomorphism. -/
def exponentEquivGroupIso (S : Scheme.{u}) (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ)) :
    splitTorus S I ≅ splitTorus S I' where
  hom := CommGroupScheme.groupHom (splitTorus.exponentEquivIso S e).hom
  inv := CommGroupScheme.groupHom (splitTorus.exponentEquivIso S e).inv
  hom_inv_id := congrArg CommGroupScheme.groupHom (splitTorus.exponentEquivIso S e).hom_inv_id
  inv_hom_id := congrArg CommGroupScheme.groupHom (splitTorus.exponentEquivIso S e).inv_hom_id

theorem isClosedSubgroup_precompTorus (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H} (hi' : IsClosedSubgroup i') :
    IsClosedSubgroup (precompTorus e i') :=
  (IsClosedSubgroup.of_iso (exponentEquivGroupIso _ e)).comp hi'

theorem isFibrewiseMaximalTorus_precompTorus (e : (I → ℤ) ≃ₗ[ℤ] (I' → ℤ))
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    (h : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i') :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) (precompTorus e i') := by
  intro s
  have h' := IsMaximalTorus.precomp_torusIso
    ((CommGroupScheme.baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).mapIso
      (splitTorus.exponentEquivIso _ e)) (h s)
  rw [precompTorus, Functor.map_comp]
  exact h'

/-- Precomposing with the torus isomorphism of a root-datum equivalence `e : P ≃ Q` turns a
fibrewise root datum `Q` of `i'` into the fibrewise root datum `P` of the new torus map,
provided `P` is a fibrewise root datum of some group (which fixes its pairing). -/
theorem isFibrewiseRootDatumOf_precompTorus [IsAffineHom H.X.hom]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H} {J J' : Type u}
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    (e : RootPairing.Equiv P Q) :
    IsFibrewiseRootDatumOf I H (precompTorus e.weightEquiv i') P := by
  refine ⟨hP.finite, hP.isReduced, fun K _ _ => ?_⟩
  rw [baseChangeHom_precompTorus]
  let eK : RootPairing.Equiv (fieldRealization K P) (fieldRealization K Q) :=
    (fieldRealizationEquiv K Q).comp (e.comp (fieldRealizationEquiv K P).symm)
  refine IsRootDatumOf.precomp_torusIso _ (hQ.field K) (hP.field K).1 eK ?_
  intro χ
  obtain ⟨m, rfl⟩ : ∃ m, splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m = χ :=
    ⟨splitTorus.characterLatticeEquiv K I χ, by
      rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
        AddEquiv.symm_apply_apply]⟩
  rw [splitTorus.congr_exponentEquivIso]
  have h1 : (fieldRealizationEquiv K P).weightEquiv.symm
      (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m) = m := by
    rw [← fieldRealizationEquiv_weightMap K P m]
    exact (fieldRealizationEquiv K P).weightEquiv_symm_weightMap m
  change (fieldRealizationEquiv K Q).toHom.weightMap
    (e.toHom.weightMap ((fieldRealizationEquiv K P).weightEquiv.symm
      (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m))) = _
  rw [h1, fieldRealizationEquiv_weightMap]
  rfl

end LocalSplitCell

end Langlands.GroupScheme
