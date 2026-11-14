import Langlands.GroupScheme.Rational.VectorLineCoordinates
import Langlands.GroupScheme.Reductive.IsogenyRootPolynomial

/-! # Characteristic powers of actual equivariant vector-line maps -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.RelativeRoot.VectorLine

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (d : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ W.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (f : V ⟶ W)

/-- Single-character coordinates give the actual scalar action on every algebra. -/
theorem affineCoordinates_act {a : AutomorphicAction T.toGrp V}
    {α : characterLattice T} (he : IsWeightVectorCoordinates a α e)
    {B : Type u} [CommRing B] [Algebra k B]
    (t : Lie.AffinePoints T.toGrp B) (x : Lie.AffinePoints V B) :
    (vectorAffineCoordinates e B (a.act t x)).toAdd 0 =
      (Lie.characterValue α t : B) * (vectorAffineCoordinates e B x).toAdd 0 := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((e _ (a.act t x)).toAdd 0) = _
  rw [he.2]
  exact (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.map_mul _ _

variable {a : AutomorphicAction T.toGrp V} {b : AutomorphicAction T.toGrp W}
    {α β : characterLattice T}
    (he : IsWeightVectorCoordinates a α e) (hd : IsWeightVectorCoordinates b β d)
    (hf : ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X) (x : U ⟶ V.X),
      a.act t x ≫ f.hom.hom = b.act t (x ≫ f.hom.hom))

include he hd hf

/-- Actual equivariance yields polynomial equivariance over every coefficient algebra. -/
theorem polynomial_equivariance_eval {B : Type u} [CommRing B] [Algebra k B]
    (t : Lie.AffinePoints T.toGrp B) (x : Lie.AffinePoints V B) :
    aeval ((Lie.characterValue α t : B) * (vectorAffineCoordinates e B x).toAdd 0)
        (polynomial e d f) =
      (Lie.characterValue β t : B) *
        aeval ((vectorAffineCoordinates e B x).toAdd 0) (polynomial e d f) := by
  calc
    _ = aeval ((vectorAffineCoordinates e B (a.act t x)).toAdd 0)
        (polynomial e d f) := by rw [affineCoordinates_act e he]
    _ = (vectorAffineCoordinates d B (a.act t x ≫ f.hom.hom)).toAdd 0 :=
      polynomial_aeval e d f he.1 hd.1 _
    _ = (vectorAffineCoordinates d B (b.act t (x ≫ f.hom.hom))).toAdd 0 :=
      congrArg (fun y => (vectorAffineCoordinates d B y).toAdd 0) (hf _ t x)
    _ = (Lie.characterValue β t : B) *
        (vectorAffineCoordinates d B (x ≫ f.hom.hom)).toAdd 0 :=
      affineCoordinates_act d hd _ _
    _ = _ := by rw [polynomial_aeval e d f he.1 hd.1]

/-- The universal equation uses the actual characters in the torus coordinate algebra. -/
theorem polynomial_isEquivariant [IsAffineHom T.toGrp.X.hom] :
    IsogenyRootPolynomial.IsEquivariant α β (polynomial e d f) := by
  let A := CharacterUnits.Coord T.toGrp
  let φ : A →ₐ[k] A[X] := Polynomial.CAlgHom
  let t : Lie.AffinePoints T.toGrp A[X] :=
    Lie.affineMap T.toGrp φ (CharacterUnits.universalPoint T.toGrp)
  have hchar (χ : characterLattice T) :
      (Lie.characterValue χ t : A[X]) =
        C ((IsogenyRootPolynomial.characterUnit χ).toMul : A) := by
    exact congrArg Units.val (Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
      (CommAlgCat.ofHom φ)
      (CharacterUnits.universalPoint T.toGrp ≫ (CommGroupScheme.groupHom χ).hom.hom))
  let x : Lie.AffinePoints V A[X] :=
    (vectorAffineCoordinates e A[X]).symm (Multiplicative.ofAdd fun _ => X)
  have h := polynomial_equivariance_eval e d f he hd hf t x
  simpa only [IsogenyRootPolynomial.IsEquivariant, x,
    MulEquiv.apply_symm_apply, toAdd_ofAdd, hchar,
    Polynomial.aeval_X_left_eq_map] using h

omit he hd hf

/-- A scheme-epimorphic actual map between naturally coordinated lines has
nonzero polynomial. -/
theorem polynomial_ne_zero [IsAffineHom V.X.hom] [Epi f.hom.hom]
    (he : IsNaturalVectorCoordinates e) (hd : IsNaturalVectorCoordinates d) :
    polynomial e d f ≠ 0 := by
  intro hz
  have hpoint {B : Type u} [CommRing B] [Algebra k B] (x : Lie.AffinePoints V B) :
      x ≫ f.hom.hom = 1 := by
    apply (vectorAffineCoordinates d B).injective
    apply Multiplicative.toAdd.injective
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have h := polynomial_aeval e d f he hd x
    simpa only [hz, map_zero, map_one, toAdd_one, Pi.zero_apply] using h.symm
  have hzero : f.hom.hom = 1 := by
    apply (cancel_epi (Lie.coordinateIso V).hom).mp
    simpa only [CharacterUnits.universalPoint_eq, MonObj.comp_one] using
      hpoint (CharacterUnits.universalPoint V)
  have hid : 𝟙 W.X = (1 : W.X ⟶ W.X) := by
    apply (cancel_epi f.hom.hom).mp
    simp only [Category.comp_id, MonObj.comp_one, hzero]
  let x : Lie.AffinePoints W k :=
    (vectorAffineCoordinates d k).symm (Multiplicative.ofAdd fun _ => 1)
  have hx : x = 1 := by
    calc
      x = x ≫ 𝟙 W.X := (Category.comp_id _).symm
      _ = x ≫ 1 := congrArg (x ≫ ·) hid
      _ = 1 := MonObj.comp_one _
  have h := congrArg (fun y => (vectorAffineCoordinates d k y).toAdd 0) hx
  exact one_ne_zero (by simpa only [x, MulEquiv.apply_symm_apply,
    toAdd_ofAdd, map_one, toAdd_one, Pi.zero_apply] using h)

/-- Extract the scalar, characteristic-power degree and actual character equation
directly from an epimorphic equivariant map of naturally coordinated lines. -/
def powerMonomial [IsAffineHom T.toGrp.X.hom] [IsAffineHom V.X.hom]
    [Epi f.hom.hom] (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0) :
    IsogenyRootPolynomial.PowerMonomial α β (polynomial e d f) :=
  IsogenyRootPolynomial.powerMonomial hT hα
    (polynomial_ne_zero e d f he.1 hd.1)
    (polynomial_isAddPoly e d f he.1 hd.1)
    (polynomial_isEquivariant e d f he hd hf)

end Langlands.GroupScheme.RelativeRoot.VectorLine
