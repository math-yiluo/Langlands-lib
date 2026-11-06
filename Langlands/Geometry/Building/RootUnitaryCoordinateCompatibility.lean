import Langlands.Geometry.Building.CentralizerCoordinateCompatibility
import Langlands.GroupScheme.Examples.SU3RootScaling
import Langlands.GroupScheme.Examples.SU3RootParametersTowerValuation

/-! # Full V6 on multipliable roots from quadratic unitary coordinates

For a multipliable relative root `a`, Kaletha–Prasad identify the actual root group `U_a(k)`
with the quadratic unitary group `U_{L/E}(E) = {(u, v) ∈ L × L | v + v̄ = u ū}` of a separable
quadratic extension `L / E` of finite separable extensions of `k`, the subgroup `U_{2a}(k)` with
its zero-first-coordinate subgroup, and the action of the centralizer with scaling
`(u, v) ↦ (λ u, λ λ̄ v)` by the value `λ` of a character of `Z_L` restricting to `a`
(`RootUnitaryCoordinates`). For a norm-calibrated conjugation-invariant valuation `w` of `L`,
the root functions `φ_a(u, v) = w(v) / 2` and `φ_{2a}(0, v) = w(v)` then satisfy V 6 at `a` and at
`2a`. Over a henselian base, these are the Library's tower depths. Combined with equivariant
coordinate families on the remaining roots this gives the integer centralizer compatibility and
the Omega compatibility of an apartment class.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}

/-- Quadratic unitary coordinates on the actual rational root group of a multipliable root `a`:
a separable quadratic extension `extension / base` of fields, with `extension` finite separable
over `k`; an isomorphism from the actual quadratic unitary parameter group of `extension / base`
onto `U_a(k)`, sending the zero-first-coordinate subgroup onto `U_{2a}(k)`; and an actual
character of `Z_extension` restricting to `a`, whose values scale the parameters under the action
of the whole centralizer: `j(z) e(p) j(z)⁻¹ = e(scale (β(z_extension)) p)`. -/
structure RootUnitaryCoordinates (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (s : S.toGrp ⟶ Z) (a : characterLattice S) where
  /-- The field over which the quadratic unitary group is defined. -/
  base : Type u
  /-- The separable quadratic extension of `base` carrying the coordinates. -/
  extension : Type u
  [baseField : Field base]
  [field : Field extension]
  [baseAlgebra : Algebra k base]
  [quadraticAlgebra : Algebra base extension]
  [algebra : Algebra k extension]
  [scalarTower : IsScalarTower k base extension]
  [quadratic : Algebra.IsQuadraticExtension base extension]
  [quadraticSeparable : Algebra.IsSeparable base extension]
  [finite : FiniteDimensional k extension]
  [separable : Algebra.IsSeparable k extension]
  /-- The parametrization of `U_a(k)` by the quadratic unitary group. -/
  equiv : SU3Root.rationalParameters base extension ≃* rootGroupPoints i a
  /-- The zero-first-coordinate parameters are exactly the points of `U_{2a}(k)`. -/
  double : ∀ g : rationalPoints G, g ∈ rootGroupPoints i (2 • a) ↔
    ∃ p ∈ SU3Root.Parameters.central (SU3Root.fieldInvolution base extension),
      (equiv p : rationalPoints G) = g
  /-- The character of `Z_extension` through which the centralizer scales the parameters. -/
  character : rationalCharacters (GaloisPointComparison.baseChanged k extension Z)
  restriction :
    characterRestrict ((GroupScheme.baseChange (GaloisPointComparison.baseMap k extension)).map s)
        character =
      rationalCharacters.baseChange (GaloisPointComparison.baseMap k extension)
        ((rationalCharacters.equivCharacterLattice S).symm a)
  conjugation : ∀ (z : rationalPoints Z) (p : SU3Root.rationalParameters base extension),
    rationalPoints.map j z * (equiv p : rationalPoints G) * (rationalPoints.map j z)⁻¹ =
      (equiv (SU3Root.Parameters.scale
        (rationalCharacterEval character
          (GaloisPointComparison.rationalExtend k extension Z z) : extension) p) :
            rationalPoints G)

attribute [instance] RootUnitaryCoordinates.baseField RootUnitaryCoordinates.field
  RootUnitaryCoordinates.baseAlgebra RootUnitaryCoordinates.quadraticAlgebra
  RootUnitaryCoordinates.algebra RootUnitaryCoordinates.scalarTower
  RootUnitaryCoordinates.quadratic RootUnitaryCoordinates.quadraticSeparable
  RootUnitaryCoordinates.finite RootUnitaryCoordinates.separable

variable {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {a : characterLattice S}

/-- Conjugation by the inverse of a centralizer point scales the parameters by the inverse
character value. -/
theorem RootUnitaryCoordinates.conj_inv (R : RootUnitaryCoordinates i j s a)
    (z : rationalPoints Z) (p : SU3Root.rationalParameters R.base R.extension) :
    (rationalPoints.map j z)⁻¹ * (R.equiv p : rationalPoints G) * rationalPoints.map j z =
      (R.equiv (SU3Root.Parameters.scale
        (((rationalCharacterEval R.character
          (GaloisPointComparison.rationalExtend k R.extension Z z))⁻¹ : R.extensionˣ) :
            R.extension) p) : rationalPoints G) := by
  have h := R.conjugation z⁻¹ p
  rwa [map_inv, inv_inv, map_inv, map_inv] at h

section Compatibility

open IntegerValuation

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  [IsAffine S.toGrp.X.left] [IsAffine Z.X.left]

/-- **V 6 at a multipliable root.** If `φ_a(e(u, v)) = w(v) / 2` for a norm-calibrated valuation
`w` of the coordinate field invariant under the quadratic conjugation, then `φ_a` satisfies V 6
on the whole centralizer. -/
theorem RootUnitaryCoordinates.conj_eq_multipliable (R : RootUnitaryCoordinates i j s a)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {w : AddValuation R.extension (WithTop ℝ)} (hw : IsNormCalibrated v w)
    (hbar : ∀ x, w ((SU3Root.fieldInvolution R.base R.extension).bar x) = w x)
    {φ : RootFunctionFamily S G}
    (hφ : ∀ p, φ a (R.equiv p) = SU3Root.Parameters.depthA w p)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u +
        ((eval S a (IntegerValuation.centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) := by
  obtain ⟨p, rfl⟩ : ∃ p, (R.equiv p : rationalPoints G) = u :=
    ⟨R.equiv.symm ⟨u, hu⟩, by simp⟩
  have hβz := characterNormOrder_eq_eval v s h R.restriction z
  rw [R.conj_inv, hφ, hφ, SU3Root.Parameters.depthA_scale w hbar, hw.apply_inv, add_comm,
    IntegerValuation.centralizerTranslation_toAdd, map_neg]
  congr 2
  change -(characterNormOrder v R.character z) = _
  rw [hβz]

/-- **V 6 at the double of a multipliable root.** If `φ_{2a}(e(0, v)) = w(v)` for a
norm-calibrated valuation `w` of the coordinate field invariant under the quadratic conjugation,
then `φ_{2a}` satisfies V 6 on the whole centralizer. -/
theorem RootUnitaryCoordinates.conj_eq_double (R : RootUnitaryCoordinates i j s a)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    {w : AddValuation R.extension (WithTop ℝ)} (hw : IsNormCalibrated v w)
    (hbar : ∀ x, w ((SU3Root.fieldInvolution R.base R.extension).bar x) = w x)
    {φ : RootFunctionFamily S G}
    (hφ : ∀ p ∈ SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension),
      φ (2 • a) (R.equiv p) = w p.second)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i (2 • a)) :
    φ (2 • a) ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ (2 • a) u + ((eval S (2 • a) (IntegerValuation.centralizerTranslation v s h z).toAdd : ℝ) :
        WithTop ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (R.double u).mp hu
  have hβz := characterNormOrder_eq_eval v s h R.restriction z
  have hp' : SU3Root.Parameters.scale (((rationalCharacterEval R.character
      (GaloisPointComparison.rationalExtend k R.extension Z z))⁻¹ : R.extensionˣ) :
        R.extension) p ∈
          SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension) := by
    rw [SU3Root.Parameters.mem_central] at hp ⊢
    rw [SU3Root.Parameters.first_scale, hp, mul_zero]
  rw [R.conj_inv, hφ _ hp', hφ p hp, SU3Root.Parameters.second_scale, w.map_mul, w.map_mul, hbar,
    hw.apply_inv, add_comm, IntegerValuation.centralizerTranslation_toAdd, map_neg, eval_nsmul_char,
    ← WithTop.coe_add]
  congr 2
  change -(characterNormOrder v R.character z) + -(characterNormOrder v R.character z) = _
  rw [hβz]
  push_cast
  ring

variable (hH : HenselianLocalRing v.valuationSubring)

/-- **V 6 at a multipliable root, henselian case.** The tower depth of the induced valuation of
the coordinate field satisfies V 6 on the whole centralizer. -/
theorem RootUnitaryCoordinates.conj_eq_multipliable_henselian (R : RootUnitaryCoordinates i j s a)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hφ : ∀ p, φ a (R.equiv p) = SU3Root.towerDepth k R.base R.extension v hH p)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) :
    φ a ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ a u +
        ((eval S a (IntegerValuation.centralizerTranslation v s h z).toAdd : ℝ) : WithTop ℝ) :=
  R.conj_eq_multipliable h (isNormCalibrated_henselianSeparableAddValuation hH R.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar k R.base R.extension v hH) hφ z hu

/-- **V 6 at the double of a multipliable root, henselian case.** The central tower depth of the
induced valuation of the coordinate field satisfies V 6 on the whole centralizer. -/
theorem RootUnitaryCoordinates.conj_eq_double_henselian (R : RootUnitaryCoordinates i j s a)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hφ : ∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension),
      φ (2 • a) (R.equiv q.val) = SU3Root.towerCentralDepth k R.base R.extension v hH q)
    (z : rationalPoints Z) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i (2 • a)) :
    φ (2 • a) ((rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z) =
      φ (2 • a) u + ((eval S (2 • a) (IntegerValuation.centralizerTranslation v s h z).toAdd : ℝ) :
        WithTop ℝ) :=
  R.conj_eq_double h (isNormCalibrated_henselianSeparableAddValuation hH R.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar k R.base R.extension v hH)
    (fun p hp => hφ ⟨p, hp⟩) z hu

end Compatibility

namespace IntegerValuation

section Compatibility

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  [IsAffine S.toGrp.X.left] [IsAffine Z.X.left] (hH : HenselianLocalRing v.valuationSubring)

/-- **Full V 6 from coordinates of the three root types.** Over a henselian base, suppose every
relative root `a` has an equivariant coordinate family, or quadratic unitary coordinates on which
`φ_a` is the tower depth, or is `2b` for a root `b` with quadratic unitary coordinates on whose
zero-first-coordinate parameters `φ_a` is the central tower depth. Then `φ` satisfies the
integer centralizer compatibility. -/
theorem isCentralizerCompatible_of_rootCoordinateTypes [IsAffineHom G.X.hom]
    [Mono i.hom.hom.left] (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hc : ∀ a ∈ relativeRoots i,
      Nonempty (RootCoordinateFamilyEquivariance v i j s φ a) ∨
      (∃ R : RootUnitaryCoordinates i j s a,
        ∀ p, φ a (R.equiv p) = SU3Root.towerDepth k R.base R.extension v hH p) ∨
      ∃ b, 2 • b = a ∧ ∃ R : RootUnitaryCoordinates i j s b,
        ∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension),
          φ a (R.equiv q.val) = SU3Root.towerCentralDepth k R.base R.extension v hH q) :
    IsCentralizerCompatible v i j s h φ := by
  intro a ha z _ hu
  rcases hc a ha with hR | ⟨R, hR⟩ | ⟨b, rfl, R, hR⟩
  · exact hR.some.conj_eq hj h z hu
  · exact R.conj_eq_multipliable_henselian hH h hR z hu
  · exact R.conj_eq_double_henselian hH h hR z hu

end Compatibility

section Apartment

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [IsAffine S.toGrp.X.left]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {v : Valuation k (WithZero (Multiplicative ℤ))} (hH : HenselianLocalRing v.valuationSubring)

/-- **Omega compatibility from coordinates of the three root types.** Over a henselian base, if
one member of the apartment class has, on every relative root group for the actual centralizer,
an equivariant coordinate family, or quadratic unitary coordinates with the tower depth, or (for
the double of a multipliable root) the central tower depth, the whole class is
Omega-compatible. -/
theorem isOmegaCompatible_of_rootCoordinateTypes {D : KPApartmentData i (order v)}
    {C : CentralizerDatum i} {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier)
    (hc : ∀ a ∈ relativeRoots i,
      Nonempty (RootCoordinateFamilyEquivariance v i C.j C.s φ a) ∨
      (∃ R : RootUnitaryCoordinates i C.j C.s a,
        ∀ p, φ a (R.equiv p) = SU3Root.towerDepth k R.base R.extension v hH p) ∨
      ∃ b, 2 • b = a ∧ ∃ R : RootUnitaryCoordinates i C.j C.s b,
        ∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution R.base R.extension),
          φ a (R.equiv q.val) = SU3Root.towerCentralDepth k R.base R.extension v hH q) :
    IsOmegaCompatible v D C := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsClosedImmersion C.j.hom.hom.left := C.isClosedSubgroup
  have : IsAffine C.Z.X.left := isAffine_of_isAffineHom C.j.hom.hom.left
  exact (isOmegaCompatible_iff_of_mem hφ).mpr
    (isCentralizerCompatible_of_rootCoordinateTypes hH C.isRepresentedBy C.bijective hc)

end Apartment

end IntegerValuation

end Langlands.Geometry.Building
