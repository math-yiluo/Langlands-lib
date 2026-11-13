import Langlands.Geometry.Building.RootQuotientFieldCoordinates
import Langlands.Geometry.Building.RootDatumValuation
import Langlands.GroupScheme.Rational.RootHeisenbergEquivariant
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability

/-! # Rational torus points acting on rational root groups through root values

Let `f ≫ j : S → T → G` be a maximal split torus whose centralizer is the torus `j : T → G`,
with `T` split by a finite Galois extension `L/k`. For a relative root `a` and an absolute root
`β` whose Galois orbit is the restriction fiber of `a`, a rational point `z` of `T` acts on
`U_a(k)` (non-multipliable `a`) or on `U_a(k)/U_{2a}(k)` (multipliable `a`) as multiplication by
the root value `β(z)` in field coordinates. This module draws two consequences:

* if the root values of `z` on the fibers of `a` (and of `2a`) are `1`, then `z` centralizes
  `U_a(k)`;
* any two nontrivial points of `U_a(k)` (modulo `U_{2a}(k)`) are carried into each other by every
  `z` with one prescribed nonzero root value.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RelativeRoot

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

variable [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]

section NonMultipliable

/-- Every point of a non-multipliable rational root group is the point with some field
coordinate. -/
theorem exists_rootPointLieEquiv_symm_eq
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) :
    ∃ x : rootOrbitField k L j β,
      ((RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh).symm
        (rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit x)).toMul.val =
        g := by
  set R := RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh
  set W := rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit
  refine ⟨W.symm (R (Additive.ofMul ⟨g, hg⟩)), ?_⟩
  rw [LinearEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  rfl

/-- **Trivial root value centralizes.** A rational torus point whose value at `β` is `1`
commutes with every point of the non-multipliable rational root group `U_a(k)`. -/
theorem commute_of_rootOrbitCharacterValue_eq_one
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (z : rationalPoints T.toGrp)
    (hz : rootOrbitCharacterValue k L j β
      (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = 1)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) :
    Commute (rationalPoints.map j z) g := by
  obtain ⟨x, rfl⟩ := exists_rootPointLieEquiv_symm_eq k L f j hG hj hS hT ha hhigh β
    horbit hg
  have h := conjugation_rootPointLieEquiv_symm k L f j hG hj hS hcent hT ha hhigh β horbit z x
  rw [hz, one_mul] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- **Transitivity on a non-multipliable root group.** For nontrivial `u, u' ∈ U_a(k)` there is
a nonzero field value `c` such that every rational torus point with value `c` at `β` conjugates
`u` to `u'`. -/
theorem exists_rootOrbitCharacterValue_conj_eq
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a)
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {u u' : rationalPoints G}
    (hu : u ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu' : u' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) (hu1 : u ≠ 1)
    (hu1' : u' ≠ 1) :
    ∃ c : rootOrbitField k L j β, c ≠ 0 ∧ ∀ z : rationalPoints T.toGrp,
      rootOrbitCharacterValue k L j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = c →
        rationalPoints.map j z * u * (rationalPoints.map j z)⁻¹ = u' := by
  set R := RelativeRoot.rootPointLieEquiv hS (CommGroupScheme.groupHom f ≫ j) ha.1 hhigh
  set W := rootOrbitFieldWeightSpaceLinearEquiv k L j f a hG hj hS hT ha.1 β horbit
  obtain ⟨x, rfl⟩ := exists_rootPointLieEquiv_symm_eq k L f j hG hj hS hT ha hhigh β
    horbit hu
  obtain ⟨x', rfl⟩ := exists_rootPointLieEquiv_symm_eq k L f j hG hj hS hT ha hhigh β
    horbit hu'
  have hne (y : rootOrbitField k L j β) (hy : ((R.symm (W y)).toMul.val : rationalPoints G) ≠ 1) :
      y ≠ 0 := by
    rintro rfl
    apply hy
    rw [map_zero, map_zero]
    rfl
  have hx := hne x hu1
  have hx' := hne x' hu1'
  refine ⟨x' * x⁻¹, mul_ne_zero hx' (inv_ne_zero hx), fun z hz => ?_⟩
  rw [conjugation_rootPointLieEquiv_symm k L f j hG hj hS hcent hT ha hhigh β horbit z x, hz,
    mul_assoc, inv_mul_cancel₀ hx, mul_one]

end NonMultipliable

section Multipliable

/-- The quotient datum of a multipliable root together with the facts used below: a
representative `jU` of `U_a`, a representative `j₂` of `U_{2a}`, and the quotient
`q : U → V = U / U₂`. -/
structure QuotientPackage (i : S.toGrp ⟶ G) (a : characterLattice S) where
  U : GroupScheme (Spec (CommRingCat.of k))
  U₂ : GroupScheme (Spec (CommRingCat.of k))
  affineU : IsAffineHom U.X.hom
  jU : U ⟶ G
  hjU : (subgroup i a).IsRepresentedBy jU
  j₂ : U₂ ⟶ G
  hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂
  C : DoubleRootCommutatorPairing i a hjU hj₂
  affineV : IsAffineHom C.V.X.hom

omit [LocallyOfFiniteType G.X.hom] [FiniteDimensional k L] [IsGalois k L] in
/-- Quotient packages exist for multipliable roots with no higher multiples. -/
theorem nonempty_quotientPackage (hS : IsSplitTorus S.toGrp) {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    Nonempty (QuotientPackage k (CommGroupScheme.groupHom f ≫ j) a) := by
  have h2a : 2 • a ≠ 0 := hS.nsmul_ne_zero ha (by omega)
  obtain ⟨U, jU, hjU, hjUc, -, -⟩ :=
    subgroup_has_smooth_closed_representative hS (CommGroupScheme.groupHom f ≫ j) a ha
  obtain ⟨U₂, j₂, hj₂, -, -, -⟩ :=
    subgroup_has_smooth_closed_representative hS (CommGroupScheme.groupHom f ≫ j) (2 • a) h2a
  have : IsAffineHom U.X.hom := hjUc.isAffineHom
  let C := Classical.choice
    (nonempty_doubleRootCommutatorPairing hS (CommGroupScheme.groupHom f ≫ j) ha hhigh hjU hj₂)
  have hV : IsAffineHom C.V.X.hom := by
    obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
    exact IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  exact ⟨⟨U, U₂, inferInstance, jU, hjU, j₂, hj₂, C, hV⟩⟩

variable {k f j}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- The rational points of `U_a` are the images of the rational points of a representative. -/
theorem QuotientPackage.exists_point {i : S.toGrp ⟶ G} {a : characterLattice S}
    (Q : QuotientPackage k i a) {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    ∃ y : rationalPoints Q.U, y ≫ Q.jU.hom.hom = g := by
  rw [rootGroupPoints, ← Q.hjU.2] at hg
  exact SubgroupFunctor.mem_range.mp hg

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- A rational point of `U` killed by the quotient map lands in `U_{2a}(k)`. -/
theorem QuotientPackage.mem_double_of_comp_q_eq_one {i : S.toGrp ⟶ G} {a : characterLattice S}
    (Q : QuotientPackage k i a) {y : rationalPoints Q.U} (hy : y ≫ Q.C.q.hom.hom = 1) :
    y ≫ Q.jU.hom.hom ∈ rootGroupPoints i (2 • a) := by
  have h := (mem_range_kernelι_iff Q.C.q y).mpr hy
  rw [Q.C.isFppfQuotient.2.2.2] at h
  exact h

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom] in
/-- A rational point of `U` landing in `U_{2a}(k)` is killed by the quotient map. -/
theorem QuotientPackage.comp_q_eq_one_of_mem_double {i : S.toGrp ⟶ G} {a : characterLattice S}
    (Q : QuotientPackage k i a) {y : rationalPoints Q.U}
    (hy : y ≫ Q.jU.hom.hom ∈ rootGroupPoints i (2 • a)) : y ≫ Q.C.q.hom.hom = 1 := by
  apply (mem_range_kernelι_iff Q.C.q y).mp
  rw [Q.C.isFppfQuotient.2.2.2]
  exact hy

variable (k f j)

/-- **Transitivity modulo the doubled root group.** For `u, u' ∈ U_a(k) ∖ U_{2a}(k)` there is a
nonzero field value `c` such that every rational torus point with value `c` at `β` conjugates
`u` into `u' · U_{2a}(k)`. -/
theorem exists_rootOrbitCharacterValue_conj_eq_mul [IsAffineHom T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    {u u' : rationalPoints G}
    (hu : u ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu' : u' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu2 : u ∉ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a))
    (hu2' : u' ∉ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a)) :
    ∃ c : rootOrbitField k L j β, c ≠ 0 ∧ ∀ z : rationalPoints T.toGrp,
      rootOrbitCharacterValue k L j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = c →
        ∃ w ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a),
          rationalPoints.map j z * u * (rationalPoints.map j z)⁻¹ = u' * w := by
  obtain ⟨Q⟩ := nonempty_quotientPackage k f j hS ha hhigh
  have := Q.affineU
  have := Q.affineV
  have hfix := conjugation_act_of_torusCentralizer k f j hcent
  set e := quotientFieldEquiv k L f j Q.C hG hj hS hT ha hhigh β horbit
  obtain ⟨y, rfl⟩ := Q.exists_point hu
  obtain ⟨y', rfl⟩ := Q.exists_point hu'
  -- field coordinates of the images in `V(k)`
  set x := (e.symm (y ≫ Q.C.q.hom.hom)).toAdd
  set x' := (e.symm (y' ≫ Q.C.q.hom.hom)).toAdd
  have hex : e (Multiplicative.ofAdd x) = y ≫ Q.C.q.hom.hom := by
    simp only [x, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hex' : e (Multiplicative.ofAdd x') = y' ≫ Q.C.q.hom.hom := by
    simp only [x', ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hne {y₀ : rationalPoints Q.U}
      (h₀ : y₀ ≫ Q.jU.hom.hom ∉ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a)) :
      (e.symm (y₀ ≫ Q.C.q.hom.hom)).toAdd ≠ 0 := by
    intro h0
    apply h₀
    apply Q.mem_double_of_comp_q_eq_one
    have h1 : e.symm (y₀ ≫ Q.C.q.hom.hom) = 1 := by
      rw [← ofAdd_toAdd (e.symm _), h0, ofAdd_zero]
    rw [← e.apply_symm_apply (y₀ ≫ Q.C.q.hom.hom), h1, map_one]
  have hx := hne hu2
  have hx' := hne hu2'
  refine ⟨x' * x⁻¹, mul_ne_zero hx' (inv_ne_zero hx), fun z hz => ?_⟩
  let ρ := rootActionOfFixesTorus (AutomorphicAction.conjugation j)
    (CommGroupScheme.groupHom f ≫ j) hfix a Q.jU Q.hjU
  -- the action of `z` on the quotient point of `y`
  have hq : ρ.act z y ≫ Q.C.q.hom.hom = y' ≫ Q.C.q.hom.hom := by
    rw [← DoubleRootCommutatorPairing.torusQuotientAction_act_comp, ← hex,
      quotientFieldEquiv_act k L f j Q.C hG hj hS hT ha hhigh β horbit hfix z x, hz, ← hex',
      mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hw : (y'⁻¹ * ρ.act z y) ≫ Q.C.q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, inv_mul_cancel]
  refine ⟨(y'⁻¹ * ρ.act z y) ≫ Q.jU.hom.hom, Q.mem_double_of_comp_q_eq_one hw, ?_⟩
  have hconj : rationalPoints.map j z * (y ≫ Q.jU.hom.hom) * (rationalPoints.map j z)⁻¹ =
      ρ.act z y ≫ Q.jU.hom.hom := by
    rw [rootActionOfFixesTorus_act_comp, AutomorphicAction.conjugation_act]
    rfl
  rw [hconj, MonObj.mul_comp, GrpObj.inv_comp, mul_inv_cancel_left]

/-- **Trivial root values centralize a multipliable root group.** A rational torus point whose
values at `β` (over `a`) and at `β₂` (over `2a`) are `1` commutes with every point of
`U_a(k)`. -/
theorem commute_of_rootOrbitCharacterValue_eq_one_of_multipliable [IsAffineHom T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j) (hS : IsSplitTorus S.toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S} (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β : roots (T := T_L) (G := G_L) j_L)
    (horbit : MulAction.orbit (L ≃ₐ[k] L) β = rootRestrictionFiber k L j f a)
    (ha2 : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (β₂ : roots (T := T_L) (G := G_L) j_L)
    (horbit₂ : MulAction.orbit (L ≃ₐ[k] L) β₂ = rootRestrictionFiber k L j f (2 • a))
    (z : rationalPoints T.toGrp)
    (hz : rootOrbitCharacterValue k L j β
      (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = 1)
    (hz₂ : rootOrbitCharacterValue k L j β₂
      (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = 1)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) :
    Commute (rationalPoints.map j z) g := by
  obtain ⟨Q⟩ := nonempty_quotientPackage k f j hS ha hhigh
  have := Q.affineU
  have := Q.affineV
  have hfix := conjugation_act_of_torusCentralizer k f j hcent
  have hhigh₂ : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) (2 • a) :=
    hasNoHigherRoots_two_nsmul hhigh
  have hD : IsTorus T.toGrp := hj.1
  have hs : ∀ (X : Over (Spec (CommRingCat.of k))) (t : X ⟶ S.X) (g : X ⟶ G.X),
      (AutomorphicAction.conjugation j).act (t ≫ (CommGroupScheme.groupHom f).hom.hom) g =
        (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom) * g *
          (t ≫ (CommGroupScheme.groupHom f ≫ j).hom.hom)⁻¹ := by
    intro X t g
    rw [AutomorphicAction.conjugation_act, Grp.comp_hom_hom, Category.assoc]
  obtain ⟨N⟩ := nonempty_equivariantHeisenbergNormalForm Q.C hS ha hhigh hD
    (AutomorphicAction.conjugation j) hfix (CommGroupScheme.groupHom f) hs
  let ρ := rootActionOfFixesTorus (AutomorphicAction.conjugation j)
    (CommGroupScheme.groupHom f ≫ j) hfix a Q.jU Q.hjU
  let ρ₂ := rootActionOfFixesTorus (AutomorphicAction.conjugation j)
    (CommGroupScheme.groupHom f ≫ j) hfix (2 • a) Q.j₂ Q.hj₂
  have : Mono Q.jU.hom.hom := Q.hjU.1
  have : Mono Q.j₂.hom.hom := Q.hj₂.1
  set e := quotientFieldEquiv k L f j Q.C hG hj hS hT ha hhigh β horbit
  obtain ⟨y, rfl⟩ := Q.exists_point hg
  -- `z` fixes every rational point of the quotient
  have hV (v : rationalPoints Q.C.V) :
      (Q.C.torusQuotientAction (AutomorphicAction.conjugation j) hfix).act z v = v := by
    rw [← e.apply_symm_apply v, ← ofAdd_toAdd (e.symm v),
      quotientFieldEquiv_act k L f j Q.C hG hj hS hT ha hhigh β horbit hfix z, hz, one_mul]
  -- `z` fixes every rational point of the doubled root group
  have hU₂ (w : rationalPoints Q.U₂) : ρ₂.act z w = w := by
    apply (cancel_mono Q.j₂.hom.hom).mp
    rw [rootActionOfFixesTorus_act_comp, AutomorphicAction.conjugation_act]
    have hc := commute_of_rootOrbitCharacterValue_eq_one k L f j hG hj hS hcent hT ha2 hhigh₂
      β₂ horbit₂ z hz₂ (g := w ≫ Q.j₂.hom.hom) (by
        rw [rootGroupPoints, ← Q.hj₂.2]
        exact ⟨w, rfl⟩)
    exact mul_inv_eq_of_eq_mul hc.eq
  -- the decomposition `y = incl(w) * sec(q y)`
  have hker : (y * ((y ≫ Q.C.q.hom.hom) ≫ N.sec)⁻¹) ≫ Q.C.q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, N.sec_comp, Category.comp_id,
      mul_inv_cancel]
  have hmem := (mem_range_kernelι_iff Q.C.q _).mpr hker
  rw [← N.range_inclusion] at hmem
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hmem
  have hy : y = (w ≫ N.inclusion.hom.hom) * ((y ≫ Q.C.q.hom.hom) ≫ N.sec) := by
    rw [hw, inv_mul_cancel_right]
  have hfixy : ρ.act z y = y := by
    conv_lhs => rw [hy]
    rw [AutomorphicAction.act_mul_right, N.act_inclusion_torus, N.act_sec_torus, hU₂, hV, ← hy]
  have hconj : rationalPoints.map j z * (y ≫ Q.jU.hom.hom) * (rationalPoints.map j z)⁻¹ =
      y ≫ Q.jU.hom.hom := by
    conv_rhs => rw [← hfixy]
    rw [rootActionOfFixesTorus_act_comp, AutomorphicAction.conjugation_act]
    rfl
  exact mul_inv_eq_iff_eq_mul.mp hconj

end Multipliable

end Langlands.Geometry.Building
