import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Dynamic.BaseConnectedProof
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement

/-! # Finiteness of the rational characters of a presented parabolic

The proof of `rationalCharacterLattice` uses only that the group is smooth, affine and
connected. A parabolic `P` of a connected reductive group with a compatible root presentation
is smooth (`IsParabolicSubgroup.smooth`) and connected: its image is a dynamic parabolic
`P_G(ζ)` (field `realization` of the presentation), and dynamic parabolics of connected affine
groups of finite type over a field are connected (`connectedSpace_parabolic`). Hence `X^*(P)`
is a free `ℤ`-module of finite rank. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.GroupScheme

open CharacterLatticeProof CharacterUnits CharacterLattice in
/-- Over a field `k`, the rational characters of a smooth connected affine group form a free
`ℤ`-module of finite rank (the proof of `rationalCharacterLattice`, which uses no more). -/
theorem rationalCharacters_free_finite_of_smooth {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [ConnectedSpace G.X.left] :
    Module.Free ℤ (rationalCharacters G) ∧ Module.Finite ℤ (rationalCharacters G) := by
  classical
  have := isDomain_coord G
  let K : Type u := CommRingCat.of k
  let _ : Field K := inferInstanceAs (Field k)
  set D := Coord G
  set L := FractionRing D
  let w : Multiplicative (rationalCharacters G) →* L :=
    { toFun := fun χ => algebraMap D L (unit χ.toAdd : D)
      map_one' := by simp [unit_zero]
      map_mul' := fun a b => by simp [toAdd_mul, unit_add] }
  have hw : LinearIndependent K (wa w) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K D L) :=
      IsFractionRing.injective D L
    exact (linearIndependent_unit (G := G)).map' (IsScalarTower.toAlgHom K D L).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨s, hs⟩ := (Lie.coordinateAlgebraFiniteType G).out
  refine free_and_finite (k := K) w hw (s.image (algebraMap D L)) fun χ => ?_
  change algebraMap D L (unit χ : D) ∈ _
  rw [Finset.coe_image, ← IsScalarTower.coe_toAlgHom' K D L, Algebra.adjoin_image]
  exact Subalgebra.mem_map.mpr ⟨_, hs ▸ Algebra.mem_top, rfl⟩

namespace ParabolicRootPresentation

variable {k : Type u} [Field k] {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {P M G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- A presented parabolic of a connected affine group of finite type is connected: its image is
a dynamic parabolic. -/
theorem connectedSpace (r : ParabolicRootPresentation p l a) [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] : ConnectedSpace P.X.left := by
  obtain ⟨ζ, -, hζ, -⟩ := r.isCompatible.realization
  have h := r.isCompatible.parabolic.isClosedSubgroup.isRepresentedBy_range
  rw [hζ] at h
  exact DynamicBaseConnected.connectedSpace_parabolic G _ h

/-- The rational characters of a presented parabolic `P` of a connected reductive group form a
free `ℤ`-module of finite rank. -/
theorem rationalCharacters_free_finite (r : ParabolicRootPresentation p l a)
    (hG : IsConnectedReductive G) [IsAffine P.X.left] :
    Module.Free ℤ (rationalCharacters P) ∧ Module.Finite ℤ (rationalCharacters P) := by
  have := hG.smooth
  have := hG.connectedSpace
  have := r.connectedSpace
  have := r.isCompatible.parabolic.smooth
  exact rationalCharacters_free_finite_of_smooth P

end ParabolicRootPresentation

end Langlands.GroupScheme
