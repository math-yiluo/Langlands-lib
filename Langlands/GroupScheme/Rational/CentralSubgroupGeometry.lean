import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.AlgebraicGeometry.SmoothProperConnectedZeroDimensionalRankProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof

/-! # Commutativity and positive dimension of central subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A central monomorphism makes its source an actual commutative group object. -/
theorem IsCentral.isCommMonObj {B : Scheme.{u}} {Z G : GroupScheme B}
    {z : Z ⟶ G} [Mono z.hom.hom] (hz : IsCentral z) : IsCommMonObj Z.X := by
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono z.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp]
  exact (commute_of_mem_center (hz T x) (y ≫ z.hom.hom)).eq

/-- The given central subgroup with its unchanged underlying group scheme,
now regarded as a commutative group scheme. -/
def IsCentral.commGroupScheme {B : Scheme.{u}} {Z G : GroupScheme B}
    {z : Z ⟶ G} [Mono z.hom.hom] (hz : IsCentral z) : CommGroupScheme B where
  toGrp := Z
  comm := hz.isCommMonObj

section Dimension

variable {k : Type u} [Field k] [IsSepClosed k]
    {Z G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Z.X.hom] [IsSeparated Z.X.hom] [ConnectedSpace Z.X.left]

/-- Over a separably closed field, a smooth connected separated group with
nontrivial image has positive relative dimension. -/
theorem exists_positive_relativeDimension_of_range_ne_bot (z : Z ⟶ G)
    (hz : SubgroupFunctor.range z ≠ ⊥) :
    ∃ n : ℕ, 0 < n ∧ SmoothOfRelativeDimension n Z.X.hom := by
  obtain ⟨n, hn⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    Z.X.left _ Z.X.hom inferInstance inferInstance
  refine ⟨n, ?_, hn⟩
  by_contra hp
  have hn0 : n = 0 := by omega
  subst n
  let : Etale Z.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hn
  let : IsIso Z.X.hom :=
    Langlands.AlgebraicGeometry.isIso_of_connected_separated_etale Z.X.hom
  apply hz
  apply SubgroupFunctor.ext
  intro T
  change (SubgroupFunctor.range z).carrier T = ⊥
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hv
  have hx : x = 1 := by
    apply Over.OverMorphism.ext
    apply (cancel_mono Z.X.hom).1
    exact (Over.w x).trans (Over.w (1 : T ⟶ Z.X)).symm
  change x ≫ z.hom.hom = 1
  rw [hx, MonObj.one_comp]

end Dimension

section Unipotent

variable {k : Type u} [Field k] [IsSepClosed k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The constructed smooth stable centre can be chosen as an actual commutative
group scheme of positive relative dimension over a separably closed field. -/
theorem exists_commutative_positiveDimensional_stable_central_subgroup_of_isUnipotent
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k))) (z : Z.toGrp ⟶ G)
      (bZ : AutomorphicAction H Z.toGrp) (n : ℕ),
      IsClosedSubgroup z ∧ Smooth Z.X.hom ∧ IsAffineHom Z.X.hom ∧
      GeometricallyConnected Z.X.hom ∧ ConnectedSpace Z.X.left ∧ IsCentral z ∧
      b.IsStable (SubgroupFunctor.range z) ∧ SubgroupFunctor.range z ≠ ⊥ ∧
      0 < n ∧ SmoothOfRelativeDimension n Z.X.hom ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ Z.X),
        bZ.act h v ≫ z.hom.hom = b.act h (v ≫ z.hom.hom) := by
  obtain ⟨Z, z, bZ, hc, hs, ha, hgc, hco, hcent, hstable, hnt, heq⟩ :=
    hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent b hH hG hU
  let : IsClosedImmersion z.hom.hom.left := hc
  let : Mono z.hom.hom := Over.mono_of_mono_left z.hom.hom
  let := hs
  let := ha
  let := hco
  obtain ⟨n, hn, hdim⟩ := exists_positive_relativeDimension_of_range_ne_bot z hnt
  exact ⟨hcent.commGroupScheme, z, bZ, n, hc, hs, ha, hgc, hco, hcent,
    hstable, hnt, hn, hdim, heq⟩

end Unipotent

end Langlands.GroupScheme
