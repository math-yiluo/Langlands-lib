import Langlands.GroupScheme.Rational.CentralSubgroupGeometry
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.AbelianScheme.Multiplication
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Smooth stable central subgroups killed by a prime -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PowerImage

variable {B : Scheme.{u}} {Z : GroupScheme B} [IsCommMonObj Z.X]

/-- Natural-number multiplication evaluates to natural powers on every test. -/
theorem points_multiplication_nat (q : ℕ) (T : Over B) (x : T ⟶ Z.X) :
    x ≫ (multiplication Z (q : ℤ)).hom.hom = x ^ q := by
  simp only [points_multiplication, zpow_natCast]

/-- A uniform exponent kills the actual multiplication morphism. -/
theorem multiplication_eq_one_of_uniformExponent {q : ℕ}
    (hq : HasUniformPowerExponent Z q) : multiplication Z (q : ℤ) = 1 := by
  apply hom_ext_points
  intro T x
  simpa only [points_multiplication_nat, Grp.Hom.hom_one, Mon.Hom.hom_one,
    MonObj.comp_one] using hq T x

/-- A nontrivial group with a bounded q-power exponent has a last nontrivial
q-power morphism. -/
theorem exists_last_nontrivial_multiplication (q : ℕ)
    (hZ : SubgroupFunctor.range (𝟙 Z) ≠ ⊥)
    (hq : ∃ r, HasUniformPowerExponent Z (q ^ r)) :
    ∃ n, multiplication Z (q ^ n : ℕ) ≠ 1 ∧
      multiplication Z (q ^ (n + 1) : ℕ) = 1 := by
  classical
  have h : ∃ r, multiplication Z (q ^ r : ℕ) = 1 := by
    obtain ⟨r, hr⟩ := hq
    exact ⟨r, multiplication_eq_one_of_uniformExponent hr⟩
  have hzero : multiplication Z (q ^ 0 : ℕ) ≠ 1 := by
    intro hz
    have hid : (𝟙 Z.X) = (1 : Z.X ⟶ Z.X) := by
      simpa only [pow_zero, Nat.cast_one, multiplication_one,
        Grp.id_hom_hom, Grp.Hom.hom_one, Mon.Hom.hom_one] using
        congrArg (fun f : Z ⟶ Z => f.hom.hom) hz
    apply hZ
    apply SubgroupFunctor.ext
    intro T
    change (SubgroupFunctor.range (𝟙 Z)).carrier T = ⊥
    apply le_antisymm _ bot_le
    intro x _hx
    change x = 1
    simpa only [Category.comp_id, MonObj.comp_one] using
      congrArg (fun f => x ≫ f) hid
  have hpos : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    exact hzero (hz ▸ Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  have he : Nat.find h - 1 + 1 = Nat.find h := by omega
  rw [he]
  exact Nat.find_spec h

variable {H : GroupScheme B}

/-- Every actual automorphic action commutes with natural multiplication. -/
theorem multiplication_equivariant (b : AutomorphicAction H Z) (q : ℕ) :
    b.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction
      (multiplication Z (q : ℤ)).hom.hom := by
  intro T h x
  change b.act h x ≫ (multiplication Z (q : ℤ)).hom.hom =
    b.act h (x ≫ (multiplication Z (q : ℤ)).hom.hom)
  rw [points_multiplication_nat, points_multiplication_nat]
  exact (map_pow (b.pointAut T h) x q).symm

/-- The preceding power morphism has source image killed by q. -/
theorem image_killed_of_succ_eq_one (q n : ℕ)
    (hn : multiplication Z (q ^ (n + 1) : ℕ) = 1) :
    (multiplication Z (q ^ n : ℕ)).hom.hom ≫
      (multiplication Z (q : ℤ)).hom.hom = 1 := by
  have hm : multiplication Z (q ^ n : ℕ) ≫ multiplication Z (q : ℤ) = 1 := by
    rw [← multiplication_mul, ← Nat.cast_mul, ← pow_succ]
    exact hn
  simpa only [Grp.comp_hom_hom, Grp.Hom.hom_one, Mon.Hom.hom_one] using
    congrArg (fun f : Z ⟶ Z => f.hom.hom) hm

variable [IsSeparated Z.X.hom] {V : Over B} {f : V ⟶ Z.X}

/-- Closed-kernel minimality extends annihilation from the source image to its
whole generated subgroup on every scheme test. -/
theorem GeneratedImage.hasUniformPowerExponent (D : GeneratedImage f) (q : ℕ)
    (hf : f ≫ (multiplication Z (q : ℤ)).hom.hom = 1) :
    HasUniformPowerExponent D.group q := by
  have hle : closedImageEnvelope f ≤
      SubgroupFunctor.range (kernelι (multiplication Z (q : ℤ))) := by
    apply closedImageEnvelope_le f (kernelι (multiplication Z (q : ℤ)))
      (by
        change IsClosedImmersion (kernelι (multiplication Z (q : ℤ))).hom.hom.left
        infer_instance)
    apply (factorsThrough_iff_containsImage f _).2
    intro T v
    apply (mem_range_kernelι_iff _ _).2
    rw [Category.assoc, hf, MonObj.comp_one]
  let : Mono D.inclusion.hom.hom := D.represents.1
  intro T x
  apply (cancel_mono D.inclusion.hom.hom).1
  rw [MonObj.pow_comp, MonObj.one_comp]
  rw [← points_multiplication_nat]
  apply (mem_range_kernelι_iff _ _).1
  apply hle T
  rw [← D.represents.2]
  exact SubgroupFunctor.mem_range.2 ⟨x, rfl⟩

end PowerImage

/-- An actual nontrivial smooth connected commutative central closed subgroup
killed by q, with its restricted action and equivariant inclusion. -/
def HasNontrivialSmoothStableTorsionCentralSubgroup
    {k : Type u} [Field k] {H G : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction H G) (q : ℕ) : Prop :=
  ∃ (W : CommGroupScheme (Spec (CommRingCat.of k))) (w : W.toGrp ⟶ G)
    (bW : AutomorphicAction H W.toGrp),
    IsClosedSubgroup w ∧ Smooth W.X.hom ∧ IsAffineHom W.X.hom ∧
    GeometricallyConnected W.X.hom ∧ ConnectedSpace W.X.left ∧ IsCentral w ∧
    b.IsStable (SubgroupFunctor.range w) ∧ SubgroupFunctor.range w ≠ ⊥ ∧
    HasUniformPowerExponent W.toGrp q ∧
    ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ W.X),
      bW.act h v ≫ w.hom.hom = b.act h (v ≫ w.hom.hom)

section Construction

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k]
    {H G Z : GroupScheme (Spec (CommRingCat.of k))}

/-- Extract a smooth stable q-torsion subgroup from any nontrivial smooth
connected affine commutative central subgroup of bounded q-power exponent. -/
theorem hasNontrivialSmoothStableTorsionCentralSubgroup_of_central
    [Smooth Z.X.hom] [IsAffineHom Z.X.hom] [ConnectedSpace Z.X.left]
    [IsCommMonObj Z.X]
    (b : AutomorphicAction H G) (bZ : AutomorphicAction H Z)
    (hH : IsAffineHom H.X.hom) (z : Z ⟶ G) (hz : IsClosedSubgroup z)
    (hcent : IsCentral z) (hnt : SubgroupFunctor.range z ≠ ⊥)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (v : T ⟶ Z.X),
      bZ.act h v ≫ z.hom.hom = b.act h (v ≫ z.hom.hom))
    (q : ℕ) (hq : ∃ r, HasUniformPowerExponent Z (q ^ r)) :
    HasNontrivialSmoothStableTorsionCentralSubgroup b q := by
  let : IsClosedImmersion z.hom.hom.left := hz
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  have hZ : SubgroupFunctor.range (𝟙 Z) ≠ ⊥ := by
    intro hzero
    apply hnt
    apply SubgroupFunctor.ext
    intro T
    change (SubgroupFunctor.range z).carrier T = ⊥
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hy
    have hx : x ∈ (SubgroupFunctor.range (𝟙 Z)).carrier T :=
      SubgroupFunctor.mem_range.2 ⟨x, by simp⟩
    rw [hzero, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    change x ≫ z.hom.hom = 1
    rw [hx, MonObj.one_comp]
  obtain ⟨n, hn, hn'⟩ := PowerImage.exists_last_nontrivial_multiplication q hZ hq
  let f := (multiplication Z (q ^ n : ℕ)).hom.hom
  have hInt := smoothConnectedAffineGeometry.1 k Z
    inferInstance inferInstance inferInstance
  obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k Z
    inferInstance inferInstance Z.X inferInstance inferInstance hInt 1 f
    (by exact MonObj.one_comp f)
  have hStable := bZ.closedImageEnvelope_isStable hH bZ.toPointwiseSchemeAction f
    (PowerImage.multiplication_equivariant bZ (q ^ n))
  let bW := D.action bZ hStable
  let w := D.inclusion ≫ z
  have hw : IsClosedSubgroup w := by
    let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
    change IsClosedImmersion (D.inclusion.hom.hom.left ≫ z.hom.hom.left)
    infer_instance
  let : IsClosedImmersion w.hom.hom.left := hw
  let : Mono w.hom.hom := Over.mono_of_mono_left _
  have hwcent : IsCentral w := hcent.comp D.inclusion
  have hweq : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ D.group.X),
      bW.act h v ≫ w.hom.hom = b.act h (v ≫ w.hom.hom) := by
    intro T h v
    change bW.act h v ≫ D.inclusion.hom.hom ≫ z.hom.hom =
      b.act h (v ≫ D.inclusion.hom.hom ≫ z.hom.hom)
    rw [← Category.assoc, D.action_act_comp, heq, Category.assoc]
  have hwnt : SubgroupFunctor.range w ≠ ⊥ := by
    intro hzero
    have hf : f ≫ z.hom.hom ∈ (SubgroupFunctor.range w).carrier Z.X :=
      SubgroupFunctor.mem_range.2 ⟨D.factor, by
        change D.factor ≫ D.inclusion.hom.hom ≫ z.hom.hom = f ≫ z.hom.hom
        rw [← Category.assoc, D.factor_comp]⟩
    rw [hzero, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hf
    apply hn
    apply hom_ext_points
    intro T x
    have hf' : f = 1 := by
      apply (cancel_mono z.hom.hom).1
      rw [MonObj.one_comp]
      exact hf
    change x ≫ f = x ≫ (1 : Z ⟶ Z).hom.hom
    rw [hf', Grp.Hom.hom_one, Mon.Hom.hom_one]
  have hWt := PowerImage.GeneratedImage.hasUniformPowerExponent D q
    (PowerImage.image_killed_of_succ_eq_one q n hn')
  have hWco : ConnectedSpace D.group.X.left := by
    have : GeometricallyConnected D.group.X.hom := hD.2.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  refine ⟨hwcent.commGroupScheme, w, bW, hw, hD.1, hD.2.1, hD.2.2.1,
    hWco, hwcent, ?_, hwnt, hWt, hweq⟩
  rintro T h y ⟨v, rfl⟩
  exact SubgroupFunctor.mem_range.2 ⟨bW.act h v, hweq T h v⟩

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Every nontrivial smooth connected affine unipotent group in prime
characteristic p has a smooth stable commutative central subgroup killed by p.
The given affine acting group and its actual action are retained. -/
theorem hasNontrivialSmoothStableTorsionCentralSubgroup_of_isUnipotent
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (b : AutomorphicAction H G) (hH : IsAffineHom H.X.hom)
    (hG : SubgroupFunctor.range (𝟙 G) ≠ ⊥) (hU : IsUnipotent G) :
    HasNontrivialSmoothStableTorsionCentralSubgroup b p := by
  obtain ⟨Z, z, bZ, hc, hs, ha, _hgc, hco, hcent, _hstable, hnt, heq⟩ :=
    hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent b hH hG hU
  let : IsClosedImmersion z.hom.hom.left := hc
  let : Mono z.hom.hom := Over.mono_of_mono_left _
  let := hs
  let := ha
  let := hco
  let := hcent.isCommMonObj
  obtain ⟨r, hr⟩ := exists_hasUniformPowerExponent_of_isUnipotent p hU
  exact hasNontrivialSmoothStableTorsionCentralSubgroup_of_central
    b bZ hH z hc hcent hnt heq p ⟨r, hr.of_mono z⟩

end Construction

end Langlands.GroupScheme
