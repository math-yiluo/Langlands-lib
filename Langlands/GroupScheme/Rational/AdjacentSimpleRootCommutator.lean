import Langlands.GroupScheme.Rational.SteinbergRootRepresentatives
import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation
import Langlands.GroupScheme.Rational.WeightSemigroupSupport
import Langlands.GroupScheme.Rational.SteinbergModifiedRootProduct

/-! # Commutators of adjacent simple root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

/-- Two distinct simple roots are linearly independent, so no strictly positive integral
combination of them vanishes. -/
theorem simple_add_ne_zero (a b : p.base.support) (hab : a ≠ b) (n m : ℕ) (hn : 0 < n) :
    n • p.rootDatum.root a + m • p.rootDatum.root b ≠ 0 := by
  have hli : LinearIndependent ℤ (fun j : p.base.support => p.rootDatum.root j) :=
    p.base.linearIndepOn_root
  have hpair : LinearIndependent ℤ ![p.rootDatum.root a, p.rootDatum.root b] := by
    have hinj : Function.Injective ![a, b] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    have h := hli.comp ![a, b] hinj
    convert h using 1
    ext i
    fin_cases i <;> rfl
  intro h0
  have h := LinearIndependent.pair_iff.mp hpair (n : ℤ) (m : ℤ) (by
    simpa only [natCast_zsmul] using h0)
  omega

/-- If two simple roots `a`, `b` have mutual pairings `-1`, then the only root of the form
`n a + m b` with `n, m ≥ 1` is `a + b`. -/
theorem adjacent_root_combination (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing (a : p.rootIndex) (b : p.rootIndex) = -1)
    (hba : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hroot : n • p.rootDatum.root a + m • p.rootDatum.root b ∈ roots p.inclusion) :
    n = 1 ∧ m = 1 := by
  -- reflections preserve the roots
  have hrefl (c : p.base.support) (χ : characterLattice p.torus) (hχ : χ ∈ roots p.inclusion) :
      p.rootDatum.reflection (c : p.rootIndex) χ ∈ roots p.inclusion := by
    rw [← p.isRootDatum.2.1] at hχ ⊢
    exact p.rootDatum.mapsTo_reflection_root (c : p.rootIndex) hχ
  -- `s_a (n a + m b) = (m - n) a + m b` and `s_b (n a + m b) = n a + (n - m) b`
  have hsa : p.rootDatum.reflection (a : p.rootIndex)
      (n • p.rootDatum.root a + m • p.rootDatum.root b) =
      ((m : ℤ) - n) • p.rootDatum.root a + (m : ℤ) • p.rootDatum.root b := by
    simp only [map_add, map_nsmul, p.rootDatum.reflection_apply_self,
      p.rootDatum.reflection_apply_root, hba]
    module
  have hsb : p.rootDatum.reflection (b : p.rootIndex)
      (n • p.rootDatum.root a + m • p.rootDatum.root b) =
      (n : ℤ) • p.rootDatum.root a + ((n : ℤ) - m) • p.rootDatum.root b := by
    simp only [map_add, map_nsmul, p.rootDatum.reflection_apply_self,
      p.rootDatum.reflection_apply_root, hab']
    module
  have hnm : n ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    have hr := hrefl a _ hroot
    rw [hsa] at hr
    obtain ⟨_, hnot⟩ := p.strict_mixed_simple_ne_zero_not_root b a hab.symm m (n - m) hm
      (by omega)
    apply hnot
    convert hr using 1
    rw [← natCast_zsmul, ← natCast_zsmul, Nat.cast_sub hlt.le]
    module
  have hmn : m ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    have hr := hrefl b _ hroot
    rw [hsb] at hr
    obtain ⟨_, hnot⟩ := p.strict_mixed_simple_ne_zero_not_root a b hab n (m - n) hn
      (by omega)
    apply hnot
    convert hr using 1
    rw [← natCast_zsmul, ← natCast_zsmul, Nat.cast_sub hlt.le]
    module
  have heq : m = n := le_antisymm hmn hnm
  subst heq
  suffices hm1 : m = 1 from ⟨hm1, hm1⟩
  -- `m (a + b)` is a root; `a + b` is a root; reducedness forces `m = 1`.
  have hsum : p.rootDatum.root (p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)) =
      p.rootDatum.root a + p.rootDatum.root b := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hba, neg_one_smul,
      sub_neg_eq_add, add_comm]
  set r₀ := p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)
  rw [← p.isRootDatum.2.1] at hroot
  obtain ⟨β, hβ⟩ := hroot
  have hβr : p.rootDatum.root β = m • p.rootDatum.root r₀ := by
    rw [hβ, hsum, smul_add]
  have hdep : ¬ LinearIndependent ℤ ![p.rootDatum.root β, p.rootDatum.root r₀] := by
    intro hli
    have h := LinearIndependent.pair_iff.mp hli 1 (-(m : ℤ)) (by
      rw [hβr, one_smul, neg_smul, natCast_zsmul, add_neg_cancel])
    exact one_ne_zero h.1
  have hpm := p.isReduced.eq_or_eq_neg β r₀ hdep
  have hpair : p.rootDatum.pairing β r₀ = 2 * (m : ℤ) := by
    rw [← p.rootDatum.root_coroot_eq_pairing, hβr, map_nsmul, LinearMap.smul_apply,
      p.rootDatum.root_coroot_eq_pairing, RootPairing.pairing_same, nsmul_eq_mul]
    ring
  rcases hpm with h | h
  · have h2 : p.rootDatum.pairing β r₀ = 2 := by
      rw [← p.rootDatum.root_coroot_eq_pairing, h, p.rootDatum.root_coroot_eq_pairing,
        RootPairing.pairing_same]
    omega
  · have h2 : p.rootDatum.pairing β r₀ = -2 := by
      rw [← p.rootDatum.root_coroot_eq_pairing, h, map_neg, LinearMap.neg_apply,
        p.rootDatum.root_coroot_eq_pairing, RootPairing.pairing_same]
    omega

/-- **Commutator of adjacent simple root subgroups.** If two distinct simple roots `a`, `b`
have mutual pairings `-1` and `α` is the root `a + b`, then on every test the commutator
`x y x⁻¹ y⁻¹` of points of the root subgroups of `a` and `b` lies in the root subgroup of
`α`. -/
theorem adjacent_commutator_mem (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing (a : p.rootIndex) (b : p.rootIndex) = -1)
    (hba : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1)
    {α : p.rootIndex}
    (hα : p.rootDatum.root α = p.rootDatum.root a + p.rootDatum.root b)
    {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root b)).carrier Z) :
    x * y * x⁻¹ * y⁻¹ ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier Z := by
  let : Smooth G.X.hom := p.isConnectedReductive.smooth
  let action := AutomorphicAction.conjugation p.inclusion
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail (p.rootDatum.root a) 1)).carrier Z := by
    change x ∈ (RelativeRoot.weightFiltration action (p.rootDatum.root a) 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup p.isSplitTorus p.inclusion _
      (p.rootDatum.ne_zero _)]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail (p.rootDatum.root b) 1)).carrier Z := by
    change y ∈ (RelativeRoot.weightFiltration action (p.rootDatum.root b) 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup p.isSplitTorus p.inclusion _
      (p.rootDatum.ne_zero _)]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G inferInstance inferInstance
    p.torus p.isSplitTorus action
    (RelativeRoot.cyclicTail (p.rootDatum.root a) 1)
    (RelativeRoot.cyclicTail (p.rootDatum.root b) 1) Z x y hx' hy'
  have hle : RelativeRoot.semigroupSubgroup action
      (RelativeRoot.semigroupSum (RelativeRoot.cyclicTail (p.rootDatum.root a) 1)
        (RelativeRoot.cyclicTail (p.rootDatum.root b) 1)) ≤
      RelativeRoot.semigroupSubgroup action
        (RelativeRoot.cyclicTail (p.rootDatum.root α) 1) := by
    apply RelativeRoot.semigroupSubgroup_mono_on_weightSupport
    rintro χ hweight ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨m, _, hm, rfl⟩, rfl⟩
    have hzero := p.simple_add_ne_zero a b hab n m hn
    have hroot : n • p.rootDatum.root a + m • p.rootDatum.root b ∈ roots p.inclusion :=
      (RelativeRoot.mem_actionWeightSupport_conjugation_iff p.inclusion hzero).mp hweight
    obtain ⟨rfl, rfl⟩ := p.adjacent_root_combination a b hab hab' hba n m hn hm hroot
    exact ⟨1, le_rfl, one_pos, by rw [hα, one_smul, one_smul, one_smul]⟩
  have h' := hle Z h
  change _ ∈ (RelativeRoot.weightFiltration action (p.rootDatum.root α) 1).carrier Z at h'
  rwa [RelativeRoot.weightFiltration_one_eq_subgroup p.isSplitTorus p.inclusion _
    (p.rootDatum.ne_zero _)] at h'

/-- Reordering form of `adjacent_commutator_mem`: `x y = y x g` for a point `g` of the root
subgroup of `α = a + b`. -/
theorem adjacent_mul_eq_mul_mul (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing (a : p.rootIndex) (b : p.rootIndex) = -1)
    (hba : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1)
    {α : p.rootIndex}
    (hα : p.rootDatum.root α = p.rootDatum.root a + p.rootDatum.root b)
    {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root b)).carrier Z) :
    ∃ g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier Z,
      x * y = y * x * g := by
  have h := p.adjacent_commutator_mem a b hab hab' hba hα
    (inv_mem hx) (inv_mem hy)
  refine ⟨x⁻¹ * y⁻¹ * x⁻¹⁻¹ * y⁻¹⁻¹, h, ?_⟩
  group

namespace RootParametrization

variable {p}

/-- Root maps are additive on the points of every test. -/
theorem point_add {α : p.rootIndex} (x : p.RootParametrization α)
    (T : Over (Spec (CommRingCat.of k))) (c c' : Γ(T.left, ⊤)) :
    x.point T (c + c') = x.point T c * x.point T c' := by
  have h : VectorGroup.scalarPoint (CommRingCat.of k) T (c + c') =
      VectorGroup.scalarPoint (CommRingCat.of k) T c *
        VectorGroup.scalarPoint (CommRingCat.of k) T c' :=
    VectorGroup.points_ext fun j => by
      rw [VectorGroup.coordinates_mul, Pi.add_apply, VectorGroup.coordinates_scalarPoint,
        VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint]
  rw [point, h, MonObj.mul_comp]
  rfl

/-- Root maps are additive on rational points. -/
theorem rationalPoint_add {α : p.rootIndex} (x : p.RootParametrization α) (c c' : k) :
    x.rationalPoint (c + c') = x.rationalPoint c * x.rationalPoint c' := by
  rw [rationalPoint, map_add, point_add]
  rfl

/-- Root maps send negation to inversion on rational points. -/
theorem rationalPoint_neg {α : p.rootIndex} (x : p.RootParametrization α) (c : k) :
    x.rationalPoint (-c) = (x.rationalPoint c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rationalPoint_add, neg_add_cancel]
  simp [rationalPoint]

/-- Root maps are injective on rational points. -/
theorem rationalPoint_injective {α : p.rootIndex} (x : p.RootParametrization α) :
    Function.Injective x.rationalPoint := by
  intro c c' h
  by_contra hne
  apply x.rationalPoint_ne_one (sub_ne_zero.mpr hne)
  rw [sub_eq_add_neg, rationalPoint_add, rationalPoint_neg, h, mul_inv_cancel]

/-- Every rational point of the root subgroup is a value of the root map. -/
theorem exists_rationalPoint_eq {α : p.rootIndex} (x : p.RootParametrization α)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier
      (Over.mk (𝟙 _))) :
    ∃ r : k, x.rationalPoint r = g := by
  obtain ⟨c, hc⟩ := (x.mem_rootSubgroup_iff _ g).mp hg
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom c, ?_⟩
  rw [rationalPoint, ← hc]
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c

end RootParametrization

/-- **Rational reordering of adjacent simple root factors.** For distinct simple roots `a`,
`b` with mutual pairings `-1`, any root map `xα` of the root `α = a + b`, and any root maps
`xa`, `xb` of `a` and `b`, every product `xa(s) xb(t)` equals `xb(t) xa(s) xα(r)` for some
`r`. -/
theorem adjacent_rationalPoint_reorder (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing (a : p.rootIndex) (b : p.rootIndex) = -1)
    (hba : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1)
    {α : p.rootIndex}
    (hα : p.rootDatum.root α = p.rootDatum.root a + p.rootDatum.root b)
    (xa : p.RootParametrization a) (xb : p.RootParametrization b)
    (xα : p.RootParametrization α) (s t : k) :
    ∃ r : k, xa.rationalPoint s * xb.rationalPoint t =
      xb.rationalPoint t * xa.rationalPoint s * xα.rationalPoint r := by
  obtain ⟨g, hg, he⟩ := p.adjacent_mul_eq_mul_mul a b hab hab' hba hα
    (xa.rationalPoint_mem s) (xb.rationalPoint_mem t)
  obtain ⟨r, rfl⟩ := xα.exists_rationalPoint_eq hg
  exact ⟨r, he⟩

end Langlands.GroupScheme.SplitPinning
