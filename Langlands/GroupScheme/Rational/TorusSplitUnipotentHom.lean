import Langlands.GroupScheme.Rational.TorusVectorCocycle
import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # Homomorphisms from tori to split-unipotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))}

private theorem zero_conjugation_act {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (v : T ⟶ V.X) :
    (AutomorphicAction.conjugation (0 : H ⟶ V)).act h v = v := by
  rw [AutomorphicAction.conjugation_act]
  change (h ≫ (1 : H.X ⟶ V.X)) * v * (h ≫ (1 : H.X ⟶ V.X))⁻¹ = v
  rw [MonObj.comp_one, one_mul, inv_one, mul_one]

namespace RelativeRoot

/-- Every homomorphism from an arbitrary torus to a naturally coordinated
vector group sends every point on every scheme test to the identity. -/
theorem IsVectorGroupOfDimension.comp_eq_one_of_isTorus {d : ℕ}
    (hV : IsVectorGroupOfDimension V d) (hH : IsTorus H)
    (f : H ⟶ V) (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ H.X) :
    t ≫ f.hom.hom = 1 := by
  obtain ⟨e, he⟩ := hV
  let a := AutomorphicAction.conjugation (0 : H ⟶ V)
  have hlin : IsLinearVectorCoordinates a e := by
    refine ⟨he, ?_⟩
    intro W h c v
    simp only [a, zero_conjugation_act, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  let c : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := {
    hom := snd _ H.X ≫ f.hom.hom
    one b := by
      rw [← Category.assoc, lift_snd, MonObj.one_comp]
    mul b h h' := by
      simp only [← Category.assoc, lift_snd, MonObj.mul_comp, a, zero_conjugation_act] }
  let : IsAffineHom V.X.hom :=
    (show IsVectorGroupOfDimension V d from ⟨e, he⟩).isAffineHom
  obtain ⟨v, hv⟩ := exists_coboundary_of_isTorus a e hlin hH c
  have h := congrArg
    (fun z : a.Cocycle (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =>
      z.eval (Over.homMk T.hom (by simp)) t) hv
  rw [AutomorphicAction.eval_coboundary] at h
  simpa only [AutomorphicAction.Cocycle.eval, c, lift_snd_assoc,
    a, zero_conjugation_act, mul_inv_cancel] using h

/-- A torus has only the trivial homomorphism to a vector group. -/
theorem IsVectorGroupOfDimension.hom_eq_zero_of_isTorus {d : ℕ}
    (hV : IsVectorGroupOfDimension V d) (hH : IsTorus H)
    (f : H ⟶ V) : f = 0 := by
  apply (Grp.forget _).map_injective
  change f.hom.hom = (1 : H.X ⟶ V.X)
  simpa only [Category.id_comp] using
    hV.comp_eq_one_of_isTorus hH f H.X (𝟙 H.X)

/-- A homomorphism from a torus to any group with a finite normal Ga-series
is the trivial homomorphism. Affineness of the target is not an extra premise. -/
theorem HasSplitSeries.hom_eq_zero_of_isTorus {n : ℕ}
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (hU : HasSplitSeries n U) (hH : IsTorus H) (f : H ⟶ U) : f = 0 := by
  induction n generalizing U with
  | zero =>
    apply (Grp.forget _).map_injective
    change f.hom.hom = (1 : H.X ⟶ U.X)
    have hx : f.hom.hom ∈ (SubgroupFunctor.range (𝟙 U)).carrier H.X := by
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨f.hom.hom, ?_⟩
      change f.hom.hom ≫ 𝟙 U.X = f.hom.hom
      exact Category.comp_id _
    rw [hU, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    exact hx
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, _, _, _, hq, hV, hK⟩ := hU
    let : IsClosedImmersion j.hom.hom.left := hj
    let : Mono j.hom.hom := Over.mono_of_mono_left _
    have hzero : f ≫ q = 0 := hV.hom_eq_zero_of_isTorus hH (f ≫ q)
    have hle : SubgroupFunctor.range f ≤ SubgroupFunctor.range j := by
      intro T x hx
      obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [← hq.2.2.2, mem_range_kernelι_iff]
      rw [Category.assoc, ← Grp.comp_hom_hom, hzero]
      change t ≫ (1 : H.X ⟶ V.X) = 1
      exact MonObj.comp_one _
    have hfmem : f.hom.hom ∈ (SubgroupFunctor.range f).carrier H.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 H.X, Category.id_comp _⟩
    obtain ⟨g₀, hg₀⟩ := SubgroupFunctor.mem_range.mp (hle H.X hfmem)
    let : IsMonHom g₀ := {
      one_hom := by
        apply (cancel_mono j.hom.hom).mp
        rw [Category.assoc, hg₀, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j.hom.hom).mp
        rw [Category.assoc, hg₀, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
          tensorHom_comp_tensorHom_assoc, hg₀] }
    let g : H ⟶ K := Grp.homMk g₀
    have hg : g ≫ j = f := Grp.hom_ext _ _ hg₀
    rw [← hg, ih hK g, CategoryTheory.Limits.zero_comp]

/-- A torus has only the trivial homomorphism to a split-unipotent group. -/
theorem IsSplitUnipotent.hom_eq_zero_of_isTorus
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (hU : IsSplitUnipotent U) (hH : IsTorus H) (f : H ⟶ U) : f = 0 := by
  obtain ⟨n, hn⟩ := hU
  exact hn.hom_eq_zero_of_isTorus hH f

/-- The canonical unique homomorphism from a torus to a split-unipotent group. -/
@[instance_reducible]
def IsSplitUnipotent.uniqueHomFromTorus
    {U : GroupScheme (Spec (CommRingCat.of k))}
    (hU : IsSplitUnipotent U) (hH : IsTorus H) : Unique (H ⟶ U) where
  default := 0
  uniq f := hU.hom_eq_zero_of_isTorus hH f

end RelativeRoot

end Langlands.GroupScheme
