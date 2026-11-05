import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Central isogenies reflect torus centralizers on every test scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {π : G ⟶ H}

private theorem commute_pow_of_commute_comp
    (hπ : IsCentralIsogeny π) (N : ℕ)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X),
      x ≫ π.hom.hom = 1 → x ^ N = 1)
    {U : Over (Spec (CommRingCat.of k))} (a b : U ⟶ G.X)
    (hab : Commute (a ≫ π.hom.hom) (b ≫ π.hom.hom)) :
    Commute a (b ^ N) := by
  let c : U ⟶ G.X := a * b * a⁻¹ * b⁻¹
  have hcπ : c ≫ π.hom.hom = 1 := by
    simp only [c, MonObj.mul_comp, GrpObj.inv_comp]
    rw [hab.eq]
    group
  have hcb : Commute c b := commute_of_mem_center (hπ.mem_center_of_comp_eq_one hcπ) b
  have hconj : a * b * a⁻¹ = c * b := by simp [c, mul_assoc]
  change a * b ^ N = b ^ N * a
  apply (mul_inv_eq_iff_eq_mul).mp
  rw [← conj_pow, hconj, hcb.mul_pow, hN U c hcπ, one_mul]

/-- Central isogenies reflect membership in a torus centralizer on arbitrary
test schemes, including nonreduced schemes. -/
theorem IsCentralIsogeny.mem_torusCentralizer_iff
    (hπ : IsCentralIsogeny π)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T.toGrp) (j : T.toGrp ⟶ G)
    {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X) :
    g ≫ π.hom.hom ∈ (torusCentralizer (j ≫ π)).carrier U ↔
      g ∈ (torusCentralizer j).carrier U := by
  constructor
  · intro hg
    obtain ⟨N, hNpos, hNker⟩ := hπ.exists_pow_eq_one_kernel
    have hN : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
        x ≫ π.hom.hom = 1 → x ^ N = 1 := by
      intro V x hx
      obtain ⟨y, hy⟩ :=
        SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff π x).mpr hx)
      rw [← hy, ← MonObj.pow_comp, hNker V y, MonObj.one_comp]
    have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
    let m := (multiplication T.toGrp (N : ℤ)).hom.hom
    have hm0 : (N : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have : Flat m.left := (hT.flat_and_surjective_multiplication hm0).1
    have : Surjective m.left := (hT.flat_and_surjective_multiplication hm0).2
    have : QuasiCompact m.left := inferInstance
    intro V a t
    let W : Over (Spec (CommRingCat.of k)) :=
      Over.mk (pullback.fst t.left m.left ≫ V.hom)
    let q : W ⟶ V := Over.homMk (pullback.fst t.left m.left) rfl
    let r : W ⟶ T.X := Over.homMk (pullback.snd t.left m.left) (by
      rw [← Over.w m, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w t]
      rfl)
    have hroot : q ≫ t = r ≫ m := Over.OverMorphism.ext pullback.condition
    have : Flat q.left := by
      change Flat (pullback.fst t.left m.left)
      infer_instance
    have : Surjective q.left := by
      change Surjective (pullback.fst t.left m.left)
      infer_instance
    have : QuasiCompact q.left := by
      change QuasiCompact (pullback.fst t.left m.left)
      infer_instance
    have : Epi q := Over.epi_of_epi_left _
    have hab : Commute ((q ≫ a ≫ g) ≫ π.hom.hom)
        ((r ≫ j.hom.hom) ≫ π.hom.hom) := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using hg W (q ≫ a) r
    have hc := commute_pow_of_commute_comp hπ N hN
      (q ≫ a ≫ g) (r ≫ j.hom.hom) hab
    have hp : (r ≫ j.hom.hom) ^ N = q ≫ t ≫ j.hom.hom := by
      rw [← Category.assoc q t, hroot, Category.assoc]
      change (r ≫ j.hom.hom) ^ N =
        r ≫ (multiplication T.toGrp (N : ℤ)).hom.hom ≫ j.hom.hom
      rw [← Category.assoc, points_multiplication, zpow_natCast, MonObj.pow_comp]
    rw [hp] at hc
    change (a ≫ g) * (t ≫ j.hom.hom) = (t ≫ j.hom.hom) * (a ≫ g)
    apply (cancel_epi q).mp
    simpa only [MonObj.comp_mul, Category.assoc] using hc.eq
  · intro hg V a t
    have hc := (hg V a t).map (IsMonHom.monoidHom π.hom.hom V)
    simpa only [IsMonHom.monoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Grp.comp_hom_hom, Category.assoc] using hc

/-- The inverse image of the centralizer of the composite torus homomorphism
is exactly the original torus centralizer as an all-test subgroup functor. -/
theorem IsCentralIsogeny.torusCentralizer_comap
    (hπ : IsCentralIsogeny π)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T.toGrp) (j : T.toGrp ⟶ G) :
    (torusCentralizer (j ≫ π)).comap π = torusCentralizer j := by
  ext U g
  exact hπ.mem_torusCentralizer_iff hT j g

/-- The universe-general reflection assertion for actual field tori. -/
def CentralIsogenyTorusCentralizerReflectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (π : G ⟶ H), IsCentralIsogeny π → IsTorus T.toGrp →
    ∀ j : T.toGrp ⟶ G,
      (torusCentralizer (j ≫ π)).comap π = torusCentralizer j

theorem centralIsogenyTorusCentralizerReflection :
    CentralIsogenyTorusCentralizerReflectionStatement.{u} := by
  intro k _ G H T π hπ hT j
  exact hπ.torusCentralizer_comap hT j

end Langlands.GroupScheme
