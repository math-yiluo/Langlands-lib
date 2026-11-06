import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.Torus.Multiplication
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Rational.MaximalTorusGenericConjugatorLift

/-! # Normalizer reflection in central-isogeny torus squares -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ H}

namespace CentralIsogenyNormalizerReflection

private theorem kernel_pow_eq_one (hq : IsCentralIsogeny q) :
    ∃ N : ℕ, 0 < N ∧ ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X),
      x ≫ q.hom.hom = 1 → x ^ N = 1 := by
  obtain ⟨N, hNpos, hNker⟩ := hq.exists_pow_eq_one_kernel
  refine ⟨N, hNpos, fun U x hx => ?_⟩
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp ((mem_range_kernelι_iff q x).mpr hx)
  rw [← hy, ← MonObj.pow_comp, hNker U y, MonObj.one_comp]

/-- A point over the image torus has a power in the source torus. -/
theorem pow_mem_range (hq : IsCentralIsogeny q) (N : ℕ)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X),
      x ≫ q.hom.hom = 1 → x ^ N = 1)
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (f : T.toGrp ⟶ S.toGrp) (j : S.toGrp ⟶ H)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    (hsquare : i ≫ q = f ≫ j)
    {U : Over (Spec (CommRingCat.of k))} {x : U ⟶ G.X}
    (hx : x ≫ q.hom.hom ∈ (SubgroupFunctor.range j).carrier U) :
    x ^ N ∈ (SubgroupFunctor.range i).carrier U := by
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left f.hom.hom.left ≫ U.hom)
  let p : V ⟶ U := Over.homMk (pullback.fst y.left f.hom.hom.left) rfl
  let t : V ⟶ T.X := Over.homMk (pullback.snd y.left f.hom.hom.left) (by
    rw [← Over.w f.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have hpt : p ≫ y = t ≫ f.hom.hom := Over.OverMorphism.ext pullback.condition
  have : EffectiveEpi p.left := by
    change EffectiveEpi (pullback.fst y.left f.hom.hom.left)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range i p
  have he : (p ≫ x) ≫ q.hom.hom = (t ≫ i.hom.hom) ≫ q.hom.hom := by
    have hs := congrArg (fun a => a.hom.hom) hsquare
    simp only [Grp.comp_hom_hom] at hs
    rw [Category.assoc, ← hy, ← Category.assoc p y, hpt, Category.assoc,
      ← hs, ← Category.assoc]
  let c : V ⟶ G.X := (p ≫ x) * (t ≫ i.hom.hom)⁻¹
  have hc : c ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel]
  have hcomm : Commute c (t ≫ i.hom.hom) :=
    commute_of_mem_center (hq.mem_center_of_comp_eq_one hc) _
  have hpow : (p ≫ x) ^ N = (t ≫ i.hom.hom) ^ N := by
    have hdecomp : p ≫ x = c * (t ≫ i.hom.hom) := by simp [c, mul_assoc]
    rw [hdecomp, hcomm.mul_pow, hN V c hc, one_mul]
  rw [MonObj.comp_pow, hpow, ← MonObj.pow_comp]
  exact SubgroupFunctor.mem_range.mpr ⟨t ^ N, rfl⟩

/-- Fpqc power roots turn conjugation modulo the central kernel into actual
containment in the source torus. -/
private theorem conj_mem_range (hq : IsCentralIsogeny q) (hT : IsTorus T.toGrp)
    (N : ℕ) (hNpos : 0 < N)
    (hN : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ G.X),
      x ≫ q.hom.hom = 1 → x ^ N = 1)
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (f : T.toGrp ⟶ S.toGrp) (j : S.toGrp ⟶ H)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    (hsquare : i ≫ q = f ≫ j)
    {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X) (t : U ⟶ T.X)
    (hg : ∀ (V : Over (Spec (CommRingCat.of k))) (p : V ⟶ U) (r : V ⟶ T.X),
      ((p ≫ g) * (r ≫ i.hom.hom) * (p ≫ g)⁻¹) ≫ q.hom.hom ∈
        (SubgroupFunctor.range j).carrier V) :
    g * (t ≫ i.hom.hom) * g⁻¹ ∈ (SubgroupFunctor.range i).carrier U := by
  have : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let m := (multiplication T.toGrp (N : ℤ)).hom.hom
  have hm0 : (N : ℤ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have : Flat m.left := (hT.flat_and_surjective_multiplication hm0).1
  have : Surjective m.left := (hT.flat_and_surjective_multiplication hm0).2
  have : QuasiCompact m.left := inferInstance
  let V : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst t.left m.left ≫ U.hom)
  let p : V ⟶ U := Over.homMk (pullback.fst t.left m.left) rfl
  let r : V ⟶ T.X := Over.homMk (pullback.snd t.left m.left) (by
    rw [← Over.w m, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w t]
    rfl)
  have hroot : p ≫ t = r ≫ m := Over.OverMorphism.ext pullback.condition
  have : EffectiveEpi p.left := by
    change EffectiveEpi (pullback.fst t.left m.left)
    infer_instance
  have hpow : (r ≫ i.hom.hom) ^ N = p ≫ t ≫ i.hom.hom := by
    rw [← Category.assoc p t, hroot, Category.assoc]
    change (r ≫ i.hom.hom) ^ N =
      r ≫ (multiplication T.toGrp (N : ℤ)).hom.hom ≫ i.hom.hom
    rw [← Category.assoc, points_multiplication, zpow_natCast, MonObj.pow_comp]
  have hmem := pow_mem_range hq N hN i f j hsquare (hg V p r)
  rw [conj_pow, hpow] at hmem
  apply SubgroupFunctor.mem_range_of_comp_mem_range i p
  simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using hmem

end CentralIsogenyNormalizerReflection

/-- A central isogeny reflects torus normalizers in a commuting square whose
torus restriction is fpqc. This holds on arbitrary, possibly nonreduced, tests. -/
theorem IsCentralIsogeny.reflectsTorusNormalizer_of_fpqc_square
    (hq : IsCentralIsogeny q) (hT : IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (f : T.toGrp ⟶ S.toGrp) (j : S.toGrp ⟶ H)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    (hsquare : i ≫ q = f ≫ j) : ReflectsTorusNormalizer q i j := by
  obtain ⟨N, hNpos, hN⟩ := CentralIsogenyNormalizerReflection.kernel_pow_eq_one hq
  intro U x hx
  rw [mem_torusNormalizer] at hx ⊢
  intro V a t
  have hs := congrArg (fun z => z.hom.hom) hsquare
  simp only [Grp.comp_hom_hom] at hs
  constructor
  · have hm := CentralIsogenyNormalizerReflection.conj_mem_range hq hT N hNpos hN
      i f j hsquare (a ≫ x) t (fun W p r => by
        obtain ⟨⟨z, hz⟩, -⟩ := hx W (p ≫ a) (r ≫ f.hom.hom)
        apply SubgroupFunctor.mem_range.mpr
        refine ⟨z, ?_⟩
        rw [← hz]
        simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs])
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hm
    exact ⟨z, hz.symm⟩
  · have hm := CentralIsogenyNormalizerReflection.conj_mem_range hq hT N hNpos hN
      i f j hsquare (a ≫ x)⁻¹ t (fun W p r => by
        obtain ⟨-, ⟨z, hz⟩⟩ := hx W (p ≫ a) (r ≫ f.hom.hom)
        apply SubgroupFunctor.mem_range.mpr
        refine ⟨z, ?_⟩
        rw [← hz]
        simp only [MonObj.mul_comp, GrpObj.inv_comp, GrpObj.comp_inv, inv_inv,
          Category.assoc, hs])
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hm
    refine ⟨z, ?_⟩
    simpa only [inv_inv] using hz.symm

/-- Normalizer reflection composes along homomorphisms. -/
theorem ReflectsTorusNormalizer.comp
    {K : GroupScheme (Spec (CommRingCat.of k))}
    {R : CommGroupScheme (Spec (CommRingCat.of k))}
    {p : H ⟶ K} {i : T.toGrp ⟶ G} {j : S.toGrp ⟶ H} {l : R.toGrp ⟶ K}
    (hq : ReflectsTorusNormalizer q i j) (hp : ReflectsTorusNormalizer p j l) :
    ReflectsTorusNormalizer (q ≫ p) i l := by
  intro U x hx
  apply hq U x
  apply hp U (x ≫ q.hom.hom)
  simpa only [Grp.comp_hom_hom, Category.assoc] using hx

/-- The identity reflects the normalizer of any retained torus. -/
theorem reflectsTorusNormalizer_id (i : T.toGrp ⟶ G) :
    ReflectsTorusNormalizer (𝟙 G) i i := by
  intro U x hx
  simpa only [Grp.id_hom_hom, Category.comp_id] using hx

/-- The all-test normalizer-reflection assertion for fpqc torus squares. -/
def CentralIsogenyTorusNormalizerReflectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    (T S : CommGroupScheme (Spec (CommRingCat.of k)))
    (q : G ⟶ H), IsCentralIsogeny q → IsTorus T.toGrp →
    ∀ (i : T.toGrp ⟶ G) [Mono i.hom.hom]
      (f : T.toGrp ⟶ S.toGrp) (j : S.toGrp ⟶ H)
      [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [QuasiCompact f.hom.hom.left],
      i ≫ q = f ≫ j → ReflectsTorusNormalizer q i j

theorem centralIsogenyTorusNormalizerReflection :
    CentralIsogenyTorusNormalizerReflectionStatement.{u} := by
  intro k _ G H T S q hq hT i _ f j _ _ _ hsquare
  exact hq.reflectsTorusNormalizer_of_fpqc_square hT i f j hsquare

end Langlands.GroupScheme
