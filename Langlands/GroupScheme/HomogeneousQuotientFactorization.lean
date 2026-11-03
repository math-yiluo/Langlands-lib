import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Factoring actual homogeneous quotients through group quotients

An actual homogeneous quotient map descends through an effective group quotient
whose full scheme kernel is contained in its stabilizer. If the stabilizer is
the full preimage of a represented subgroup of the new group, fpqc descent
preserves the exact right-coset fiber condition on every relative test scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFactorization

variable {S : Scheme.{u}} {G H K : GroupScheme S} {Q : Over S}
variable (f : G ⟶ H) (F : SubgroupFunctor G) (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (a b : T ⟶ G.X),
  a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ F.carrier T)
variable (hker : SubgroupFunctor.range (kernelι f) ≤ F)

section Descent

include hfib hker

/-- A quotient map with stabilizer containing the full kernel is constant on
all fibers of the group homomorphism. -/
theorem comp_eq_of_groupQuotient_eq {T : Over S} (a b : T ⟶ G.X)
    (hab : a ≫ f.hom.hom = b ≫ f.hom.hom) : a ≫ q = b ≫ q := by
  apply (hfib T a b).mpr
  apply hker T
  apply (mem_range_kernelι_iff f _).mpr
  rw [MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]

variable [EffectiveEpi f.hom.hom.left]

/-- The actual relative morphism induced by the supplied group quotient. -/
def desc : H.X ⟶ Q :=
  HomogeneousQuotientComparison.desc f.hom.hom q
    (fun _ a b hab => comp_eq_of_groupQuotient_eq f F q hfib hker a b hab)

@[reassoc]
theorem fac_desc : f.hom.hom ≫ desc f F q hfib hker = q :=
  HomogeneousQuotientComparison.fac_desc _ _ _

/-- The factorization equation uniquely determines the induced relative map. -/
theorem desc_unique (r : H.X ⟶ Q) (hr : f.hom.hom ≫ r = q) :
    r = desc f F q hfib hker :=
  HomogeneousQuotientComparison.desc_unique _ _ _ r hr

end Descent

/-- A full subgroup preimage contains the entire scheme-theoretic kernel. -/
theorem kernel_le_of_comap (j : K ⟶ H)
    (hpre : F = (SubgroupFunctor.range j).comap f) :
    SubgroupFunctor.range (kernelι f) ≤ F := by
  intro T a ha
  rw [hpre, SubgroupFunctor.mem_comap, (mem_range_kernelι_iff f a).mp ha]
  exact (SubgroupFunctor.range j).carrier T |>.one_mem

section LocalLifts

variable {X Y T : Over S} (p : X ⟶ Y)
variable [QuasiCompact p.left] [Flat p.left] [Surjective p.left]

/-- Any actual relative test map lifts after an fpqc pullback of its source. -/
private theorem exists_fpqc_lift (a : T ⟶ Y) :
    ∃ (V : Over S) (v : V ⟶ T) (b : V ⟶ X),
      QuasiCompact v.left ∧ Flat v.left ∧ Surjective v.left ∧ v ≫ a = b ≫ p := by
  let V : Over S := Over.mk (pullback.fst a.left p.left ≫ T.hom)
  let v : V ⟶ T := Over.homMk (pullback.fst a.left p.left) rfl
  let b : V ⟶ X := Over.homMk (pullback.snd a.left p.left) (by
    rw [← Over.w p, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a]
    rfl)
  refine ⟨V, v, b, ?_, ?_, ?_, Over.OverMorphism.ext pullback.condition⟩
  · change QuasiCompact (pullback.fst a.left p.left)
    infer_instance
  · change Flat (pullback.fst a.left p.left)
    infer_instance
  · change Surjective (pullback.fst a.left p.left)
    infer_instance

/-- Two relative test maps lift simultaneously after a single fpqc cover. -/
private theorem exists_fpqc_lift_pair (a b : T ⟶ Y) :
    ∃ (V : Over S) (v : V ⟶ T) (a' b' : V ⟶ X),
      QuasiCompact v.left ∧ Flat v.left ∧ Surjective v.left ∧
        v ≫ a = a' ≫ p ∧ v ≫ b = b' ≫ p := by
  obtain ⟨V, v, a', hvq, hvf, hvs, ha⟩ := exists_fpqc_lift p a
  obtain ⟨W, w, b', hwq, hwf, hws, hb⟩ := exists_fpqc_lift p (v ≫ b)
  let : QuasiCompact v.left := hvq
  let : Flat v.left := hvf
  let : Surjective v.left := hvs
  let : QuasiCompact w.left := hwq
  let : Flat w.left := hwf
  let : Surjective w.left := hws
  refine ⟨W, w ≫ v, w ≫ a', b', ?_, ?_, ?_, ?_, ?_⟩
  · change QuasiCompact (w.left ≫ v.left)
    infer_instance
  · change Flat (w.left ≫ v.left)
    infer_instance
  · change Surjective (w.left ≫ v.left)
    infer_instance
  · rw [Category.assoc, ha, Category.assoc]
  · simpa only [Category.assoc] using hb

end LocalLifts

section Fibers

variable [QuasiCompact f.hom.hom.left] [Flat f.hom.hom.left]
  [Surjective f.hom.hom.left]

include hfib

/-- Descent along an fpqc group quotient preserves the exact right-coset
fibers for a represented subgroup with the specified full preimage. -/
theorem fibers_of_factorization (r : H.X ⟶ Q) (hr : f.hom.hom ≫ r = q)
    (j : K ⟶ H) [Mono j.hom.hom]
    (hpre : F = (SubgroupFunctor.range j).comap f)
    (T : Over S) (a b : T ⟶ H.X) :
    a ≫ r = b ≫ r ↔ a⁻¹ * b ∈ (SubgroupFunctor.range j).carrier T := by
  obtain ⟨V, v, a', b', hvq, hvf, hvs, ha, hb⟩ :=
    exists_fpqc_lift_pair f.hom.hom a b
  let : QuasiCompact v.left := hvq
  let : Flat v.left := hvf
  let : Surjective v.left := hvs
  let : Epi v := Over.epi_of_epi_left v
  have hmem : a'⁻¹ * b' ∈ F.carrier V ↔
      v ≫ (a⁻¹ * b) ∈ (SubgroupFunctor.range j).carrier V := by
    rw [hpre, SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp,
      MonObj.comp_mul, GrpObj.comp_inv, ha, hb]
  have heq : a' ≫ q = b' ≫ q ↔ v ≫ (a ≫ r) = v ≫ (b ≫ r) := by
    rw [← hr, ← Category.assoc a', ← Category.assoc b', ← ha, ← hb,
      Category.assoc, Category.assoc]
  constructor
  · intro hab
    apply SubgroupFunctor.mem_range_of_comp_mem_range j v
    exact hmem.mp ((hfib V a' b').mp (heq.mpr (by rw [hab])))
  · intro hab
    apply (cancel_epi v).mp
    apply heq.mp
    apply (hfib V a' b').mpr
    exact hmem.mpr ((SubgroupFunctor.range j).comp_mem v hab)

/-- The canonical descended map has the original all-test homogeneous
quotient condition for the specified represented subgroup of the new group. -/
theorem desc_fibers (j : K ⟶ H) [Mono j.hom.hom]
    (hpre : F = (SubgroupFunctor.range j).comap f)
    (T : Over S) (a b : T ⟶ H.X) :
    a ≫ desc f F q hfib hker = b ≫ desc f F q hfib hker ↔
      a⁻¹ * b ∈ (SubgroupFunctor.range j).carrier T :=
  fibers_of_factorization f F q hfib (desc f F q hfib hker)
    (fac_desc f F q hfib hker) j hpre T a b

end Fibers

end Langlands.GroupScheme.HomogeneousQuotientFactorization
