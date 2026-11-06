import Langlands.GroupScheme.SelfNormalizingAmbient.HopfIdeal
import Langlands.GroupScheme.SelfNormalizingAmbient.Krull
import Langlands.RingTheory.Smooth.SectionJets

/-! # Stabilizing every infinitesimal neighbourhood of a smooth subgroup normalizes it

Let `F` be a group-valued functor on commutative `R`-algebras corepresented by `B`, and let
`H` be a family of subgroups cut out by an ideal `J` of `B` with `B ⧸ J` smooth and flat over
`R`, with domain fibres over fields, and `J` finitely generated. A point stabilizing all jet
subfunctors cut out by `J ⊔ I ^ (n + 1)` normalizes `H`. If `H` is self-normalizing and the
jet quotients `B ⧸ (J ⊔ I ^ (n + 1))` are projective, then a single jet subfunctor has
stabilizer exactly `H`.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.GroupScheme.Corepresented

open SelfNormalizingAmbient

/-- Jet quotients of smooth algebras along a section are flat. -/
theorem flat_quotient_ker_pow (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] (ε : C →ₐ[A] A) (n : ℕ) :
    Module.Flat A (C ⧸ RingHom.ker ε ^ (n + 1)) := by
  have := (Algebra.Smooth.finite_projective_quotient_ker_pow ε n).2
  infer_instance

/-- If every element of a finitely generated ideal `L` is killed by some `1 - j` with `j ∈ I`,
then a single such `1 - j` kills `L`. -/
theorem exists_one_sub_mul_eq_zero_of_fg {A : Type u} [CommRing A] {L I : Ideal A}
    (hL : L.FG) (h : ∀ l ∈ L, ∃ j ∈ I, (1 - j) * l = 0) :
    ∃ j ∈ I, ∀ l ∈ L, (1 - j) * l = 0 := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have key : ∀ t : Finset A, (t : Set A) ⊆ s → ∃ j ∈ I, ∀ l ∈ t, (1 - j) * l = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨0, I.zero_mem, fun l hl => absurd hl (Finset.notMem_empty l)⟩
    | insert a t _ ih =>
      intro hts
      obtain ⟨j₁, hj₁, hj₁t⟩ := ih (subset_trans (Finset.coe_subset.2 (Finset.subset_insert a t)) hts)
      obtain ⟨j₂, hj₂, hj₂a⟩ :=
        h a (Ideal.subset_span (hts (Finset.mem_coe.2 (Finset.mem_insert_self a t))))
      refine ⟨j₁ + j₂ - j₁ * j₂, I.sub_mem (I.add_mem hj₁ hj₂) (I.mul_mem_left _ hj₂), ?_⟩
      have hfac : 1 - (j₁ + j₂ - j₁ * j₂) = (1 - j₁) * (1 - j₂) := by ring
      intro l hl
      rw [hfac]
      rcases Finset.mem_insert.1 hl with rfl | hl
      · rw [mul_assoc, hj₂a, mul_zero]
      · rw [mul_comm (1 - j₁), mul_assoc, hj₁t l hl, mul_zero]
  obtain ⟨j, hj, hjs⟩ := key s le_rfl
  refine ⟨j, hj, fun l hl => ?_⟩
  refine Submodule.span_induction (fun x hx => hjs x hx) (mul_zero _) ?_ ?_ hl
  · intro x y _ _ hx hy
    rw [mul_add, hx, hy, add_zero]
  · intro r x _ hx
    rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- The stabilizer condition is symmetric under inversion. -/
theorem Stabilizes.inv {K : Ideal B} {A : CommAlgCat.{u} R} {g : F.obj A}
    (hg : Stabilizes e K g) : Stabilizes e K g⁻¹ := by
  intro A' f x hx
  obtain ⟨h₁, h₂⟩ := hg A' f x hx
  rw [map_inv, inv_inv]
  exact ⟨h₂, h₁⟩

section KeyStep

variable {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}
  (hH : IsCutOutBy e H J) {S : CommAlgCat.{u} R}

theorem cutCorepresentableBy_homEquiv_symm_mk {T : CommAlgCat.{u} R}
    (x : (cutFunctor hH).obj T) (b : B) :
    ((cutCorepresentableBy hH).homEquiv.symm x).hom (Ideal.Quotient.mk J b) =
      (e.homEquiv.symm x.1).hom b :=
  rfl

theorem tensorQuotientLeft_comp_tensorPairMap {T : CommAlgCat.{u} R} (s : S ⟶ T)
    (x : (cutFunctor hH).obj T) :
    tensorQuotientLeft J S ≫ tensorPairMap (cutCorepresentableBy hH) s x = s := by
  apply CommAlgCat.hom_ext
  ext a
  rw [CommAlgCat.hom_comp, AlgHom.comp_apply]
  change (tensorPairMap (cutCorepresentableBy hH) s x).hom (a ⊗ₜ 1) = s.hom a
  rw [tensorPairMap_tmul, map_one, mul_one]

theorem map_tensorPairMap_universalCutPoint {T : CommAlgCat.{u} R} (s : S ⟶ T)
    (x : (cutFunctor hH).obj T) :
    F.map (tensorPairMap (cutCorepresentableBy hH) s x) (universalCutPoint e J S) = x.1 := by
  apply e.homEquiv.symm.injective
  rw [homEquiv_symm_map, universalCutPoint, Equiv.symm_apply_apply]
  apply CommAlgCat.hom_ext
  ext b
  rw [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_comp, AlgHom.comp_apply]
  change (tensorPairMap (cutCorepresentableBy hH) s x).hom (1 ⊗ₜ Ideal.Quotient.mk J b) = _
  rw [tensorPairMap_tmul, map_one, one_mul, cutCorepresentableBy_homEquiv_symm_mk]

variable (g : F.obj S)

theorem map_tensorPairMap_conj {T : CommAlgCat.{u} R} (s : S ⟶ T) (x : (cutFunctor hH).obj T) :
    F.map (tensorPairMap (cutCorepresentableBy hH) s x)
        (F.map (tensorQuotientLeft J S) g * universalCutPoint e J S *
          (F.map (tensorQuotientLeft J S) g)⁻¹) =
      F.map s g * x.1 * (F.map s g)⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_tensorPairMap_universalCutPoint, ← ConcreteCategory.comp_apply,
    ← F.map_comp, tensorQuotientLeft_comp_tensorPairMap]

/-- The algebra map `tensorPairMap (𝟙 S) x` kills the ideal generated by the image of `J` under the
classifying map of `g u g⁻¹` exactly when `g` conjugates `x` into `H`. -/
theorem tensorPairMap_kills_iff {T : CommAlgCat.{u} R} (s : S ⟶ T) (x : (cutFunctor hH).obj T) :
    (∀ l ∈ J.map (e.homEquiv.symm (F.map (tensorQuotientLeft J S) g *
        universalCutPoint e J S * (F.map (tensorQuotientLeft J S) g)⁻¹)).hom,
        (tensorPairMap (cutCorepresentableBy hH) s x).hom l = 0) ↔
      F.map s g * x.1 * (F.map s g)⁻¹ ∈ H T := by
  rw [hH, ← map_tensorPairMap_conj hH g s x, homEquiv_symm_map]
  constructor
  · intro h b hb
    rw [CommAlgCat.hom_comp, AlgHom.comp_apply]
    exact h _ (Ideal.mem_map_of_mem _ hb)
  · intro h l hl
    have hle : J.map (e.homEquiv.symm (F.map (tensorQuotientLeft J S) g *
        universalCutPoint e J S * (F.map (tensorQuotientLeft J S) g)⁻¹)).hom ≤
          RingHom.ker (tensorPairMap (cutCorepresentableBy hH) s x).hom := by
      refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have := h b hb
      rwa [CommAlgCat.hom_comp, AlgHom.comp_apply] at this
    exact hle hl

variable (S) in
/-- The counit of `S ⊗[R] (B ⧸ J)` as an `S`-algebra map, evaluating at the unit point. -/
def cutCounit : S ⊗[R] (B ⧸ J) →ₐ[S] S :=
  { (tensorPairMap (cutCorepresentableBy hH) (𝟙 S) 1).hom with
    commutes' := fun r => by
      change (tensorPairMap (cutCorepresentableBy hH) (𝟙 S) 1).hom (r ⊗ₜ 1) = r
      rw [tensorPairMap_tmul, map_one, mul_one]
      rfl }

theorem cutCounit_apply (z : S ⊗[R] (B ⧸ J)) :
    cutCounit hH S z = (tensorPairMap (cutCorepresentableBy hH) (𝟙 S) 1).hom z :=
  rfl

/-- The classifying map of the universal cut point sends the augmentation ideal into the
kernel of the counit. -/
theorem classify_universalCutPoint_mem_ker {b : B} (hb : b ∈ augIdeal e) :
    (e.homEquiv.symm (universalCutPoint e J S)).hom b ∈ RingHom.ker (cutCounit hH S) := by
  rw [universalCutPoint, Equiv.symm_apply_apply, RingHom.mem_ker, CommAlgCat.hom_comp,
    AlgHom.comp_apply, cutCounit_apply]
  change (tensorPairMap (cutCorepresentableBy hH) (𝟙 S) 1).hom (1 ⊗ₜ Ideal.Quotient.mk J b) = 0
  rw [tensorPairMap_tmul, map_one, one_mul, cutCorepresentableBy_homEquiv_symm_mk]
  have hunit := LinearEmbedding.cls_one e S
  dsimp only [LinearEmbedding.cls, LinearEmbedding.unitMap] at hunit
  change (e.homEquiv.symm (1 : F.obj S)).hom b = 0
  rw [hunit, CommAlgCat.hom_comp, AlgHom.comp_apply]
  rw [augIdeal, RingHom.mem_ker] at hb
  rw [hb, map_zero]

/-- Stabilizing the `n`-th jet subfunctor forces the classifying map of `g u g⁻¹` to send `J`
into the `(n + 1)`-st power of the kernel of the counit. -/
theorem classify_conj_mem_pow {n : ℕ} (hg : Stabilizes e (jetIdeal e J n) g) {b : B}
    (hb : b ∈ J) :
    (e.homEquiv.symm (F.map (tensorQuotientLeft J S) g * universalCutPoint e J S *
        (F.map (tensorQuotientLeft J S) g)⁻¹)).hom b ∈
      RingHom.ker (cutCounit hH S) ^ (n + 1) := by
  set N : Ideal (S ⊗[R] (B ⧸ J)) := RingHom.ker (cutCounit hH S) ^ (n + 1)
  let q : tensorQuotient J S ⟶ CommAlgCat.of R ((S ⊗[R] (B ⧸ J)) ⧸ N) :=
    CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)
  have h1 : (augIdeal e).map (e.homEquiv.symm (universalCutPoint e J S)).hom ≤
      RingHom.ker (cutCounit hH S) :=
    Ideal.map_le_iff_le_comap.2 fun b hb => classify_universalCutPoint_mem_ker hH hb
  have h2 : (augIdeal e ^ (n + 1)).map (e.homEquiv.symm (universalCutPoint e J S)).hom ≤ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 _
  have hu : VanishesOn e (jetIdeal e J n) (F.map q (universalCutPoint e J S)) := by
    rw [jetIdeal, vanishesOn_sup]
    refine ⟨(vanishesOn_universalCutPoint S).map q, fun b hb => ?_⟩
    rw [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply]
    change Ideal.Quotient.mkₐ R N _ = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact h2 (Ideal.mem_map_of_mem _ hb)
  have h := (hg _ (tensorQuotientLeft J S ≫ q) _ hu).1
  rw [F.map_comp, ConcreteCategory.comp_apply, ← map_inv, ← map_mul, ← map_mul] at h
  have h' := h b (le_jetIdeal hb)
  rw [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply] at h'
  change Ideal.Quotient.mkₐ R N _ = 0 at h'
  rwa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h'

variable [Module.Flat R (B ⧸ J)] [Algebra.Smooth R (B ⧸ J)]

include hH in
/-- **Key step.** A point stabilizing every jet subfunctor of `H` conjugates the universal point
of `H` into `H`. -/
theorem conj_mem_of_stabilizes
    (hdom : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] (B ⧸ J))) (hJ : J.FG)
    (hg : ∀ n, Stabilizes e (jetIdeal e J n) g) :
    F.map (tensorQuotientLeft J S) g * universalCutPoint e J S *
      (F.map (tensorQuotientLeft J S) g)⁻¹ ∈ H (tensorQuotient J S) := by
  set c := F.map (tensorQuotientLeft J S) g * universalCutPoint e J S *
    (F.map (tensorQuotientLeft J S) g)⁻¹ with hc
  set L : Ideal (S ⊗[R] (B ⧸ J)) := J.map (e.homEquiv.symm c).hom with hLdef
  have hK : ∀ l ∈ L, ∃ j ∈ RingHom.ker (cutCounit hH S), (1 - j) * l = 0 := by
    intro l hl
    refine exists_one_sub_mul_eq_zero_of_mem_pow flat_quotient_ker_pow (cutCounit hH S)
      fun n => ?_
    have hle : L ≤ RingHom.ker (cutCounit hH S) ^ (n + 1) :=
      Ideal.map_le_iff_le_comap.2 fun b hb => classify_conj_mem_pow hH g (hg n) hb
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (hle hl)
  have hLfg : L.FG := hJ.map (e.homEquiv.symm c).hom.toRingHom
  obtain ⟨j, hj, hjL⟩ := exists_one_sub_mul_eq_zero_of_fg hLfg hK
  have hf : (tensorPairMap (cutCorepresentableBy hH) (𝟙 S) 1).hom (1 - j) = 1 := by
    rw [← cutCounit_apply, map_sub, map_one, RingHom.mem_ker.1 hj, sub_zero]
  have hL0 : L = ⊥ := by
    refine eq_bot_of_mul_closed (e := cutCorepresentableBy hH) hdom L ?_ hf hjL
    intro T s x y hx hy
    rw [tensorPairMap_kills_iff hH g] at hx hy ⊢
    have hxy : F.map s g * (x * y).1 * (F.map s g)⁻¹ =
        (F.map s g * x.1 * (F.map s g)⁻¹) * (F.map s g * y.1 * (F.map s g)⁻¹) := by
      change F.map s g * (x.1 * y.1) * (F.map s g)⁻¹ = _
      group
    rw [hxy]
    exact mul_mem hx hy
  rw [hH]
  intro b hb
  have hbL : (e.homEquiv.symm c).hom b ∈ L := Ideal.mem_map_of_mem _ hb
  rw [hL0, Ideal.mem_bot] at hbL
  exact hbL

include hH in
/-- **A point stabilizing every jet subfunctor of `H` normalizes `H`.** -/
theorem mem_normalizerFamily_of_stabilizes
    (hdom : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] (B ⧸ J))) (hJ : J.FG)
    (hg : ∀ n, Stabilizes e (jetIdeal e J n) g) : g ∈ normalizerFamily H S := by
  rw [mem_normalizerFamily_iff hH]
  refine ⟨conj_mem_of_stabilizes hH g hdom hJ hg, ?_⟩
  have h := conj_mem_of_stabilizes hH g⁻¹ hdom hJ fun n => (hg n).inv
  rwa [map_inv, inv_inv] at h

end KeyStep

section Stabilization

variable {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}
  (hH : IsCutOutBy e H J) [Module.Flat R (B ⧸ J)] [Algebra.Smooth R (B ⧸ J)]
  [∀ n, Module.Projective R (B ⧸ jetIdeal e J n)]

include hH in
/-- For a self-normalizing `H`, the union of the stabilizer ideals of the jet subfunctors
contains `J`. -/
theorem le_iSup_subgroupNormalizerIdeal_jetIdeal
    (hdom : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] (B ⧸ J))) (hJ : J.FG)
    (hself : ∀ A, normalizerFamily H A ≤ H A) :
    J ≤ ⨆ n, subgroupNormalizerIdeal e (jetIdeal e J n) := by
  set a := ⨆ n, subgroupNormalizerIdeal e (jetIdeal e J n)
  have hg : ∀ n, Stabilizes e (jetIdeal e J n) (e.homEquiv (quotientMap a)) := fun n => by
    rw [stabilizes_iff]
    intro b hb
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (le_iSup (fun n => subgroupNormalizerIdeal e (jetIdeal e J n)) n hb)
  have hmem := hself _ (mem_normalizerFamily_of_stabilizes hH _ hdom hJ hg)
  rw [hH, Equiv.symm_apply_apply] at hmem
  intro b hb
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hmem b hb)

include hH in
/-- **Finite stabilization.** For a self-normalizing `H`, a single jet subfunctor has
stabilizer exactly `H`. -/
theorem exists_stabilizes_jetIdeal_iff
    (hdom : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] (B ⧸ J))) (hJ : J.FG)
    (hself : ∀ A, normalizerFamily H A ≤ H A) :
    ∃ N : ℕ, ∀ (A : CommAlgCat.{u} R) (x : F.obj A),
      Stabilizes e (jetIdeal e J N) x ↔ x ∈ H A := by
  let a : ℕ → Ideal B := fun n => subgroupNormalizerIdeal e (jetIdeal e J n)
  have hmono : Monotone a :=
    monotone_nat_of_le_succ fun n => subgroupNormalizerIdeal_jetIdeal_mono
  have hc := (Submodule.fg_iff_compact J).1 hJ
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hc
  obtain ⟨-, ⟨N, rfl⟩, hN⟩ := hc (Set.range a) (Set.range_nonempty a)
    (directedOn_range.2 hmono.directed_le)
    (by rw [sSup_range]; exact le_iSup_subgroupNormalizerIdeal_jetIdeal hH hdom hJ hself)
  have heq : a N = J := le_antisymm (subgroupNormalizerIdeal_jetIdeal_le hH) hN
  refine ⟨N, fun A x => ?_⟩
  obtain ⟨φ, rfl⟩ := e.homEquiv.surjective x
  rw [stabilizes_iff, hH, Equiv.symm_apply_apply]
  change a N ≤ _ ↔ _
  rw [heq]
  exact ⟨fun h b hb => h hb, fun h b hb => h b hb⟩

end Stabilization

end Langlands.GroupScheme.Corepresented
