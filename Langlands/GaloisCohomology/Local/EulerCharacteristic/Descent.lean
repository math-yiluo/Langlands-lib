import Langlands.Cohomology.Profinite.Dimension.Basic
import Langlands.Cohomology.Profinite.InflationRestriction.DegreeOne
import Langlands.Cohomology.Profinite.InnerConjugation
import Langlands.Cohomology.Profinite.Corestriction
import Langlands.Cohomology.Profinite.Cup.Pairing
import Langlands.Cohomology.Profinite.ClassFormation.Basic

/-!
# Conjugation on the cohomology of a normal subgroup, and descent
-/

noncomputable section

open CategoryTheory

universe u

namespace Langlands.ProfiniteCohomology

-- from ConjAction.lean
open CategoryTheory


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]

theorem cohomologyConj_one (n : ℕ) : cohomologyConj A N n 1 = 𝟙 _ :=
  ProfiniteCohomology.map_eq_id _ (ContinuousMonoidHom.ext fun s => Subtype.ext (by
    change (1 : G)⁻¹ * (s : G) * 1 = s
    group)) (fun a => by change A.ρ 1 a = a; simp) n

theorem cohomologyConj_mul (n : ℕ) (g h : G) :
    cohomologyConj A N n (g * h) = cohomologyConj A N n h ≫ cohomologyConj A N n g := by
  rw [cohomologyConj, cohomologyConj, cohomologyConj, ← map_comp]
  refine ProfiniteCohomology.map_congr _ _ ?_ (fun a => ?_) n
  · refine ContinuousMonoidHom.ext fun s => Subtype.ext ?_
    change (g * h)⁻¹ * (s : G) * (g * h) = h⁻¹ * (g⁻¹ * (s : G) * g) * h
    group
  · change A.ρ (g * h) a = A.ρ g (A.ρ h a)
    rw [map_mul]
    rfl

theorem cohomologyConj_mul_apply (n : ℕ) (g h : G) (x : cohomology (Rep.res N.subtype A) n) :
    (cohomologyConj A N n (g * h)).hom x =
      (cohomologyConj A N n g).hom ((cohomologyConj A N n h).hom x) := by
  rw [cohomologyConj_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
-- A coefficient map used at the types `Rep.res ↑(.id _) A` and `A`, definitionally but not
-- reducibly equal at Lean 4.35, has to be identified for `map_comp` to apply.
@[reassoc]
theorem cohomologyConj_naturality {B : Rep.{u} k G} [IsSmoothRep B] (f : A ⟶ B) (n : ℕ) (g : G) :
    coeffMap ((Rep.resFunctor N.subtype).map f) n ≫ cohomologyConj B N n g =
      cohomologyConj A N n g ≫ coeffMap ((Rep.resFunctor N.subtype).map f) n := by
  rw [coeffMap_eq, cohomologyConj, cohomologyConj,
    ← map_comp, ← map_comp]
  refine ProfiniteCohomology.map_congr _ _ (ContinuousMonoidHom.ext fun s => by simp) (fun a => ?_) n
  exact (Rep.hom_comm_apply f g a).symm

noncomputable def conjShortComplexMor (S : ShortComplex (Rep.{u} k G)) (g : G) :
    (S.map (Rep.resFunctor N.subtype)).map (Rep.resFunctor (conjHom N g)) ⟶
      S.map (Rep.resFunctor N.subtype) where
  τ₁ := conjMor S.X₁ N g
  τ₂ := conjMor S.X₂ N g
  τ₃ := conjMor S.X₃ N g
  comm₁₂ := by
    ext a
    exact (Rep.hom_comm_apply S.f g a)
  comm₂₃ := by
    ext a
    exact (Rep.hom_comm_apply S.g g a)

@[reassoc]
theorem δ_comp_cohomologyConj {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁]
    [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (g : G) :
    δ (shortExact_map_res N hS) i j hij ≫ cohomologyConj S.X₁ N j g =
      cohomologyConj S.X₃ N i g ≫ δ (shortExact_map_res N hS) i j hij :=
  δ_comp_map ⟨(conjHom N g), (continuous_conjHom N g)⟩
    (conjShortComplexMor N S g) _ _ i j hij

section CompactSubgroup

variable [CompactSpace N]

theorem cohomologyConj_of_mem (n : ℕ) {m : G} (hm : m ∈ N) : cohomologyConj A N n m = 𝟙 _ := by
  rw [← cohomologyInnerConj_eq_id (Γ := N) n (Rep.res N.subtype A) ⟨m, hm⟩]
  exact ProfiniteCohomology.map_congr _ _ (ContinuousMonoidHom.ext fun s => by simp) (fun a => rfl) n

theorem cohomologyConj_eq_of_mk_eq (n : ℕ) {g h : G} (hgh : (g : G ⧸ N) = h) :
    cohomologyConj A N n g = cohomologyConj A N n h := by
  have hm : g⁻¹ * h ∈ N := QuotientGroup.eq.1 hgh
  have : h = g * (g⁻¹ * h) := by group
  rw [this, cohomologyConj_mul, cohomologyConj_of_mem A N n hm, Category.id_comp]

noncomputable def cohomologyConjRep (n : ℕ) :
    Representation k (G ⧸ N) (cohomology (Rep.res N.subtype A) n) where
  toFun q := (cohomologyConj A N n q.out).hom
  map_one' := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := 1) (by rw [QuotientGroup.out_eq']; rfl),
      cohomologyConj_one]
    rfl
  map_mul' q r := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := q.out * r.out)
      (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']), cohomologyConj_mul]
    rfl

theorem cohomologyConjRep_mk (n : ℕ) (g : G) (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyConjRep A N n (g : G ⧸ N) x = (cohomologyConj A N n g).hom x := by
  change (cohomologyConj A N n (g : G ⧸ N).out).hom x = _
  rw [cohomologyConj_eq_of_mk_eq A N n (QuotientGroup.out_eq' (g : G ⧸ N))]

theorem mem_cohomologyConjInvariants_iff (n : ℕ) (x : cohomology (Rep.res N.subtype A) n) :
    x ∈ cohomologyConjInvariants A N n ↔ x ∈ (cohomologyConjRep A N n).invariants := by
  refine ⟨fun hx q => ?_, fun hx g => ?_⟩
  · induction q using QuotientGroup.induction_on with
    | H g => rw [cohomologyConjRep_mk]; exact hx g
  · rw [← cohomologyConjRep_mk]
    exact hx _

end CompactSubgroup

section CompactGroup

variable [CompactSpace G]

set_option backward.isDefEq.respectTransparency false in
-- A coefficient map used at the types `Rep.res ↑(.id _) A` and `A`, definitionally but not
-- reducibly equal at Lean 4.35, has to be identified for `map_comp` to apply.
@[reassoc]
theorem cohomologyRes_comp_cohomologyConj (n : ℕ) (g : G) :
    res A N n ≫ cohomologyConj A N n g = res A N n := by
  conv_rhs => rw [← Category.id_comp (res A N n), ← cohomologyInnerConj_eq_id n A g]
  rw [res, cohomologyConj, cohomologyInnerConj, ← map_comp,
    ← map_comp]
  exact ProfiniteCohomology.map_congr _ _ (ContinuousMonoidHom.ext fun s => by simp) (fun a => rfl) n

theorem cohomologyRes_apply_mem_cohomologyConjInvariants (n : ℕ) (x : cohomology A n) :
    (res A N n).hom x ∈ cohomologyConjInvariants A N n := fun g => by
  rw [← ModuleCat.comp_apply, cohomologyRes_comp_cohomologyConj]

end CompactGroup

-- from Descent.lean
open CategoryTheory


section Nsmul

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem bijective_nsmul_cohomology (B : Rep.{u} k Γ) [IsSmoothRep B] (m : ℕ)
    (hB : Function.Bijective fun b : B => m • b) (n : ℕ) :
    Function.Bijective fun x : cohomology B n => m • x := by
  let L : B →ₗ[k] B := m • LinearMap.id
  let e : B ≃ₗ[k] B := LinearEquiv.ofBijective L hB
  have he : ∀ b : B, e b = m • b := fun _ => rfl
  let φ : B ⟶ B := Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext b
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [he, ← map_nsmul, ← he, LinearEquiv.apply_symm_apply]⟩
  have h1 : (m • 𝟙 B) ≫ φ = 𝟙 B := by
    ext b
    change e.symm (m • b) = b
    rw [← he, LinearEquiv.symm_apply_apply]
  have h2 : φ ≫ (m • 𝟙 B) = 𝟙 B := by
    ext b
    change m • e.symm b = b
    rw [← he, LinearEquiv.apply_symm_apply]
  have hf : (fun x : cohomology B n => m • x) = (coeffMap (m • 𝟙 B) n).hom := by
    funext x
    rw [cohomologyMap_nsmul_id_apply]
  rw [hf]
  refine Function.bijective_iff_has_inverse.2 ⟨(coeffMap φ n).hom, fun x => ?_, fun x => ?_⟩
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, h1, coeffMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, h2, coeffMap_id]
    rfl

end Nsmul

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) [(U : Subgroup G).Normal] (A : Rep.{u} k G)
  [IsSmoothRep A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section ResCores

noncomputable def coindTraceTermMor (c : G ⧸ (U : Subgroup G)) :
    Rep.res (U : Subgroup G).subtype
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) ⟶
      Rep.res (U : Subgroup G).subtype A :=
  Rep.ofHom ⟨coindTraceTerm (U : Subgroup G) A c, fun u => by
    ext f
    induction c using QuotientGroup.induction_on with
    | H x =>
      change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
          ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ u f) =
        A.ρ u (coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G)) f)
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ x (f.1 (x⁻¹ * u)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      have hv : x⁻¹ * (u : G) * x ∈ (U : Subgroup G) := by
        simpa using ‹(U : Subgroup G).Normal›.conj_mem _ u.2 x⁻¹
      have e : x⁻¹ * (u : G) = (U : Subgroup G).subtype ⟨_, hv⟩ * x⁻¹ := by
        simp only [Subgroup.subtype_apply]
        group
      rw [e, f.2 ⟨_, hv⟩ x⁻¹]
      change A.ρ x (A.ρ (x⁻¹ * u * x) (f.1 x⁻¹)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩

omit [IsSmoothRep A] in

theorem resFunctor_map_coindTrace :
    (Rep.resFunctor (U : Subgroup G).subtype).map (coindTrace (U : Subgroup G) A) =
      ∑ c : G ⧸ (U : Subgroup G), coindTraceTermMor U A c := by
  ext f
  change (coindTrace (U : Subgroup G) A).hom f = (∑ c, coindTraceTermMor U A c).hom f
  rw [coindTrace_hom_apply, Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  rfl

instance isSmoothRep_res_coind_res :
    IsSmoothRep (Rep.res (U : Subgroup G).subtype
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))) :=
  isSmoothRep_res_subtype _ _

instance isSmoothRep_resFunctor_obj_coind_res :
    IsSmoothRep ((Rep.resFunctor (U : Subgroup G).subtype).obj
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))) :=
  isSmoothRep_res_subtype _ _

set_option backward.isDefEq.respectTransparency false in
-- A coefficient map used at the types `Rep.res ↑(.id _) A` and `A`, definitionally but not
-- reducibly equal at Lean 4.35, has to be identified for `map_comp` to apply.
theorem cohomologyRes_comp_cohomologyMap_coindTraceTermMor (n : ℕ) (x : G) :
    res (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))
        (U : Subgroup G) n ≫ coeffMap (coindTraceTermMor U A (x : G ⧸ (U : Subgroup G))) n =
      shapiroMap U (Rep.res (U : Subgroup G).subtype A) n ≫ cohomologyConj A (U : Subgroup G) n x := by
  rw [coeffMap_eq]
  conv_lhs => rw [← Category.id_comp (res _ _ n), ← cohomologyInnerConj_eq_id n
    (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) x]
  rw [res, cohomologyInnerConj, shapiroMap, cohomologyConj, ← map_comp,
    ← map_comp, ← map_comp]
  refine ProfiniteCohomology.map_congr _ _ (ContinuousMonoidHom.ext fun s => rfl) (fun f => ?_) n
  change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
      ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ x f) =
    A.ρ x (f.1 1)
  rw [coindTraceTerm_apply]
  change A.ρ x (f.1 (x⁻¹ * x)) = A.ρ x (f.1 1)
  rw [inv_mul_cancel]

theorem cohomologyMap_sum {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {B C : Rep.{u} k Γ} [IsSmoothRep B] [IsSmoothRep C] {ι : Type*} (s : Finset ι)
    (f : ι → (B ⟶ C)) (n : ℕ) :
    coeffMap (∑ i ∈ s, f i) n = ∑ i ∈ s, coeffMap (f i) n := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

set_option backward.isDefEq.respectTransparency false in
-- A coefficient map used at the types `Rep.res ↑(.id _) A` and `A`, definitionally but not
-- reducibly equal at Lean 4.35, has to be identified for `map_comp` to apply.
theorem cohomologyCores_comp_cohomologyRes (n : ℕ) :
    cores U A n ≫ res A (U : Subgroup G) n =
      ∑ c : G ⧸ (U : Subgroup G), cohomologyConj A (U : Subgroup G) n c.out := by
  have hsum : map (ContinuousMonoidHom.id (U : Subgroup G))
      (∑ c : G ⧸ (U : Subgroup G), coindTraceTermMor U A c) n =
      ∑ c : G ⧸ (U : Subgroup G), coeffMap (coindTraceTermMor U A c) n :=
    cohomologyMap_sum _ _ n
  rw [cores, Category.assoc, res_naturality, resFunctor_map_coindTrace, hsum,
    Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [(QuotientGroup.out_eq' c).symm]
  rw [cohomologyRes_comp_cohomologyMap_coindTraceTermMor, IsIso.inv_hom_id_assoc]

theorem cohomologyRes_cohomologyCores_apply (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) n) :
    (res A (U : Subgroup G) n).hom ((cores U A n).hom x) =
      ∑ c : G ⧸ (U : Subgroup G), (cohomologyConj A (U : Subgroup G) n c.out).hom x := by
  have h := congrArg (fun f => f.hom x) (cohomologyCores_comp_cohomologyRes U A n)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.comp_apply, LinearMap.sum_apply]
    using h

end ResCores

section Descent

variable (hA : Function.Bijective fun a : A => (U : Subgroup G).index • a)
include hA

omit [(U : Subgroup G).Normal] in

theorem cohomologyRes_injective_of_bijective (n : ℕ) :
    Function.Injective (res A (U : Subgroup G) n).hom := by
  intro x y h
  have hc : ∀ z : cohomology A n, (cores U A n).hom ((res A (U : Subgroup G) n).hom z) =
      (U : Subgroup G).index • z := fun z => by
    rw [← ModuleCat.comp_apply, res_comp_cores]
    rfl
  apply (bijective_nsmul_cohomology A _ hA n).1
  change (U : Subgroup G).index • x = (U : Subgroup G).index • y
  rw [← hc, ← hc, h]

theorem range_cohomologyRes_of_bijective (n : ℕ) :
    LinearMap.range (res A (U : Subgroup G) n).hom =
      cohomologyConjInvariants A (U : Subgroup G) n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact cohomologyRes_apply_mem_cohomologyConjInvariants A _ n z
  · intro x hx
    have hAU : Function.Bijective fun a : Rep.res (U : Subgroup G).subtype A =>
        (U : Subgroup G).index • a := hA
    have hbij := bijective_nsmul_cohomology (Rep.res (U : Subgroup G).subtype A) _ hAU n
    obtain ⟨x', hx'⟩ := hbij.2 x
    simp only at hx'
    have hinv : ∀ g : G, (cohomologyConj A (U : Subgroup G) n g).hom x' = x' := fun g => by
      apply hbij.1
      simp only
      rw [← map_nsmul, hx']
      exact hx g
    refine ⟨(cores U A n).hom x', ?_⟩
    rw [cohomologyRes_cohomologyCores_apply]
    simp only [hinv, Finset.sum_const, Finset.card_univ]
    rw [← hx', Subgroup.index_eq_card, Nat.card_eq_fintype_card]

noncomputable def coprimeDescentEquiv (n : ℕ) :
    cohomology A n ≃ₗ[k] cohomologyConjInvariants A (U : Subgroup G) n :=
  LinearEquiv.ofBijective
    ((res A (U : Subgroup G) n).hom.codRestrict _
      (cohomologyRes_apply_mem_cohomologyConjInvariants A _ n))
    ⟨fun x y h => cohomologyRes_injective_of_bijective U A hA n (congrArg Subtype.val h),
      fun x => by
        obtain ⟨z, hz⟩ := (range_cohomologyRes_of_bijective U A hA n).ge x.2
        exact ⟨z, Subtype.ext hz⟩⟩

end Descent

end Langlands.ProfiniteCohomology
