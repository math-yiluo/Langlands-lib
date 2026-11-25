import Langlands.GaloisCohomology.CompactSupport.OpenSubgroupCup
import Langlands.Cohomology.Profinite.Duality.Main

/-!
# The duality theorem for cohomology with compact support

Dévissage: under `CompactGroupDualityHypotheses` (`D ≅ ℤ/n`, `H_c^4 = 0` for modules killed by `n`,
duality for the modules coinduced from `ℤ/n` on open subgroups below `U₀`) the duality map
`Hʳ(G, Hom(M, D)) → Hom(H_c^s(G, M), ℤ/n)` (`r + s = 3`) is bijective for every finite smooth
module `M` killed by `n` (`CompactGroupDualityHypotheses.bijective_compactDualityMap`), by
induction on the degree through the long exact sequences of an embedding of `M` into a sum of
coinduced modules. With Shapiro's lemma and corestriction the coinduced case reduces to `ℤ/n` over
open subgroups, which gives the theorem from `CompactDualityHypotheses`
(`CompactDualityHypotheses.bijective_compactDualityMap`).
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from PoincarePairs/Devissage.lean
section Devissage

noncomputable section


open CategoryTheory MonoidalCategory Limits


attribute [local instance 2000] Rep.hV2

section Sequence

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃]

omit [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] in

instance isSmoothRep_map_resFunctor_X₁ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsSmoothRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₁ :=
  IsSmoothRep.res (continuous_toMonoidHom ψ) _

omit [IsSmoothRep S.X₁] [IsSmoothRep S.X₃] in
instance isSmoothRep_map_resFunctor_X₂ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsSmoothRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₂ :=
  IsSmoothRep.res (continuous_toMonoidHom ψ) _

omit [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] in
instance isSmoothRep_map_resFunctor_X₃ {K : Type u} [Group K] [TopologicalSpace K]
    (ψ : K →ₜ* G) :
    IsSmoothRep (S.map (Rep.resFunctor ψ.toMonoidHom)).X₃ :=
  IsSmoothRep.res (continuous_toMonoidHom ψ) _

/-- The connecting map of cohomology with compact support (local modules the restrictions) for a
short exact sequence of `G`-modules. -/
noncomputable def compactSupportδRes (hS : S.ShortExact) (n : ℕ) :
    compactSupportCohomologyRes φ S.X₃ n ⟶ compactSupportCohomologyRes φ S.X₁ (n + 1) :=
  compactSupportδ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G))) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS) n

variable (hS : S.ShortExact)

include hS in

theorem compactRes_exact₂ (n : ℕ) :
    (ShortComplex.mk (compactSupportCohomologyResMap φ S.f n) (compactSupportCohomologyResMap φ S.g n)
      (by rw [← compactSupportCohomologyResMap_comp, S.zero, compactSupportCohomologyResMap_zero])).Exact :=
  compactSupportCohomology_exact₂ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G)))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS) n

theorem compactRes_exact₃ (n : ℕ) :
    (ShortComplex.mk (compactSupportCohomologyResMap φ S.g n) (compactSupportδRes φ hS n)
      ((compactSupportCochains_shortExact φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G)))
        (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS)).comp_δ n
          (n + 1) rfl)).Exact :=
  compactSupportCohomology_exact₃ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G)))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS) n

theorem compactRes_exact₁ (n : ℕ) :
    (ShortComplex.mk (compactSupportδRes φ hS n) (compactSupportCohomologyResMap φ S.f (n + 1))
      ((compactSupportCochains_shortExact φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G)))
        (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS)).δ_comp n
          (n + 1) rfl)).Exact :=
  compactSupportCohomology_exact₁ φ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : Hv v →* G)))
    (fun _ => 𝟙 _) hS (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hS) n

end Sequence

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (D : Rep.{u} (ULift.{u} ℤ) G)
  [IsSmoothRep D] {N : ℕ}

theorem eq_zero_of_neg_neg_one_pow_zsmul {A : Type*} [AddCommGroup A] (s : ℕ) {a : A}
    (ha : (-(-1 : ℤ) ^ s) • a = 0) : a = 0 := by
  rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] at ha <;> simpa using ha

theorem neg_neg_one_pow_zsmul_zsmul {A : Type*} [AddCommGroup A] (s : ℕ) (a : A) :
    (-(-1 : ℤ) ^ s) • ((-(-1 : ℤ) ^ s) • a) = a := by
  rcases neg_one_pow_eq_or ℤ s with h | h <;> rw [h] <;> simp

theorem map_eq_of_add_neg_one_pow_smul_eq_zero {R Z A : Type*} [Ring R] [AddCommGroup Z]
    [Module R Z] [AddCommGroup A] (t : Z →+ A) (s : ℕ) {a b : Z}
    (h : a + (-1 : R) ^ s • b = 0) : t b = (-(-1 : ℤ) ^ s) • t a := by
  have e : (-1 : R) ^ s • b = ((-1 : ℤ) ^ s) • b := by
    rw [← Int.cast_smul_eq_zsmul R]
    push_cast
    rfl
  rw [e] at h
  rcases neg_one_pow_eq_or ℤ s with e | e <;> rw [e] at h ⊢
  · rw [one_smul] at h
    rw [eq_neg_of_add_eq_zero_right h, map_neg, neg_smul, one_smul]
  · rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    rw [← h, neg_neg, one_smul]

variable {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]

theorem compactDualityMap_δ {n : ℕ} (t : compactSupportCohomologyRes φ D (n + 1) →+ ZMod N) (hS : S.ShortExact)
    (hT : (dualShortComplex D S).ShortExact) {r s : ℕ} (h₁ : r + 1 + s = n + 1)
    (h₀ : r + (s + 1) = n + 1) (q : cohomology S.X₃ r)
    (y : compactSupportCohomologyRes φ (dualRep D S.X₁) s) :
    compactDualityMap φ D h₁ t S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      (-(-1 : ℤ) ^ s) • compactDualityMap φ D h₀ t S.X₃ q ((compactSupportδRes φ hT s).hom y) := by
  have key := compactCup_compactSupportδ_add_compactCup_δ φ
    (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v : Hv v →* G)))
    (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v : Hv v →* G) D) (c := fun _ => 𝟙 _)
    (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X₁)
    (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map (dualEvalPairing D S.X₃))
    (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map (dualEvalPairing D S.X₂))
    (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map (dualEvalPairing D S.X₁))
    (fun v => resFunctor_map_comp_id (φ v : Hv v →* G) _)
    (fun v => resFunctor_map_comp_id (φ v : Hv v →* G) _)
    (fun v => resFunctor_map_comp_id (φ v : Hv v →* G) _)
    (tensorHom_dualEvalPairing D S.g) (tensorHom_dualEvalPairing D S.f).symm
    (fun v => resFunctor_map_naturality (φ v : Hv v →* G) _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun v => (resFunctor_map_naturality (φ v : Hv v →* G) _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    hT (fun v => (Rep.shortExact_res (φ v : Hv v →* G)).2 hT) hS
    (show s + 1 + r = n + 1 by omega) (show s + (r + 1) = n + 1 by omega) y q
  rw [compactDualityMap_apply, compactDualityMap_apply]
  exact map_eq_of_add_neg_one_pow_smul_eq_zero t s key

end Sign

section Embedding

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}

theorem exists_injective_biproduct_coind_le [NeZero n] (U₀ : OpenSubgroup Γ)
    (M : Rep.{u} (ULift.{u} ℤ) Γ) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    ∃ (W : OpenSubgroup Γ) (_ : W ≤ U₀) (J : Type) (_ : Fintype J)
      (i : M ⟶ ⨁ fun _ : J => Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)),
      Function.Injective i.hom := by
  let W := fixingOpenSubgroup M ⊓ U₀
  have hW : ∀ w ∈ (W : Subgroup Γ), ∀ m : M, M.ρ w m = m :=
    fun w hw m => fixingOpenSubgroup_apply M
      ((inf_le_left : fixingOpenSubgroup M ⊓ U₀ ≤ fixingOpenSubgroup M) hw) m
  let e := (Finite.equivFin (M →+ ZMod n)).symm
  let F : ∀ _ : Fin (Nat.card (M →+ ZMod n)),
      M ⟶ Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n) :=
    fun j => Rep.resCoindToHom (W : Subgroup Γ).subtype M _ (charHom (W : Subgroup Γ) M hW (e j))
  refine ⟨W, inf_le_right, Fin (Nat.card (M →+ ZMod n)), inferInstance, biproduct.lift F, ?_⟩
  intro a b hab
  by_contra hne
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hM (sub_ne_zero.2 hne)
  apply hχ
  have hj := congrArg (biproduct.π (fun _ : Fin (Nat.card (M →+ ZMod n)) =>
    Rep.coind (W : Subgroup Γ).subtype (zmodRep.{u} (W : Subgroup Γ) n)) (e.symm χ)).hom hab
  change (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom a =
    (biproduct.lift F ≫ biproduct.π _ (e.symm χ)).hom b at hj
  rw [biproduct.lift_π] at hj
  have h1 := congrArg (fun f => ULift.down (f.1 1 : ULift.{u} (ZMod n))) hj
  simp only [F, Rep.resCoindToHom_hom_apply_coe, map_one, Module.End.one_apply,
    Equiv.apply_symm_apply] at h1
  rw [charHom_hom_apply, charHom_hom_apply] at h1
  change χ a = χ b at h1
  rw [map_sub, h1, sub_self]

end Embedding

section Core

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- The hypotheses of the dévissage: `D ≅ ℤ/n`, `H_c^4` vanishes for modules killed by `n`, and
the duality map is bijective for the modules coinduced from `ℤ/n` on open subgroups below `U₀`. -/
structure CompactGroupDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep D] (t : compactSupportCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- `H_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactSupportCohomologyRes φ M 4)
  /-- The duality map is bijective for the modules coinduced from `ℤ/n` on open subgroups below `U₀`. -/
  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (compactDualityMap φ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))

namespace CompactGroupDualityHypotheses

variable {φ} {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : compactSupportCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}
  (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in
theorem finite_D : Finite D :=
  finite_of_nonempty_addEquiv H.nonempty_addEquiv

include H in
theorem nsmul_D (d : D) : n • d = 0 :=
  nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv d

include H in

theorem exists_devissage (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    ∃ (I Q : Rep.{u} (ULift.{u} ℤ) G) (_ : IsSmoothRep I) (_ : IsSmoothRep Q) (_ : Finite I)
      (_ : Finite Q) (i : M ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧ (∀ x : I, n • x = 0) ∧ (∀ x : Q, n • x = 0) ∧
      ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactDualityMap φ D h t I) := by
  obtain ⟨W, hW, J, _, i, hi⟩ := exists_injective_biproduct_coind_le (n := n) U₀ M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective (compactDualityMap φ D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) :
        Rep.{u} (ULift.{u} ℤ) G)) :=
    fun h => bijective_compactDualityMap_biproduct φ D h t _ fun _ => H.bijective_coind W hW h
  have hnI : ∀ x : ((⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype
      (zmodRep.{u} (W : Subgroup G) n) : Rep.{u} (ULift.{u} ℤ) G) : Type u), n • x = 0 := by
    intro x
    rw [biproduct_eq_sum _ x, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← map_nsmul, nsmul_coind_zmodRep_eq_zero W, map_zero]
  have hmono : Mono i := (Rep.mono_iff_injective i).2 hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (S.exact_of_g_is_cokernel (cokernelIsCokernel i)) hmono
      (inferInstance : Epi (cokernel.π i))
  have hQd : IsSmoothRep (cokernel i) := isSmoothRep_X₃_of_shortExact hS
  have hsurj : Function.Surjective (cokernel.π i).hom :=
    (Rep.epi_iff_surjective _).1 inferInstance
  have hQf : Finite ((cokernel i : Rep.{u} (ULift.{u} ℤ) G) : Type u) :=
    Finite.of_surjective _ hsurj
  refine ⟨_, cokernel i, inferInstance, hQd, inferInstance, hQf, i, cokernel.π i,
    cokernel.condition i, hS, hnI, fun x => ?_, hφ⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [← map_nsmul, hnI, map_zero]

end CompactGroupDualityHypotheses

end Core

section Steps

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : compactSupportCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactGroupDualityHypotheses

variable (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in

theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((coeffMap i 0).hom x) = 0 := by
    ext y
    rw [compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i x y, hx]
    rfl
  have h2 : (coeffMap i 0).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI (rfl : 0 + 3 = 3)).1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (compactSupportCohomologyResMap φ (dualMap D i) 3).hom := by
    intro y
    have : Subsingleton (compactSupportCohomologyRes φ (dualRep D Q) 4) :=
      H.subsingleton_four (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT 3) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := (hI (rfl : 0 + 3 = 3)).2
    (l.comp (compactSupportCohomologyResMap φ (dualMap D i) 3).hom.toAddMonoidHom)
  have hpv : (coeffMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t p v y, hv]
    change l ((compactSupportCohomologyResMap φ (dualMap D p) 3 ≫
      compactSupportCohomologyResMap φ (dualMap D i) 3).hom y) = 0
    rw [← compactSupportCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      compactSupportCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← compactDualityMap_cohomologyMap φ D (rfl : 0 + 3 = 3) t i m z]
  change compactDualityMap φ D (rfl : 0 + 3 = 3) t I ((coeffMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (compactDualityMap φ D (rfl : 0 + 3 = 3) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

variable {r s : ℕ} (h₁ : r + 1 + s = 3) (h₀ : r + (s + 1) = 3)

include H in

theorem injective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Injective (compactDualityMap φ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : compactDualityMap φ D h₁ t I ((coeffMap i (r + 1)).hom x) = 0 := by
    ext y
    rw [compactDualityMap_cohomologyMap φ D h₁ t i x y, hx]
    rfl
  have hix : (coeffMap i (r + 1)).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI h₁).1 _ h1
  obtain ⟨q, hq⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix
  have hker : ((compactSupportCohomologyResMap φ (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤
      (compactDualityMap φ D h₀ t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₁ φ hT s) z hz
    rw [AddMonoidHom.mem_ker, ← hy]
    have e := compactDualityMap_δ φ D t hS hT h₁ h₀ q y
    change compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
    rw [hq, hx, AddMonoidHom.zero_apply] at e
    exact eq_zero_of_neg_neg_one_pow_zsmul s e.symm
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_compactSupportCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨v, hv⟩ := (ih I hnI).2 ψ
  have hpv : (coeffMap p r).hom v = q := by
    apply (ih Q hnQ).1
    ext z
    rw [compactDualityMap_cohomologyMap φ D h₀ t p v z, hv, ← hψ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)

include H in

theorem surjective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (compactDualityMap φ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := (hI h₁).2 (l.comp (compactSupportCohomologyResMap φ (dualMap D i) s).hom.toAddMonoidHom)
  have hpv : (coeffMap p (r + 1)).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_succ h₁ h₀ ih Q hnQ)
    ext y
    rw [compactDualityMap_cohomologyMap φ D h₁ t p v y, hv]
    change l ((compactSupportCohomologyResMap φ (dualMap D p) s ≫
      compactSupportCohomologyResMap φ (dualMap D i) s).hom y) = 0
    rw [← compactSupportCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      compactSupportCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv
  set ν := l - compactDualityMap φ D h₁ t M x' with hν
  have hker : ((compactSupportδRes φ hT s).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (compactRes_exact₃ φ hT s) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((compactSupportCohomologyResMap φ (dualMap D i) s).hom z) =
      compactDualityMap φ D h₁ t M x' ((compactSupportCohomologyResMap φ (dualMap D i) s).hom z)
    rw [← compactDualityMap_cohomologyMap φ D h₁ t i x' z]
    change _ = compactDualityMap φ D h₁ t I ((coeffMap S.f (r + 1)).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨ψ, hψ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_compactSupportCohomologyRes_eq_zero φ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨q, hq⟩ := (ih Q hnQ).2 ψ
  refine ⟨x' + (-(-1 : ℤ) ^ s) • (δ hS r (r + 1) rfl).hom q, ?_⟩
  ext y
  have e := compactDualityMap_δ φ D t hS hT h₁ h₀ q y
  change compactDualityMap φ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
  have hψy : ψ ((compactSupportδRes φ hT s).hom y) = ν y := congrArg (fun f => f y) hψ
  rw [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq,
    neg_neg_one_pow_zsmul_zsmul]
  change _ + ψ ((compactSupportδRes φ hT s).hom y) = l y
  rw [hψy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H in
theorem bijective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (compactDualityMap φ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (compactDualityMap φ D h₁ t M) :=
  ⟨H.injective_succ h₁ h₀ ih M hM, H.surjective_succ h₁ h₀ ih M hM⟩

end CompactGroupDualityHypotheses

end Steps

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : compactSupportCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactGroupDualityHypotheses

variable (H : CompactGroupDualityHypotheses φ n D t U₀)

include H in

theorem bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M) := by
  have b0 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_zero M hM
  have b1 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 0) (s := 2) rfl rfl b0 M hM
  have b2 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 1) (s := 1) rfl rfl b1 M hM
  have b3 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_succ (r := 2) (s := 0) rfl rfl b2 M hM
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 3) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) ∨ (r = 3 ∧ s = 0) := by omega
  · exact b0 M hM
  · exact b1 M hM
  · exact b2 M hM
  · exact b3 M hM

end CompactGroupDualityHypotheses

end Main

end

end Devissage

-- from PoincarePairs.lean
section PoincarePairs

noncomputable section


open CategoryTheory MonoidalCategory


attribute [local instance 2000] Rep.hV2

section Natural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem LeibnizPairing.homologyMap_homology {M N P P' : CochainComplex (ModuleCat.{u} k) ℕ}
    (μ₁ : LeibnizPairing M N P) (μ₂ : LeibnizPairing M N P') (ψ : P ⟶ P')
    (hψ : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N.X s),
      (ψ.f n).hom (μ₁.μ h x y) = μ₂.μ h x y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N.homology s) :
    (HomologicalComplex.homologyMap ψ n).hom (μ₁.homology h x y) = μ₂.homology h x y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply,
    LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles]
  exact hψ h _ _

variable {A B C C' : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]
  [IsSmoothRep C']

theorem compactSupportCohomologyResMap_compactCupRes (μ : A ⊗ B ⟶ C) (ψ : C ⟶ C') {r s n : ℕ}
    (h : r + s = n) (y : compactSupportCohomologyRes φ A r) (x : cohomology B s) :
    (compactSupportCohomologyResMap φ ψ n).hom (compactCupRes φ μ h y x) =
      compactCupRes φ (μ ≫ ψ) h y x := by
  rw [compactCupRes_eq_homology, compactCupRes_eq_homology]
  refine LeibnizPairing.homologyMap_homology _ _ _ (fun {r s n} h p z => ?_) h y x
  revert p
  intro (p : (cochains A).X r ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A)) r)
  refine Prod.ext rfl ?_
  cases r with
  | zero =>
    exact map_zero (shiftNegOneMapF (piMap fun v => coeffCochainsMap
      ((Rep.resFunctor (φ v : Hv v →* G)).map ψ)) n).hom
  | succ r =>
    cases n with
    | zero => rfl
    | succ n => rfl

theorem bijective_compactSupportCohomologyResMap_of_comp_eq_id (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (hgf : g ≫ f = 𝟙 B) (m : ℕ) :
    Function.Bijective (compactSupportCohomologyResMap φ f m) := by
  refine Function.bijective_iff_has_inverse.2 ⟨compactSupportCohomologyResMap φ g m, fun x => ?_,
    fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← compactSupportCohomologyResMap_comp, hfg,
      compactSupportCohomologyResMap_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← compactSupportCohomologyResMap_comp, hgf,
      compactSupportCohomologyResMap_id]
    rfl

end Natural

section Bridge

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem compactCores_mackeyCompactCohomologyIso {k : Type u} [CommRing k] (V : OpenSubgroup G)
    (A : Rep.{u} k G) [IsSmoothRep A] (m : ℕ)
    (w : compactSupportCohomologyRes φ (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A)) m) :
    (compactCores φ V A m).hom
        ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom.hom w) =
      (compactSupportCohomologyResMap φ (coindTrace (V : Subgroup G) A) m).hom w := by
  change (compactSupportCohomologyResMap φ (coindTrace (V : Subgroup G) A) m).hom
    ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).inv.hom
      ((mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom.hom w)) = _
  rw [hom_apply_hom_apply_of_comp_eq
    (mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) m).hom_inv_id w]
  rfl

variable {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]

omit [NeZero n] [IsSmoothRep D] in

theorem tensorHom_coindDualHom_dualEvalPairing (U : OpenSubgroup G) :
    (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D ⊗ₘ
        𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) =
    coindPairing (U : Subgroup G)
        (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) ≫
      coindTrace (U : Subgroup G) D := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  induction z using TensorProduct.inductionOn with
  | tmul μ f => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

omit [NeZero n] in

theorem tensorHom_zmodDualIso_zmodMulPairingRight {K : Type u} [Group K]
    (E : Rep.{u} (ULift.{u} ℤ) K) (hE : ∀ d : E, n • d = 0) :
    ((zmodDualIso n E hE).hom ⊗ₘ 𝟙 (zmodRep.{u} K n)) ≫ zmodMulPairingRight n E hE =
      dualEvalPairing E (zmodRep.{u} K n) := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
  induction z using TensorProduct.inductionOn with
  | tmul ν a =>
    obtain ⟨a⟩ := a
    change zmodMulAddHom n hE a (ν (ULift.up 1)) = ν (ULift.up a)
    rw [zmodMulAddHom_apply]
    exact (dualRep_zmodRep_apply n E ν a).symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

variable {D}

/-- For `M = Coind_U^G(ℤ/n)`, the identification of `H_c^s(G, Hom(M, D))` with `H_c^s(U, D)`
composed with the duality map of `U`. -/
def coindDualCompactMap (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) (s : ℕ) :
    compactSupportCohomologyRes φ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) s →+
      compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s :=
  ((compactSupportCohomologyResMap (mackeyFamily U φ)
      (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom s).hom.comp
    (((mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom).comp
      (compactSupportCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom)).toAddMonoidHom

theorem bijective_coindDualCompactMap (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) (s : ℕ) :
    Function.Bijective (coindDualCompactMap φ hD U s) := by
  have h1 := bijective_compactSupportCohomologyResMap_of_comp_eq_id (mackeyFamily U φ)
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).inv (Iso.hom_inv_id _)
    (Iso.inv_hom_id _) s
  have h2 : Function.Bijective (mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom :=
    Function.bijective_iff_has_inverse.2 ⟨(mackeyCompactCohomologyIso U φ _ s).inv.hom,
      fun w => hom_apply_hom_apply_of_comp_eq (mackeyCompactCohomologyIso U φ _ s).hom_inv_id w,
      fun w => hom_apply_hom_apply_of_comp_eq (mackeyCompactCohomologyIso U φ _ s).inv_hom_id w⟩
  have h3 := bijective_compactSupportCohomologyResMap_of_comp_eq_id φ
    (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D)
    (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D)
    (coindDualInv_comp_coindDualHom _ _ _) (coindDualHom_comp_coindDualInv _ _ _) s
  exact h1.comp (h2.comp h3)

theorem compactDualityMap_coind (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G)
    (t : compactSupportCohomologyRes φ D 3 →+ ZMod n) {r s : ℕ} (h : r + s = 3)
    (x : cohomology (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) r)
    (y : compactSupportCohomologyRes φ
      (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) s) :
    compactDualityMap φ D h t
        (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)) x y =
      zmodCompactDualityMap φ D hD U h t ((shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r).hom x)
        (coindDualCompactMap φ hD U s y) := by
  have hy : (compactSupportCohomologyResMap φ (coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom
      ((compactSupportCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom y) =
        y := by
    rw [← ConcreteCategory.comp_apply, ← compactSupportCohomologyResMap_comp,
      coindDualInv_comp_coindDualHom, compactSupportCohomologyResMap_id]
    rfl
  rw [compactDualityMap_apply, zmodCompactDualityMap_apply]
  conv_lhs => rw [← hy]
  rw [compactCupRes_compactSupportCohomologyResMap φ _
    ((coindDualHom (U : Subgroup G) (ULift.{u} (ZMod n)) D ⊗ₘ
      𝟙 (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) ≫
      dualEvalPairing D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))
    _ (𝟙 _) (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]), coeffMap_id,
    tensorHom_coindDualHom_dualEvalPairing, ← compactSupportCohomologyResMap_compactCupRes,
    ← compactCores_mackeyCompactCohomologyIso, mackeyCompactCohomologyIso_compactCupRes]
  congr 2
  rw [ModuleCat.hom_id, LinearMap.id_apply]
  have e := compactCupRes_compactSupportCohomologyResMap (mackeyFamily U φ)
    (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
    (dualEvalPairing (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n))
    (zmodDualIso n (Rep.res (U : Subgroup G).subtype D) hD).hom (𝟙 _)
    (by rw [tensorHom_zmodDualIso_zmodMulPairingRight, MonoidalCategory.id_tensorHom_id,
      Category.id_comp]) ((Nat.add_comm s r).trans h)
    ((mackeyCompactCohomologyIso U φ
      (dualRep (Rep.res (U : Subgroup G).subtype D) (zmodRep.{u} (U : Subgroup G) n)) s).hom.hom
      ((compactSupportCohomologyResMap φ (coindDualInv (U : Subgroup G) (ULift.{u} (ZMod n)) D) s).hom y))
    ((shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r).hom x)
  rw [coeffMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e
  exact e.symm

end Bridge

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : compactSupportCohomologyRes φ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace CompactDualityHypotheses

variable (H : CompactDualityHypotheses φ n D t U₀)

include H in

theorem bijective_compactDualityMap_coind (U : OpenSubgroup G) (hU : U ≤ U₀) {r s : ℕ}
    (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) := by
  have hD := nsmul_eq_zero_of_nonempty_addEquiv H.nonempty_addEquiv
  have hsh : Function.Bijective (shapiroMap U (zmodRep.{u} (U : Subgroup G) n) r) :=
    Function.bijective_iff_has_inverse.2 ⟨inv (shapiroMap U _ r), inv_shapiroMap_apply U r,
      shapiroMap_inv_apply U r⟩
  exact bijective_of_bijective_comp (H.bijective_base U hU h) hsh
    (bijective_coindDualCompactMap φ hD U s) (compactDualityMap_coind φ hD U t h)

include H in

theorem compactGroupDualityHypotheses : CompactGroupDualityHypotheses φ n D t U₀ where
  nonempty_addEquiv := H.nonempty_addEquiv
  subsingleton_four := H.subsingleton_four
  bijective_coind U hU _ _ h := H.bijective_compactDualityMap_coind U hU h

include H in

theorem bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M) :=
  H.compactGroupDualityHypotheses.bijective_compactDualityMap M hM h

end CompactDualityHypotheses

end Main

end

end PoincarePairs

end Langlands.GaloisCohomology
