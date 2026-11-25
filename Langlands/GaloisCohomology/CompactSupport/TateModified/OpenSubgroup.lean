import Langlands.GaloisCohomology.CompactSupport.TateModified.Basic
import Langlands.GaloisCohomology.CompactSupport.DualityMap
import Langlands.Cohomology.Profinite.Coinduced.Acyclic

/-!
# Tate-modified compact support and open subgroups

Forgetting the finite groups gives `Ĥ_c^n(G, A) → H_c^n(G, A)` (`tateForget`), an isomorphism when
the local modules at the `F_w` are cohomologically trivial with invariants the norms
(`tateForgetIso`). For an open subgroup `U` meeting the conjugates of the `F_w` trivially
(`FreeOnCosets`) the coinduced modules have no cohomology at the `F_w`, which gives
`Ĥ_c^{n+1}(G, Coind_U^G N) ≅ H_c^{n+1}(U, N)` (`tateCoindIso`) and the corestriction
`tateCompactCores`.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from RealPlaces/InducedDefs.lean
section InducedDefs

open CategoryTheory Limits


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w)

/-- The map from Tate-modified to ordinary compactly supported cochains (forgetting the finite
groups). -/
noncomputable def tateForgetCochains :
    tateCompactCochains φ ψ A Aᵥ a Aᵣ ar ⟶ compactSupportCochains φ A Aᵥ a :=
  mappingCoconeNat.map (prodFst _ _) (prodFst _ _) (tateCompactRes_prodFst φ ψ A Aᵥ a Aᵣ ar)

/-- The map `Ĥ_c^n(G, A) → H_c^n(G, A)` forgetting the finite groups. -/
noncomputable def tateForget (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ compactSupportCohomology φ A Aᵥ a n :=
  HomologicalComplex.homologyMap (tateForgetCochains φ ψ A Aᵥ a Aᵣ ar) n

@[reassoc (attr := simp)]
theorem tateForget_compactToGlobal (n : ℕ) :
    tateForget φ ψ A Aᵥ a Aᵣ ar n ≫ compactToGlobal φ A Aᵥ a n = tateToGlobal φ ψ A Aᵥ a Aᵣ ar n := by
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n) (mappingCoconeNat.map_fst _ _ _))

/-- The projection of the local terms onto those of the first family. -/
noncomputable def tateLocalFst (n : ℕ) :
    ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) ⟶
      ModuleCat.of k (∀ v, cohomology (Aᵥ v) n) :=
  ModuleCat.ofHom (LinearMap.fst k _ _)

omit [∀ w, Fintype (F w)] in
theorem tateLocalCohomologyIso_inv_homologyMap_prodFst (n : ℕ) :
    (tateLocalCohomologyIso Aᵥ Aᵣ n).inv ≫ HomologicalComplex.homologyMap (prodFst _ _) n =
      tateLocalFst Aᵥ Aᵣ n ≫ (localCohomologyIso Aᵥ n).inv := by
  refine ModuleCat.hom_ext (LinearMap.ext fun p => ?_)
  have hp := hom_apply_hom_apply_of_comp_eq (Iso.inv_hom_id (tateLocalCohomologyIso Aᵥ Aᵣ n)) p
  rw [tateLocalCohomologyIso_hom_apply] at hp
  have h1 := congrArg Prod.fst hp
  change (localCohomologyIso Aᵥ n).hom.hom _ = p.1 at h1
  change (HomologicalComplex.homologyMap (prodFst _ _) n).hom
      ((tateLocalCohomologyIso Aᵥ Aᵣ n).inv.hom p) = (localCohomologyIso Aᵥ n).inv.hom p.1
  rw [← h1]
  exact (hom_apply_hom_apply_of_comp_eq (Iso.hom_inv_id (localCohomologyIso Aᵥ n)) _).symm

@[reassoc]
theorem tateLocalToCompact_tateForget (n : ℕ) :
    tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar n ≫ tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1) =
      tateLocalFst Aᵥ Aᵣ n ≫ localToCompact φ A Aᵥ a n := by
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (mappingCoconeNat.homologyδ_naturality _ _ _ n)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (tateLocalCohomologyIso_inv_homologyMap_prodFst Aᵥ Aᵣ n)).trans
        (Category.assoc _ _ _))))

end InducedDefs

-- from RealPlaces/InducedDropOut.lean
section InducedDropOut

open CategoryTheory Limits


section ProdSeq

variable {k : Type u} [CommRing k] (M N : CochainComplex (ModuleCat.{u} k) ℕ)

/-- The inclusion of the second factor of a product complex. -/
noncomputable def prodInr : N ⟶ prodComplex M N :=
  prodLift 0 (𝟙 N)

theorem prodInr_f_hom_apply (n : ℕ) (y : N.X n) :
    ((prodInr M N).f n).hom y = ((0 : M.X n), y) :=
  rfl

/-- The split short exact sequence `N → M × N → M`. -/
noncomputable def prodSeq : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (prodInr M N) (prodFst M N)
    (HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

theorem prodSeq_shortExact : (prodSeq M N).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : M.X n × N.X n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : M.X n) =>
      ⟨((x, 0) : M.X n × N.X n), rfl⟩ }

end ProdSeq

section NormClass

variable {k F' : Type u} [CommRing k] [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
  [Fintype F'] (B : Rep.{u} k F') [IsSmoothRep B]

theorem exists_normClass_eq (hB : ∀ x ∈ B.ρ.invariants, ∃ m, B.ρ.norm m = x) (c : cohomology B 0) :
    ∃ m, normClass B m = c := by
  obtain ⟨z, rfl⟩ := homologyπ_hom_surjective (cochains B) 0 c
  obtain ⟨v, hx⟩ : ∃ v, ((cochains B).iCycles 0).hom z = zeroCochain B v := by
    refine ⟨cochainOf B (((cochains B).iCycles 0).hom z) Fin.elim0, ?_⟩
    apply cochainOf_injective
    funext σ
    rw [cochainOf_zeroCochain, Subsingleton.elim σ Fin.elim0]
  have hd : ((cochains B).d 0 1).hom (zeroCochain B v) = 0 := by
    rw [← hx]
    exact (hom_apply_hom_apply_of_comp_eq ((cochains B).iCycles_d 0 1) z).trans rfl
  have hinv : v ∈ B.ρ.invariants := fun g => by
    have h := congrFun (congrArg (cochainOf B) hd) (fun _ => g)
    rw [cochainOf_d_zeroCochain, cochainOf_zero] at h
    exact sub_eq_zero.1 h
  obtain ⟨m, hm⟩ := hB v hinv
  refine ⟨m, ?_⟩
  unfold normClass
  congr 1
  apply iCycles_hom_injective
  exact (((cochains B).i_cyclesMk _ _ _ _).trans (congrArg (zeroCochain B) hm)).trans hx.symm

end NormClass

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w)

theorem normCochains_prodInr :
    normCochains Aᵣ ≫ prodInr _ _ = prodInr _ _ ≫ tateCompactRes φ ψ A Aᵥ a Aᵣ ar := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((prodInr _ _).f n).hom (((normCochains Aᵣ).f n).hom m) =
    ((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f n).hom (((prodInr _ _).f n).hom m)
  rw [prodInr_f_hom_apply, prodInr_f_hom_apply]
  refine Prod.ext ?_ ?_
  · change (0 : (piComplex fun v => cochains (Aᵥ v)).X n) = ((localRes φ A Aᵥ a).f n).hom 0
    exact (map_zero _).symm
  · change ((normCochains Aᵣ).f n).hom m =
      ((localRes ψ A Aᵣ ar).f n).hom 0 + ((normCochains Aᵣ).f n).hom m
    rw [map_zero, zero_add]

/-- The morphism of short exact sequences comparing the Tate-modified and the ordinary cocone. -/
noncomputable def tateResSeqHom :
    prodSeq (cochains A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))) ⟶
      prodSeq (piComplex fun v => cochains (Aᵥ v)) (piComplex fun w => cochains (Aᵣ w)) where
  τ₁ := normCochains Aᵣ
  τ₂ := tateCompactRes φ ψ A Aᵥ a Aᵣ ar
  τ₃ := localRes φ A Aᵥ a
  comm₁₂ := normCochains_prodInr φ ψ A Aᵥ a Aᵣ ar
  comm₂₃ := tateCompactRes_prodFst φ ψ A Aᵥ a Aᵣ ar

theorem tateForgetShortComplex_shortExact :
    (mappingCoconeNat.mapShortComplex (tateResSeqHom φ ψ A Aᵥ a Aᵣ ar)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _ (prodSeq_shortExact _ _) (prodSeq_shortExact _ _)

theorem isZero_homology_normCocone (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsZero ((mappingCoconeNat (normCochains Aᵣ)).homology (n + 1)) := by
  have hK : IsZero ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).homology (n + 1)) :=
    isZero_degZeroComplex_homology_succ _ n
  have hepi : Epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n) := by
    cases n with
    | zero =>
      rw [ModuleCat.epi_iff_surjective]
      intro z
      choose m hm using fun w =>
        exists_normClass_eq (Aᵣ w) (hnorm w) ((localCohomologyIso Aᵣ 0).hom.hom z w)
      refine ⟨(degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).inv.hom
        (show ModuleCat.of k (∀ w, Aᵣ w) from m), ?_⟩
      have hinj : Function.Injective (localCohomologyIso Aᵣ 0).hom.hom :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      apply hinj
      rw [localCohomologyIso_homologyMap_normCochains, hom_apply_hom_apply_of_comp_eq
        (Iso.inv_hom_id (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))))]
      exact funext hm
    | succ n =>
      have hsub : ∀ w, Subsingleton (cohomology (Aᵣ w) (n + 1)) := fun w =>
        ModuleCat.isZero_iff_subsingleton.1 (hcoh w n)
      have hL : IsZero ((piComplex fun w => cochains (Aᵣ w)).homology (n + 1)) :=
        IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (localCohomologyIso Aᵣ (n + 1))
      exact ⟨fun _ _ _ => hL.eq_of_src _ _⟩
  have hex := mappingCoconeNat.homology_exact₂ (normCochains Aᵣ) n
  have hδ : mappingCoconeNat.homologyδ (normCochains Aᵣ) n = 0 :=
    (cancel_epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n)).1
      ((mappingCoconeNat.homologyMap_homologyδ _ n).trans comp_zero.symm)
  exact hex.isZero_X₂ hδ (hK.eq_of_tgt _ _)

theorem isIso_tateForget (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsIso (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) := by
  have hS := tateForgetShortComplex_shortExact φ ψ A Aᵥ a Aᵣ ar
  have h0 := isZero_homology_normCocone Aᵣ hcoh hnorm n
  have h1 := isZero_homology_normCocone Aᵣ hcoh hnorm (n + 1)
  have hmono := (hS.homology_exact₂ (n + 1)).mono_g (h0.eq_of_src _ _)
  have hepi := (hS.homology_exact₃ (n + 1) (n + 1 + 1) rfl).epi_f (h1.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) hmono hepi

/-- When the cohomology of the `A_w` vanishes in positive degrees and invariants are norms,
forgetting the finite groups is an isomorphism `Ĥ_c^n ≅ H_c^n`. -/
noncomputable def tateForgetIso (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) ≅ compactSupportCohomology φ A Aᵥ a (n + 1) :=
  @asIso _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1))
    (isIso_tateForget φ ψ A Aᵥ a Aᵣ ar hcoh hnorm n)

end Tate

end InducedDropOut

-- from RealPlaces/Induced.lean
section Induced

open CategoryTheory Limits


section TrivialGroup

variable {k K : Type u} [CommRing k] [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [Subsingleton K]

/-- A module of the trivial group is its own coinduced module. -/
noncomputable def subsingletonCoindIso (M : Rep.{u} k K) : M ≅ discreteCoind k K M where
  hom := Rep.ofHom ⟨{ toFun := fun m => LocallyConstant.const K m
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun m => LocallyConstant.ext fun x => by
      change M.ρ g m = m
      rw [Subsingleton.elim g 1, map_one]
      rfl⟩
  inv := Rep.ofHom ⟨{ toFun := fun f => f 1
                      map_add' := fun _ _ => rfl
                      map_smul' := fun _ _ => rfl }, fun g =>
    LinearMap.ext fun f => by
      change f (1 * g) = M.ρ g (f 1)
      rw [Subsingleton.elim g 1, map_one, mul_one]
      rfl⟩
  hom_inv_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  inv_hom_id := Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun f =>
    LocallyConstant.ext fun x => by
      change f 1 = f x
      rw [Subsingleton.elim x 1]))

theorem isZero_cohomology_succ_of_subsingleton (M : Rep.{u} k K) [IsSmoothRep M] (n : ℕ) :
    IsZero (cohomology M (n + 1)) :=
  (isZero_cohomology_discreteCoind k K M n).of_iso
    { hom := coeffMap (subsingletonCoindIso M).hom (n + 1)
      inv := coeffMap (subsingletonCoindIso M).inv (n + 1)
      hom_inv_id := by rw [← coeffMap_comp, Iso.hom_inv_id, coeffMap_id]
      inv_hom_id := by rw [← coeffMap_comp, Iso.inv_hom_id, coeffMap_id] }

end TrivialGroup

section FreeAction

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (U : Subgroup G) (ι : H →* G)

/-- `y` lies in the `U`-coset of the chosen representative of its double coset. -/
def InOutCoset (y : G) : Prop :=
  ∃ u : U, y = (u : G) * (DoubleCoset.mk U ι.range y).out

theorem doubleCosetMk_mul_left (u : U) (y : G) :
    DoubleCoset.mk U ι.range ((u : G) * y) = DoubleCoset.mk U ι.range y := by
  simpa using doubleCosetMk_mul_mul U ι y u 1

theorem inOutCoset_mul_left_iff (u : U) (y : G) : InOutCoset U ι ((u : G) * y) ↔ InOutCoset U ι y := by
  unfold InOutCoset
  rw [doubleCosetMk_mul_left]
  constructor
  · rintro ⟨u', hu'⟩
    refine ⟨u⁻¹ * u', ?_⟩
    calc y = (u : G)⁻¹ * ((u : G) * y) := by group
      _ = (u : G)⁻¹ * ((u' : G) * (DoubleCoset.mk U ι.range y).out) := by rw [hu']
      _ = ((u⁻¹ * u' : U) : G) * (DoubleCoset.mk U ι.range y).out := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  · rintro ⟨u', hu'⟩
    refine ⟨u * u', ?_⟩
    nth_rewrite 1 [hu']
    rw [Subgroup.coe_mul, mul_assoc]

variable [Fintype H] (N : Rep.{u} k U)

theorem exists_norm_eq_res_coind (hfree : ∀ (x : G) (h : H), x * ι h * x⁻¹ ∈ U → h = 1)
    (f : Rep.res ι (Rep.coind U.subtype N))
    (hf : f ∈ (Rep.res ι (Rep.coind U.subtype N)).ρ.invariants) :
    ∃ m, (Rep.res ι (Rep.coind U.subtype N)).ρ.norm m = f := by
  classical
  have hmem : (fun y => if InOutCoset U ι y then f.1 y else 0) ∈
      Representation.coindV U.subtype N.ρ := by
    intro u y
    change (if InOutCoset U ι ((u : G) * y) then f.1 ((u : G) * y) else 0) =
      N.ρ u (if InOutCoset U ι y then f.1 y else 0)
    by_cases hy : InOutCoset U ι y
    · rw [ite_eq_left ((inOutCoset_mul_left_iff U ι u y).2 hy), ite_eq_left hy]
      exact f.2 u y
    · rw [ite_eq_right (mt (inOutCoset_mul_left_iff U ι u y).1 hy), ite_eq_right hy, map_zero]
  refine ⟨⟨_, hmem⟩, Subtype.ext (funext fun y => ?_)⟩
  have hnorm : ((Rep.res ι (Rep.coind U.subtype N)).ρ.norm ⟨_, hmem⟩).1 y =
      ∑ h : H, (if InOutCoset U ι (y * ι h) then f.1 (y * ι h) else 0) := by
    rw [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hnorm]
  obtain ⟨u₀, h₀, e₀⟩ := exists_eq_mul_out_mul U ι y
  set x := (DoubleCoset.mk U ι.range y).out with hx
  have hD : ∀ h : H, DoubleCoset.mk U ι.range (y * ι h) = DoubleCoset.mk U ι.range y := fun h => by
    have := doubleCosetMk_mul_mul U ι y 1 h
    simpa using this
  have hinv : ∀ h : H, f.1 (y * ι h) = f.1 y := fun h =>
    congrArg (fun g : Rep.res ι (Rep.coind U.subtype N) => g.1 y) (hf h)
  rw [Finset.sum_eq_single h₀⁻¹]
  · rw [ite_eq_left, hinv]
    refine ⟨u₀, ?_⟩
    rw [hD, ← hx, e₀, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  · intro h _ hne
    rw [ite_eq_right]
    rintro ⟨u, hu⟩
    rw [hD, ← hx] at hu
    apply hne
    have key : x * ι (h₀ * h) * x⁻¹ = ((u₀⁻¹ * u : U) : G) := by
      calc x * ι (h₀ * h) * x⁻¹ = (u₀ : G)⁻¹ * ((u₀ : G) * x * ι h₀ * ι h) * x⁻¹ := by
            rw [map_mul]; group
        _ = (u₀ : G)⁻¹ * (y * ι h) * x⁻¹ := by rw [← e₀]
        _ = (u₀ : G)⁻¹ * ((u : G) * x) * x⁻¹ := by rw [hu]
        _ = ((u₀⁻¹ * u : U) : G) := by rw [Subgroup.coe_mul, Subgroup.coe_inv]; group
    exact eq_inv_of_mul_eq_one_right (hfree x _ (key ▸ (u₀⁻¹ * u).2))
  · intro h
    exact absurd (Finset.mem_univ _) h

end FreeAction

section Naturality

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
  {Aᵥ Bᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsSmoothRep (Aᵥ v)] [∀ v, IsSmoothRep (Bᵥ v)]
  {a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v} {b : ∀ v, Rep.res (φ v : H v →* G) B ⟶ Bᵥ v}
  {Aᵣ Bᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsSmoothRep (Aᵣ w)] [∀ w, IsSmoothRep (Bᵣ w)]
  {ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w} {br : ∀ w, Rep.res (ψ w : F w →* G) B ⟶ Bᵣ w}
  (g : A ⟶ B) (gᵥ : ∀ v, Aᵥ v ⟶ Bᵥ v) (gᵣ : ∀ w, Aᵣ w ⟶ Bᵣ w)
  (hg : ∀ v, a v ≫ gᵥ v = (Rep.resFunctor (φ v : H v →* G)).map g ≫ b v)
  (hgr : ∀ w, ar w ≫ gᵣ w = (Rep.resFunctor (ψ w : F w →* G)).map g ≫ br w)

end Naturality

section LocalClasses

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsSmoothRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsSmoothRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v : H v →* G) A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsSmoothRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w : F w →* G) A ⟶ Aᵣ w)

end LocalClasses

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] [∀ v, CompactSpace (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- The conjugates of the finite groups `F_w` meet `U` trivially. -/
def FreeOnCosets (U : Subgroup G) : Prop :=
  ∀ w (x : G) (h : F w), x * ψ w h * x⁻¹ ∈ U → h = 1

variable (U : OpenSubgroup G) (N : Rep.{u} k (U : Subgroup G)) [IsSmoothRep N]

theorem isZero_cohomology_res_coind (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ) (n : ℕ) :
    IsZero (cohomology (Rep.res (ψ w : F w →* G) (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) := by
  have hb := mackeyCohomology_bijective U (ψ w) N (n + 1)
  have hsub : ∀ d : MackeyDoubleCoset (U : Subgroup G) (ψ w : F w →* G),
      Subsingleton (cohomology (mackeyRep (U : Subgroup G) (ψ w).toMonoidHom N d.out) (n + 1)) :=
    fun d => by
      have : Subsingleton (mackeySubgroup (U : Subgroup G) (ψ w).toMonoidHom d.out) :=
        ⟨fun a b => Subtype.ext ((hU w d.out a ((mem_mackeySubgroup _ _ _ _).1 a.2)).trans
          (hU w d.out b ((mem_mackeySubgroup _ _ _ _).1 b.2)).symm)⟩
      exact ModuleCat.isZero_iff_subsingleton.1 (isZero_cohomology_succ_of_subsingleton _ n)
  have : Subsingleton (cohomology (Rep.res (ψ w : F w →* G)
      (Rep.coind (U : Subgroup G).subtype N)) (n + 1)) :=
    ⟨fun c c' => hb.1 (funext fun d => Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

omit [IsTopologicalGroup G] [CompactSpace G] [∀ w, IsTopologicalGroup (F w)] [IsSmoothRep N] in

theorem exists_norm_eq_res_coind' (hU : FreeOnCosets ψ (U : Subgroup G)) (w : κ)
    (f : Rep.res (ψ w : F w →* G) (Rep.coind (U : Subgroup G).subtype N))
    (hf : f ∈ (Rep.res (ψ w : F w →* G) (Rep.coind (U : Subgroup G).subtype N)).ρ.invariants) :
    ∃ m, (Rep.res (ψ w : F w →* G) (Rep.coind (U : Subgroup G).subtype N)).ρ.norm m = f :=
  exists_norm_eq_res_coind (U : Subgroup G) (ψ w : F w →* G) N (hU w) f hf

/-- For `U` meeting the conjugates of the finite groups trivially, `Ĥ_c^{n+1}(G, Coind_U^G N) ≅
H_c^{n+1}(U, N)`. -/
noncomputable def tateCoindIso (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N) (n + 1) ≅
      compactSupportCohomology (mackeyFamily U φ) N (mackeyCoeff U φ N) (fun _ => 𝟙 _) (n + 1) :=
  tateForgetIso φ ψ _ _ _ _ _ (fun w n => isZero_cohomology_res_coind ψ U N hU w n)
      (fun w f hf => exists_norm_eq_res_coind' ψ U N hU w f hf) n ≪≫
    mackeyCompactCohomologyIso U φ N (n + 1)

theorem tateCoindIso_hom (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    (tateCoindIso φ ψ U N hU n).hom =
      tateForget φ ψ _ _ _ _ _ (n + 1) ≫ (mackeyCompactCohomologyIso U φ N (n + 1)).hom :=
  rfl

/-- Corestriction for the Tate-modified cohomology with compact support (when `U` meets the
conjugates of the finite groups trivially). -/
noncomputable def tateCompactCores (hU : FreeOnCosets ψ (U : Subgroup G)) (A : Rep.{u} k G)
    [IsSmoothRep A] (n : ℕ) :
    compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype A) (n + 1) ⟶
      tateCompactCohomologyRes φ ψ A (n + 1) :=
  (tateCoindIso φ ψ U (Rep.res (U : Subgroup G).subtype A) hU n).inv ≫
    tateCompactCohomologyMap φ ψ
      (Aᵥ := fun v => Rep.res (φ v : H v →* G)
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵥ := fun v => Rep.res (φ v : H v →* G) A)
      (Aᵣ := fun w => Rep.res (ψ w : F w →* G)
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)))
      (Bᵣ := fun w => Rep.res (ψ w : F w →* G) A)
      (coindTrace (U : Subgroup G) A)
      (fun v => (Rep.resFunctor (φ v : H v →* G)).map (coindTrace (U : Subgroup G) A))
      (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (coindTrace (U : Subgroup G) A))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) (n + 1)

end Tate

end Induced

end Langlands.GaloisCohomology
