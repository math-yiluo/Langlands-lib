import Langlands.GaloisCohomology.CompactSupport.TateModified.CupProduct
import Langlands.GaloisCohomology.CompactSupport.Duality

/-!
# The Tate-modified duality theorem

The duality map `Hʳ(G, Hom(M, D)) → Hom(Ĥ_c^s(G, M), ℤ/n)` (`tateCompactDualityMap`) and its
dévissage: under `TateCompactDualityHypotheses` it is bijective for `s ≥ 1` and every finite smooth
`M` killed by `n` (`TateCompactDualityHypotheses.bijective_tateCompactDualityMap`).
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from RealPlaces/DevissageDefs.lean
section DevissageDefs

noncomputable section


open CategoryTheory MonoidalCategory Limits


attribute [local instance 2000] Rep.hV2

section ResMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- The map of Tate-modified cochains induced by `g : A ⟶ B`, local modules the restrictions. -/
noncomputable abbrev tateCompactCochainsResMap {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] (g : A ⟶ B) :
    tateCompactCochains φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _) ⟶
      tateCompactCochains φ ψ B (fun v => Rep.res (φ v : H v →* G) B) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) B) (fun _ => 𝟙 _) :=
  tateCompactCochainsMap φ ψ (Aᵥ := fun v => Rep.res (φ v : H v →* G) A)
    (Bᵥ := fun v => Rep.res (φ v : H v →* G) B) (Aᵣ := fun w => Rep.res (ψ w : F w →* G) A)
    (Bᵣ := fun w => Rep.res (ψ w : F w →* G) B) g
    (fun v => (Rep.resFunctor (φ v : H v →* G)).map g)
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The map `Ĥ_c^n(G, A) → Ĥ_c^n(G, B)` induced by `g : A ⟶ B`, local modules the restrictions. -/
noncomputable abbrev tateCompactCohomologyResMap {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] (g : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyRes φ ψ A n ⟶ tateCompactCohomologyRes φ ψ B n :=
  HomologicalComplex.homologyMap (tateCompactCochainsResMap φ ψ g) n

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

theorem tateCompactCochainsResMap_add (g₁ g₂ : A ⟶ B) :
    tateCompactCochainsResMap φ ψ (g₁ + g₂) =
      tateCompactCochainsResMap φ ψ g₁ + tateCompactCochainsResMap φ ψ g₂ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w : F w →* G) A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v : H v →* G) A) fun w => Rep.res (ψ w : F w →* G) A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (cochainsMap_add g₁ g₂)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v)) (cochainsMap_add
          ((Rep.resFunctor (φ v : H v →* G)).map g₁) ((Rep.resFunctor (φ v : H v →* G)).map g₂))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w)) (cochainsMap_add
          ((Rep.resFunctor (ψ w : F w →* G)).map g₁) ((Rep.resFunctor (ψ w : F w →* G)).map g₂))

theorem tateCompactCochainsResMap_zero :
    tateCompactCochainsResMap φ ψ (0 : A ⟶ B) = 0 := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w : F w →* G) A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v : H v →* G) A) fun w => Rep.res (ψ w : F w →* G) A) n) =>
    Prod.ext (Prod.ext ?_ ?_) ?_)
  · exact congrArg (fun F => (F.f n).hom p.1.1) (coeffCochainsMap_zero (A := A) (B := B))
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n =>
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact congrArg (fun F => (F.f n).hom (p.2.1 v))
          (coeffCochainsMap_zero (A := Rep.res (φ v : H v →* G) A) (B := Rep.res (φ v : H v →* G) B))
      · exact congrArg (fun F => (F.f n).hom (p.2.2 w))
          (coeffCochainsMap_zero (A := Rep.res (ψ w : F w →* G) A) (B := Rep.res (ψ w : F w →* G) B))

theorem tateCompactCochainsResMap_id : tateCompactCochainsResMap φ ψ (𝟙 A) = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w : F w →* G) A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v : H v →* G) A) fun w => Rep.res (ψ w : F w →* G) A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

theorem tateCompactCochainsResMap_comp (g : A ⟶ B) (g' : B ⟶ C) :
    tateCompactCochainsResMap φ ψ (g ≫ g') =
      tateCompactCochainsResMap φ ψ g ≫ tateCompactCochainsResMap φ ψ g' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (tateGlobalComplex A
      fun w => Rep.res (ψ w : F w →* G) A).X n × shiftNegOneX (tateLocalComplex
      (fun v => Rep.res (φ v : H v →* G) A) fun w => Rep.res (ψ w : F w →* G) A) n) =>
    Prod.ext (Prod.ext rfl ?_) ?_)
  · cases n with
    | zero => rfl
    | succ n => exact Subsingleton.elim _ _
  · cases n with
    | zero => rfl
    | succ n => rfl

theorem tateCompactCohomologyResMap_add (g₁ g₂ : A ⟶ B) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g₁ + g₂) n =
      tateCompactCohomologyResMap φ ψ g₁ n + tateCompactCohomologyResMap φ ψ g₂ n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_add,
    HomologicalComplex.homologyMap_add]
  rfl

theorem tateCompactCohomologyResMap_zero (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (0 : A ⟶ B) n = 0 := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_zero,
    HomologicalComplex.homologyMap_zero]
  rfl

theorem tateCompactCohomologyResMap_id (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (𝟙 A) n = 𝟙 _ := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_id,
    HomologicalComplex.homologyMap_id]
  rfl

theorem tateCompactCohomologyResMap_comp (g : A ⟶ B) (g' : B ⟶ C) (n : ℕ) :
    tateCompactCohomologyResMap φ ψ (g ≫ g') n =
      tateCompactCohomologyResMap φ ψ g n ≫ tateCompactCohomologyResMap φ ψ g' n := by
  rw [tateCompactCohomologyResMap, tateCompactCochainsResMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

theorem tateCompactCohomologyResMap_finsetSum {J : Type*} (s : Finset J) (f : J → (A ⟶ B))
    (m : ℕ) :
    tateCompactCohomologyResMap φ ψ (∑ j ∈ s, f j) m =
      ∑ j ∈ s, tateCompactCohomologyResMap φ ψ (f j) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [tateCompactCohomologyResMap_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tateCompactCohomologyResMap_add, ih]

theorem nsmul_tateCompactCohomologyRes_eq_zero {m : ℕ} (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : tateCompactCohomologyRes φ ψ A n) : m • x = 0 := by
  have h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0 := by
    rw [Finset.sum_const, Finset.card_range]
    ext a
    exact hm a
  have e : (tateCompactCohomologyResMap φ ψ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x =
      (tateCompactCohomologyResMap φ ψ (0 : A ⟶ A) n).hom x := by rw [h0]
  rw [tateCompactCohomologyResMap_finsetSum, tateCompactCohomologyResMap_zero] at e
  simp only [tateCompactCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e
  simpa using e

end ResMap

section Sequence

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {S : ShortComplex (Rep.{u} k G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃]

/-- The connecting map of `Ĥ_c` (local modules the restrictions) for a short exact sequence of
`G`-modules. -/
noncomputable def tateCompactδRes (hS : S.ShortExact) (n : ℕ) :
    tateCompactCohomologyRes φ ψ S.X₃ n ⟶ tateCompactCohomologyRes φ ψ S.X₁ (n + 1) :=
  tateCompactδ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G))) (fun _ => 𝟙 _)
    (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
    (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n

variable (hS : S.ShortExact)

include hS in

theorem tateCompactRes_exact₂ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.f n) (tateCompactCohomologyResMap φ ψ S.g n)
      (by rw [← tateCompactCohomologyResMap_comp, S.zero, tateCompactCohomologyResMap_zero])).Exact :=
  tateCompactCohomology_exact₂ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G)))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
    (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n

theorem tateCompactRes_exact₃ (n : ℕ) :
    (ShortComplex.mk (tateCompactCohomologyResMap φ ψ S.g n) (tateCompactδRes φ ψ hS n)
      (tateCompactCohomologyMap₂₃_tateCompactδ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G))) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
        (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n)).Exact :=
  tateCompactCohomology_exact₃ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G)))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
    (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n

theorem tateCompactRes_exact₁ (n : ℕ) :
    (ShortComplex.mk (tateCompactδRes φ ψ hS n) (tateCompactCohomologyResMap φ ψ S.f (n + 1))
      (tateCompactδ_tateCompactCohomologyMap₁₂ φ ψ
        (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G))) (fun _ => 𝟙 _)
        (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
        (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
        (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n)).Exact :=
  tateCompactCohomology_exact₁ φ ψ (Sᵥ := fun v => S.map (Rep.resFunctor (φ v : H v →* G)))
    (fun _ => 𝟙 _) (Sᵣ := fun w => S.map (Rep.resFunctor (ψ w : F w →* G))) (fun _ => 𝟙 _) hS
    (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hS)
    (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hS) n

end Sequence

section CupRes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- The cup product with Tate-modified compact support, local modules the restrictions. -/
noncomputable def tateCompactCupRes {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomologyRes φ ψ A r →ₗ[k] cohomology B s →ₗ[k] tateCompactCohomologyRes φ ψ C n :=
  tateCompactCup φ ψ μ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) μ)
    (fun w => resFunctor_map_comp_id (ψ w : F w →* G) μ) h

/-- The Tate-modified duality map `Hʳ(G, Hom(M, D)) → Hom(Ĥ_c^s(G, M), ℤ/n)`. -/
def tateCompactDualityMap (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] :
    cohomology M r →+ (tateCompactCohomologyRes φ ψ (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp ((bilinAddHom (tateCompactCupRes φ ψ (dualEvalPairing D M)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem tateCompactDualityMap_apply (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ}
    (h : r + s = m) (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G)
    [IsSmoothRep M] [IsSmoothRep (dualRep D M)] (x : cohomology M r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D M) s) :
    tateCompactDualityMap φ ψ D h t M x y =
      t (tateCompactCupRes φ ψ (dualEvalPairing D M) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end CupRes

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- The hypotheses of the Tate-modified dévissage (as `CompactGroupDualityHypotheses`, for `s ≥
1`). -/
structure TateCompactDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep D] (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) :
    Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- The Tate-modified `Ĥ_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (tateCompactCohomologyRes φ ψ M 4)
  /-- The Tate-modified duality map is bijective, for `s ≥ 1`, for the modules coinduced from `ℤ/n` on open subgroups below `U₀`. -/
  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))

end Hypotheses

end

end DevissageDefs

-- from RealPlaces/DevissageNatural.lean
section DevissageNatural

noncomputable section


open CategoryTheory MonoidalCategory Limits Langlands.ProfiniteCohomology.GroupCoh


attribute [local instance 2000] Rep.hV2

section CupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {A A' B B' C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep A'] [IsSmoothRep B]
  [IsSmoothRep B'] [IsSmoothRep C]

/-- The Leibniz pairing defining `tateCompactCupRes`. -/
noncomputable abbrev tateCompactCupResLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (tateCompactCochains φ ψ A (fun v => Rep.res (φ v : H v →* G) A) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) A) (fun _ => 𝟙 _)) (cochains B)
      (tateCompactCochains φ ψ C (fun v => Rep.res (φ v : H v →* G) C) (fun _ => 𝟙 _)
        (fun w => Rep.res (ψ w : F w →* G) C) (fun _ => 𝟙 _)) :=
  tateCompactCupLeibniz φ ψ μ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) μ)
    (fun w => resFunctor_map_comp_id (ψ w : F w →* G) μ)

theorem tateCompactCupRes_eq_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    tateCompactCupRes φ ψ μ h = (tateCompactCupResLeibniz φ ψ μ).homology h :=
  rfl

theorem tateCompactCupResLeibniz_naturality (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C) (g : A' ⟶ A)
    (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ} (h : r + s = n)
    (p : (tateCompactCochains φ ψ A' (fun v => Rep.res (φ v : H v →* G) A') (fun _ => 𝟙 _)
      (fun w => Rep.res (ψ w : F w →* G) A') (fun _ => 𝟙 _)).X r)
    (z : (cochains B).X s) :
    (tateCompactCupResLeibniz φ ψ μ).μ h (((tateCompactCochainsResMap φ ψ g).f r).hom p) z =
      (tateCompactCupResLeibniz φ ψ μ').μ h p (((coeffCochainsMap f).f s).hom z) := by
  revert p
  intro (p : (tateGlobalComplex A' fun w => Rep.res (ψ w : F w →* G) A').X r ×
    shiftNegOneX (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) A')
      fun w => Rep.res (ψ w : F w →* G) A') r)
  obtain ⟨⟨x0, e⟩, b⟩ := p
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · apply cochainOf_injective
    funext σ
    exact (cupCochain_naturality μ μ' g f hμ h (cochainOf _ x0) (cochainOf _ z) σ).symm
  · rcases r with _ | r
    · rcases s with _ | s
      · obtain rfl : n = 0 := by omega
        funext w
        exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf B z (fun i => i.elim0) :
          (Rep.res (ψ w : F w →* G) A' ⊗ Rep.res (ψ w : F w →* G) B : Rep k (F w)))))
          (resFunctor_map_naturality (ψ w : F w →* G) μ μ' g f hμ)
      · rfl
    · rfl
  · rcases r with _ | r
    · rcases s with _ | t
      · obtain rfl : n = 0 := by omega
        exact Subsingleton.elim (α := PUnit) _ _
      · obtain rfl : n = t + 1 := by omega
        change (0 : (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) C)
              fun w => Rep.res (ψ w : F w →* G) C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)
              (Cᵥ := fun v => Rep.res (φ v : H v →* G) C) (rfl : t + 1 = t + 1)
              ((piRepHom fun w => (Rep.resFunctor (ψ w : F w →* G)).map g).hom e) z =
          (0 : (tateLocalComplex (fun v => Rep.res (φ v : H v →* G) C)
              fun w => Rep.res (ψ w : F w →* G) C).X t) +
            tateCupHomotopyL ψ (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ')
              (Cᵥ := fun v => Rep.res (φ v : H v →* G) C) (rfl : t + 1 = t + 1) e
              (((coeffCochainsMap f).f (t + 1)).hom z)
        erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
        refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
        have key := normHomotopy_compat_left ((Rep.resFunctor (ψ w : F w →* G)).map μ')
          ((Rep.resFunctor (ψ w : F w →* G)).map μ) ((Rep.resFunctor (ψ w : F w →* G)).map g)
          ((Rep.resFunctor (ψ w : F w →* G)).map f)
          (resFunctor_map_naturality (ψ w : F w →* G) μ μ' g f hμ) (rfl : t + 1 = t + 1) (e w)
          (((localRes ψ B (fun w => Rep.res (ψ w : F w →* G) B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        exact key
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
      change (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ)
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ)).μ (show r + s = m by omega)
            ((tateLocalMap (fun v => (Rep.resFunctor (φ v : H v →* G)).map g)
              fun w => (Rep.resFunctor (ψ w : F w →* G)).map g).f r |>.hom b)
            (((tateLocalResB φ ψ B).f s).hom z) + 0 =
          (tateLocalCup φ ψ (fun v => (Rep.resFunctor (φ v : H v →* G)).map μ')
            (fun w => (Rep.resFunctor (ψ w : F w →* G)).map μ')).μ (show r + s = m by omega) b
            (((tateLocalResB φ ψ B').f s).hom (((coeffCochainsMap f).f s).hom z)) + 0
      rw [add_zero, add_zero]
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (φ v : H v →* G)).map μ)
          ((Rep.resFunctor (φ v : H v →* G)).map μ') ((Rep.resFunctor (φ v : H v →* G)).map g)
          ((Rep.resFunctor (φ v : H v →* G)).map f)
          (resFunctor_map_naturality (φ v : H v →* G) μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.1 v)) (fun τ => cochainOf B z (⇑(φ v : H v →* G) ∘ τ)) σ).symm
      · apply cochainOf_injective
        funext σ
        exact (cupCochain_naturality ((Rep.resFunctor (ψ w : F w →* G)).map μ)
          ((Rep.resFunctor (ψ w : F w →* G)).map μ') ((Rep.resFunctor (ψ w : F w →* G)).map g)
          ((Rep.resFunctor (ψ w : F w →* G)).map f)
          (resFunctor_map_naturality (ψ w : F w →* G) μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b.2 w)) (fun τ => cochainOf B z (⇑(ψ w : F w →* G) ∘ τ)) σ).symm

theorem tateCompactCupRes_tateCompactCohomologyResMap (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C)
    (g : A' ⟶ A) (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ}
    (h : r + s = n) (y : tateCompactCohomologyRes φ ψ A' r) (x : cohomology B s) :
    tateCompactCupRes φ ψ μ h ((tateCompactCohomologyResMap φ ψ g r).hom y) x =
      tateCompactCupRes φ ψ μ' h y ((coeffMap f s).hom x) := by
  rw [tateCompactCupRes_eq_homology, tateCompactCupRes_eq_homology]
  exact (LeibnizPairing.homology_homologyMap (tateCompactCupResLeibniz φ ψ μ')
    (tateCompactCupResLeibniz φ ψ μ) (tateCompactCochainsResMap φ ψ g) (coeffCochainsMap f)
    (fun h p z => (tateCompactCupResLeibniz_naturality φ ψ μ μ' g f hμ h p z).symm) h y x).symm

end CupNatural

section DualityNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
  (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n)

theorem tateCompactDualityMap_cohomologyMap {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep (dualRep D A)] [IsSmoothRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : tateCompactCohomologyRes φ ψ (dualRep D B) s) :
    tateCompactDualityMap φ ψ D h t B ((coeffMap f r).hom x) y =
      tateCompactDualityMap φ ψ D h t A x ((tateCompactCohomologyResMap φ ψ (dualMap D f) s).hom y) := by
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply,
    tateCompactCupRes_tateCompactCohomologyResMap φ ψ (dualEvalPairing D A) (dualEvalPairing D B)
      (dualMap D f) f (tensorHom_dualEvalPairing D f)]

theorem bijective_tateCompactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, IsSmoothRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsSmoothRep P] [IsSmoothRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t P) := by
  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, (coeffMap (i j) r).hom ((coeffMap (p j) r).hom x) := by
    intro x
    have e := congrArg (fun φ => (coeffMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, coeffMap_id, coeffMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : tateCompactCohomologyRes φ ψ (dualRep D P) s,
      ∑ j, (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom
        ((tateCompactCohomologyResMap φ ψ (dualMap D (i j)) s).hom y) = y := by
    intro y
    have e := congrArg (fun F => (tateCompactCohomologyResMap φ ψ (dualMap D F) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, tateCompactCohomologyResMap_finsetSum, dualMap_id,
      tateCompactCohomologyResMap_id, tateCompactCohomologyResMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at e
    exact e
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hj : ∀ j, (coeffMap (p j) r).hom x = 0 := by
      intro j
      apply (hX j).1
      rw [map_zero]
      ext y
      rw [AddMonoidHom.zero_apply, tateCompactDualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2
      (χ.comp (tateCompactCohomologyResMap φ ψ (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, (coeffMap (i j) r).hom (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [tateCompactDualityMap_cohomologyMap, ha j]
    rfl

theorem bijective_tateCompactDualityMap_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, Finite (X j)]
    (hX : ∀ j, Function.Bijective (tateCompactDualityMap φ ψ D h t (X j))) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t (⨁ X)) :=
  bijective_tateCompactDualityMap_of_sum φ ψ D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end DualityNatural

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {N : ℕ}
  {S : ShortComplex (Rep.{u} (ULift.{u} ℤ) G)} [IsSmoothRep S.X₁] [IsSmoothRep S.X₂]
  [IsSmoothRep S.X₃] [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]

theorem tateCompactDualityMap_δ {n : ℕ} (t : tateCompactCohomologyRes φ ψ D (n + 1) →+ ZMod N)
    (hS : S.ShortExact) (hT : (dualShortComplex D S).ShortExact) {r s : ℕ}
    (h₁ : r + 1 + s = n + 1) (h₀ : r + (s + 1) = n + 1) (q : cohomology S.X₃ r)
    (y : tateCompactCohomologyRes φ ψ (dualRep D S.X₁) s) :
    tateCompactDualityMap φ ψ D h₁ t S.X₁ ((δ hS r (r + 1) rfl).hom q) y =
      (-(-1 : ℤ) ^ s) • tateCompactDualityMap φ ψ D h₀ t S.X₃ q ((tateCompactδRes φ ψ hT s).hom y) := by
  have key := tateCompactCup_tateCompactδ_add_tateCompactCup_δ φ ψ
    (SAᵥ := fun v => (dualShortComplex D S).map (Rep.resFunctor (φ v : H v →* G)))
    (fun _ => 𝟙 _)
    (SAᵣ := fun w => (dualShortComplex D S).map (Rep.resFunctor (ψ w : F w →* G)))
    (fun _ => 𝟙 _) (C := D) (Cᵥ := fun v => Rep.res (φ v : H v →* G) D) (c := fun _ => 𝟙 _)
    (Cᵣ := fun w => Rep.res (ψ w : F w →* G) D) (cr := fun _ => 𝟙 _)
    (dualEvalPairing D S.X₃) (dualEvalPairing D S.X₂) (dualEvalPairing D S.X₁)
    (fun v => (Rep.resFunctor (φ v : H v →* G)).map (dualEvalPairing D S.X₃))
    (fun v => (Rep.resFunctor (φ v : H v →* G)).map (dualEvalPairing D S.X₂))
    (fun v => (Rep.resFunctor (φ v : H v →* G)).map (dualEvalPairing D S.X₁))
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (dualEvalPairing D S.X₃))
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (dualEvalPairing D S.X₂))
    (fun w => (Rep.resFunctor (ψ w : F w →* G)).map (dualEvalPairing D S.X₁))
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) _)
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) _)
    (fun v => resFunctor_map_comp_id (φ v : H v →* G) _)
    (fun w => resFunctor_map_comp_id (ψ w : F w →* G) _)
    (fun w => resFunctor_map_comp_id (ψ w : F w →* G) _)
    (fun w => resFunctor_map_comp_id (ψ w : F w →* G) _)
    (tensorHom_dualEvalPairing D S.g) (tensorHom_dualEvalPairing D S.f).symm
    (fun v => resFunctor_map_naturality (φ v : H v →* G) _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun v => (resFunctor_map_naturality (φ v : H v →* G) _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    (fun w => resFunctor_map_naturality (ψ w : F w →* G) _ _ _ _ (tensorHom_dualEvalPairing D S.g))
    (fun w => (resFunctor_map_naturality (ψ w : F w →* G) _ _ _ _
      (tensorHom_dualEvalPairing D S.f)).symm)
    hT (fun v => (Rep.shortExact_res (φ v : H v →* G)).2 hT)
    (fun w => (Rep.shortExact_res (ψ w : F w →* G)).2 hT) hS
    (show s + 1 + r = n + 1 by omega) (show s + (r + 1) = n + 1 by omega) y q
  rw [tateCompactDualityMap_apply, tateCompactDualityMap_apply]
  exact map_eq_of_add_neg_one_pow_smul_eq_zero t s key

end Sign

end

end DevissageNatural

-- from RealPlaces/Devissage.lean
section Devissage

noncomputable section


open CategoryTheory MonoidalCategory Limits


attribute [local instance 2000] Rep.hV2

section Core

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

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
      ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
        Function.Bijective (tateCompactDualityMap φ ψ D h t I) := by
  obtain ⟨W, hW, J, _, i, hi⟩ := exists_injective_biproduct_coind_le (n := n) U₀ M hM
  have hφ : ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective (tateCompactDualityMap φ ψ D h t
      (⨁ fun _ : J => Rep.coind (W : Subgroup G).subtype (zmodRep.{u} (W : Subgroup G) n) :
        Rep.{u} (ULift.{u} ℤ) G)) :=
    fun h hs => bijective_tateCompactDualityMap_biproduct φ ψ D h t _
      fun _ => H.bijective_coind W hW h hs
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

end TateCompactDualityHypotheses

end Core

section Steps

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

include H in

theorem injective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  have hi : Function.Injective i.hom := (Rep.mono_iff_injective i).1 hS.mono_f
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t I ((coeffMap i 0).hom x) = 0 := by
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t i x y, hx]
    rfl
  have h2 : (coeffMap i 0).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI (rfl : 0 + 3 = 3) (by norm_num)).1 _ h1
  exact (injective_iff_map_eq_zero _).1 (injective_cohomologyMap_zero i hi) x h2

include H in

theorem surjective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  have hsurj : Function.Surjective (tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom := by
    intro y
    have : Subsingleton (tateCompactCohomologyRes φ ψ (dualRep D Q) 4) :=
      H.subsingleton_four (dualRep D Q) (nsmul_dualRep_eq_zero H.nsmul_D)
    exact (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₃ φ ψ hT 3) y
      (Subsingleton.elim _ _)
  intro l
  obtain ⟨v, hv⟩ := (hI (rfl : 0 + 3 = 3) (by norm_num)).2
    (l.comp (tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom.toAddMonoidHom)
  have hpv : (coeffMap p 0).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_zero Q hnQ)
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t p v y, hv]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D p) 3 ≫
      tateCompactCohomologyResMap φ ψ (dualMap D i) 3).hom y) = 0
    rw [← tateCompactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      tateCompactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS 0) v hpv
  refine ⟨m, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := hsurj y
  rw [← tateCompactDualityMap_cohomologyMap φ ψ D (rfl : 0 + 3 = 3) t i m z]
  change tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t I ((coeffMap S.f 0).hom m) z = _
  rw [hm, hv]
  rfl

include H in
theorem bijective_zero (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (tateCompactDualityMap φ ψ D (rfl : 0 + 3 = 3) t M) :=
  ⟨H.injective_zero M hM, H.surjective_zero M hM⟩

variable {r s : ℕ} (h₁ : r + 1 + s = 3) (h₀ : r + (s + 1) = 3) (hs : 1 ≤ s)

include H hs in

theorem injective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Injective (tateCompactDualityMap φ ψ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : tateCompactDualityMap φ ψ D h₁ t I ((coeffMap i (r + 1)).hom x) = 0 := by
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₁ t i x y, hx]
    rfl
  have hix : (coeffMap i (r + 1)).hom x = 0 :=
    (injective_iff_map_eq_zero _).1 (hI h₁ hs).1 _ h1
  obtain ⟨q, hq⟩ :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS r (r + 1) rfl) x hix
  have hker : ((tateCompactCohomologyResMap φ ψ (dualMap D p) (s + 1)).hom.toAddMonoidHom).ker ≤
      (tateCompactDualityMap φ ψ D h₀ t Q q).ker := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₁ φ ψ hT s) z hz
    rw [AddMonoidHom.mem_ker, ← hy]
    have e := tateCompactDualityMap_δ φ ψ D t hS hT h₁ h₀ q y
    change tateCompactDualityMap φ ψ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
    rw [hq, hx, AddMonoidHom.zero_apply] at e
    exact eq_zero_of_neg_neg_one_pow_zsmul s e.symm
  obtain ⟨χ, hχ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_tateCompactCohomologyRes_eq_zero φ ψ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨v, hv⟩ := (ih I hnI).2 χ
  have hpv : (coeffMap p r).hom v = q := by
    apply (ih Q hnQ).1
    ext z
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₀ t p v z, hv, ← hχ]
    rfl
  rw [← hq, ← hpv]
  exact congrArg (fun F => F.hom v) (comp_δ hS r (r + 1) rfl)

include H hs in

theorem surjective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (tateCompactDualityMap φ ψ D h₁ t M) := by
  have := H.finite_D
  obtain ⟨I, Q, _, _, _, _, i, p, w, hS, hnI, hnQ, hI⟩ := H.exists_devissage M hM
  let S := ShortComplex.mk i p w
  have hT : (dualShortComplex D S).ShortExact :=
    dualShortComplex_shortExact H.nonempty_addEquiv hS hnI
  intro l
  obtain ⟨v, hv⟩ := (hI h₁ hs).2 (l.comp (tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom.toAddMonoidHom)
  have hpv : (coeffMap p (r + 1)).hom v = 0 := by
    apply (injective_iff_map_eq_zero _).1 (H.injective_succ h₁ h₀ hs ih Q hnQ)
    ext y
    rw [tateCompactDualityMap_cohomologyMap φ ψ D h₁ t p v y, hv]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D p) s ≫
      tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom y) = 0
    rw [← tateCompactCohomologyResMap_comp, ← dualMap_comp, w, dualMap_zero,
      tateCompactCohomologyResMap_zero]
    exact map_zero l
  obtain ⟨x', hx'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hS (r + 1)) v hpv
  set ν := l - tateCompactDualityMap φ ψ D h₁ t M x' with hν
  have hker : ((tateCompactδRes φ ψ hT s).hom.toAddMonoidHom).ker ≤ ν.ker := by
    intro y hy
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₃ φ ψ hT s) y hy
    rw [AddMonoidHom.mem_ker, ← hz, hν, AddMonoidHom.sub_apply, sub_eq_zero]
    change l ((tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom z) =
      tateCompactDualityMap φ ψ D h₁ t M x' ((tateCompactCohomologyResMap φ ψ (dualMap D i) s).hom z)
    rw [← tateCompactDualityMap_cohomologyMap φ ψ D h₁ t i x' z]
    change _ = tateCompactDualityMap φ ψ D h₁ t I ((coeffMap S.f (r + 1)).hom x') z
    rw [hx', hv]
    rfl
  obtain ⟨χ, hχ⟩ := zmod_exists_comp_eq_of_ker_le
    (nsmul_tateCompactCohomologyRes_eq_zero φ ψ (nsmul_dualRep_eq_zero H.nsmul_D) (s + 1)) _ _ hker
  obtain ⟨q, hq⟩ := (ih Q hnQ).2 χ
  refine ⟨x' + (-(-1 : ℤ) ^ s) • (δ hS r (r + 1) rfl).hom q, ?_⟩
  ext y
  have e := tateCompactDualityMap_δ φ ψ D t hS hT h₁ h₀ q y
  change tateCompactDualityMap φ ψ D h₁ t M ((δ hS r (r + 1) rfl).hom q) y = _ at e
  have hχy : χ ((tateCompactδRes φ ψ hT s).hom y) = ν y := congrArg (fun f => f y) hχ
  rw [map_add, map_zsmul, AddMonoidHom.add_apply, AddMonoidHom.smul_apply, e, hq,
    neg_neg_one_pow_zsmul_zsmul]
  change _ + χ ((tateCompactδRes φ ψ hT s).hom y) = l y
  rw [hχy, hν, AddMonoidHom.sub_apply, add_sub_cancel]

include H hs in
theorem bijective_succ
    (ih : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Function.Bijective (tateCompactDualityMap φ ψ D h₀ t M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (tateCompactDualityMap φ ψ D h₁ t M) :=
  ⟨H.injective_succ h₁ h₀ hs ih M hM, H.surjective_succ h₁ h₀ hs ih M hM⟩

end TateCompactDualityHypotheses

end Steps

section Main

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] {φ : ∀ v, Hv v →ₜ* G}
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] {ψ : ∀ w, F w →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep D]
  {t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n} {U₀ : OpenSubgroup G}

namespace TateCompactDualityHypotheses

variable (H : TateCompactDualityHypotheses φ ψ n D t U₀)

include H in

theorem bijective_tateCompactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t M) := by
  have b0 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) => H.bijective_zero M hM
  have b1 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) =>
      H.bijective_succ (r := 0) (s := 2) rfl rfl (by norm_num) b0 M hM
  have b2 := fun (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) =>
      H.bijective_succ (r := 1) (s := 1) rfl rfl (by norm_num) b1 M hM
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (r = 0 ∧ s = 3) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by omega
  · exact b0 M hM
  · exact b1 M hM
  · exact b2 M hM

end TateCompactDualityHypotheses

end Main

end

end Devissage

noncomputable section

open CategoryTheory

section Abstract

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

/-- The vanishing of `Ĥ_cⁿ` passes to extensions. -/
theorem subsingleton_tateCompactCohomologyRes_of_shortExact {S : ShortComplex (Rep.{u} k G)}
    [IsSmoothRep S.X₁] [IsSmoothRep S.X₂] [IsSmoothRep S.X₃] (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (tateCompactCohomologyRes φ ψ S.X₁ n))
    (h₃ : Subsingleton (tateCompactCohomologyRes φ ψ S.X₃ n)) :
    Subsingleton (tateCompactCohomologyRes φ ψ S.X₂ n) := by
  refine ⟨fun x x' => ?_⟩
  suffices h : ∀ x : tateCompactCohomologyRes φ ψ S.X₂ n, x = 0 from (h x).trans (h x').symm
  intro x
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (tateCompactRes_exact₂ φ ψ hS n) x
    (Subsingleton.elim _ _)
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- The vanishing of `Ĥ_cⁿ` passes to retracts. -/
theorem subsingleton_tateCompactCohomologyRes_of_retract {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] (i : A ⟶ B) (p : B ⟶ A) (hip : i ≫ p = 𝟙 A) (n : ℕ)
    (hB : Subsingleton (tateCompactCohomologyRes φ ψ B n)) :
    Subsingleton (tateCompactCohomologyRes φ ψ A n) := by
  refine ⟨fun x x' => ?_⟩
  have key : ∀ x : tateCompactCohomologyRes φ ψ A n,
      (tateCompactCohomologyResMap φ ψ p n).hom ((tateCompactCohomologyResMap φ ψ i n).hom x) = x :=
    fun x => by
      rw [← ConcreteCategory.comp_apply, ← tateCompactCohomologyResMap_comp, hip,
        tateCompactCohomologyResMap_id]
      rfl
  rw [← key x, ← key x', Subsingleton.elim ((tateCompactCohomologyResMap φ ψ i n).hom x)
    ((tateCompactCohomologyResMap φ ψ i n).hom x')]

end Abstract

end

end Langlands.GaloisCohomology
