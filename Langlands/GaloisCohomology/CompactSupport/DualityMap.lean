import Langlands.GaloisCohomology.CompactSupport.CupProduct
import Langlands.GaloisCohomology.CompactSupport.OpenSubgroup
import Langlands.Cohomology.Profinite.Duality.Devissage
import Langlands.Cohomology.Profinite.Dimension.Basic

/-!
# The duality map of cohomology with compact support

For a dualizing module `D` with a trace `t : H_c^m(G, D) → ℤ/n`, the duality map
`Hʳ(G, Hom(M, D)) → Hom(H_c^s(G, M), ℤ/n)` (`r + s = m`) is the cup product with evaluation followed
by `t` (`compactDualityMap`). This file defines it with the cup product `compactCupRes` (local
modules the restrictions), corestriction `compactCores` from an open subgroup, the hypothesis
structure `CompactDualityHypotheses` of the duality theorem, the functoriality of `H_c` in the
module (`compactSupportCohomologyResMap`) and the naturality of the duality map, and its
bijectivity for direct sums and biproducts.
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from PoincarePairs/IsDiscreteRepResHomCoindRes.lean
section IsDiscreteRepResHomCoindRes

noncomputable section


open CategoryTheory MonoidalCategory


attribute [local instance 2000] Rep.hV2

section Eval

variable {k G : Type u} [CommRing k] [Group G]

/-- Evaluation `Hom(M, D) ⊗ M → D`, with the dual module in the left factor. -/
def dualEvalPairing (D M : Rep.{u} k G) : dualRep D M ⊗ M ⟶ D :=
  (β_ (dualRep D M) M).hom ≫ evalPairing D M

@[simp]
theorem dualEvalPairing_tmul (D M : Rep.{u} k G) (f : M →ₗ[k] D) (m : M) :
    (dualEvalPairing D M).hom ((f : dualRep D M) ⊗ₜ[k] m : (dualRep D M ⊗ M : Rep k G)) = f m :=
  rfl

variable {H : Type u} [Group H]

theorem resFunctor_map_comp_id (ψ : H →* G) {A B C : Rep.{u} k G} (μ : A ⊗ B ⟶ C) :
    (Rep.resFunctor ψ).map μ ≫ 𝟙 _ =
      resTensorHom ψ (𝟙 (Rep.res ψ A)) (𝟙 (Rep.res ψ B)) ≫ (Rep.resFunctor ψ).map μ := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Eval

section CupRes

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- The cup product `H_c^r(G, A) × Hˢ(G, B) → H_c^{r+s}(G, C)` when the local modules are the
restrictions. -/
noncomputable def compactCupRes {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    compactSupportCohomologyRes φ A r →ₗ[k] cohomology B s →ₗ[k] compactSupportCohomologyRes φ C n :=
  compactCup φ μ (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map μ)
    (fun v => resFunctor_map_comp_id (φ v : Hv v →* G) μ) h

/-- The duality map `Hʳ(G, Hom(M, D)) → Hom(H_c^s(G, M), ℤ/n)` (`r + s = m`): cup product with
evaluation followed by a trace `t : H_c^m(G, D) → ℤ/n`. -/
def compactDualityMap (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] :
    cohomology M r →+ (compactSupportCohomologyRes φ (dualRep D M) s →+ ZMod n) where
  toFun x := t.comp ((bilinAddHom (compactCupRes φ (dualEvalPairing D M)
    ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem compactDualityMap_apply (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] (x : cohomology M r)
    (y : compactSupportCohomologyRes φ (dualRep D M) s) :
    compactDualityMap φ D h t M x y =
      t (compactCupRes φ (dualEvalPairing D M) ((Nat.add_comm s r).trans h) y x) :=
  rfl

end CupRes

section Cores

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (φ : ∀ v, Hv v →ₜ* G)

omit [∀ v, CompactSpace (Hv v)] in

instance isSmoothRep_resHom_coind_res {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] (ψ : K →ₜ* G) (V : OpenSubgroup G) (A : Rep.{u} k G)
    [IsSmoothRep A] :
    IsSmoothRep (Rep.res (ψ : K →* G)
      (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A))) :=
  isSmoothRep_res ψ _

/-- Corestriction on cohomology with compact support from an open subgroup `V` (with its Mackey
family) to `G`. -/
noncomputable def compactCores (V : OpenSubgroup G) (A : Rep.{u} k G) [IsSmoothRep A] (n : ℕ) :
    compactSupportCohomologyRes (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n ⟶
      compactSupportCohomologyRes φ A n :=
  (mackeyCompactCohomologyIso V φ (Rep.res (V : Subgroup G).subtype A) n).inv ≫
    compactSupportMap φ (Aᵥ := fun v => Rep.res (φ v : Hv v →* G)
        (Rep.coind (V : Subgroup G).subtype (Rep.res (V : Subgroup G).subtype A)))
      (Bᵥ := fun v => Rep.res (φ v : Hv v →* G) A) (coindTrace (V : Subgroup G) A)
      (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map (coindTrace (V : Subgroup G) A))
      (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) n

end Cores

section Hypotheses

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- Multiplication `D ⊗ ℤ/n → D` for a module `D` killed by `n`. -/
def zmodMulPairingRight (n : ℕ) {K : Type u} [Group K] (D : Rep.{u} (ULift.{u} ℤ) K)
    (hD : ∀ d : D, n • d = 0) : D ⊗ zmodRep.{u} K n ⟶ D :=
  (β_ D (zmodRep.{u} K n)).hom ≫ zmodMulPairing n D hD

/-- The duality map for `ℤ/n` over an open subgroup `U`: `Hʳ(U, ℤ/n) → Hom(H_c^s(U, D), ℤ/n)`. -/
def zmodCompactDualityMap (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) {m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) :
    cohomology (zmodRep.{u} (U : Subgroup G) n) r →+
      (compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s →+ ZMod n)
    where
  toFun x := (t.comp (compactCores φ U D m).hom.toAddMonoidHom).comp
    ((bilinAddHom (compactCupRes (mackeyFamily U φ)
      (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
      ((Nat.add_comm s r).trans h))).flip x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem zmodCompactDualityMap_apply (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) {m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) (x : cohomology (zmodRep.{u} (U : Subgroup G) n) r)
    (y : compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s) :
    zmodCompactDualityMap φ D hD U h t x y =
      t ((compactCores φ U D m).hom (compactCupRes (mackeyFamily U φ)
        (zmodMulPairingRight n (Rep.res (U : Subgroup G).subtype D) hD)
        ((Nat.add_comm s r).trans h) y x)) :=
  rfl

/-- The hypotheses of the duality theorem for cohomology with compact support: `D ≅ ℤ/n`,
vanishing of `H_c^4` for modules killed by `n`, and bijectivity of the duality map for `ℤ/n` over
all open subgroups below `U₀`. -/
structure CompactDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
    (t : compactSupportCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- `H_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactSupportCohomologyRes φ M 4)
  /-- The duality map for `ℤ/n` is bijective over every open subgroup below `U₀`. -/
  bijective_base : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (zmodCompactDualityMap φ D
      (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv) U h t)

end Hypotheses

section ZModRes

variable {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
  [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G ≃ₜ* G')

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
/-- Restriction along a topological isomorphism `θ : G ≃ₜ* G'` carries the multiplication pairing
`D' ⊗ ℤ/n → D'` to that of `D`, through a morphism `f : Res_θ D' ⟶ D` and `zmodRepResIso`. -/
theorem zmodMulPairingRight_res (n : ℕ) {D' : Rep.{u} (ULift.{u} ℤ) G'}
    {D : Rep.{u} (ULift.{u} ℤ) G} (hD' : ∀ d : D', n • d = 0) (hD : ∀ d : D, n • d = 0)
    (f : Rep.res (θ : G →* G') D' ⟶ D) :
    (Rep.resFunctor (θ : G →* G')).map (zmodMulPairingRight n D' hD') ≫ f =
      resTensorHom (θ : G →* G') f (zmodRepResIso θ n).hom ≫ zmodMulPairingRight n D hD := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro d a
  obtain ⟨a⟩ := a
  change f.hom ((zmodMulPairing n D' hD').hom ((ULift.up a : zmodRep.{u} G' n) ⊗ₜ[ULift.{u} ℤ] (d : D') :
      (zmodRep.{u} G' n ⊗ D' : Rep _ _))) =
    (zmodMulPairing n D hD).hom ((ULift.up a : zmodRep.{u} G n) ⊗ₜ[ULift.{u} ℤ] f.hom d :
      (zmodRep.{u} G n ⊗ D : Rep _ _))
  rw [zmodMulPairing_tmul, zmodMulPairing_tmul]
  exact map_zsmul f.hom.toLinearMap.toAddMonoidHom _ _

end ZModRes

end

end IsDiscreteRepResHomCoindRes

-- from PoincarePairs/Natural.lean
section Natural

noncomputable section


open CategoryTheory MonoidalCategory Limits Langlands.ProfiniteCohomology.GroupCoh


attribute [local instance 2000] Rep.hV2

section LeibnizNatural

variable {k : Type u} [CommRing k] {M M' N N' P : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homology_homologyMap (μ₁ : LeibnizPairing M N P)
    (μ₂ : LeibnizPairing M' N' P) (f : M ⟶ M') (g : N' ⟶ N)
    (hfg : ∀ {r s n : ℕ} (h : r + s = n) (x : M.X r) (y : N'.X s),
      μ₁.μ h x ((g.f s).hom y) = μ₂.μ h ((f.f r).hom x) y)
    {r s n : ℕ} (h : r + s = n) (x : M.homology r) (y : N'.homology s) :
    μ₁.homology h x ((HomologicalComplex.homologyMap g s).hom y) =
      μ₂.homology h ((HomologicalComplex.homologyMap f r).hom x) y := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective M r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective N' s y
  rw [hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality g s) y,
    hom_apply_hom_apply_eq_of_comp_eq (HomologicalComplex.homologyπ_naturality f r) x,
    LeibnizPairing.homology_homologyπ, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles, iCycles_cyclesMap_apply,
    iCycles_cyclesMap_apply]
  exact hfg h _ _

end LeibnizNatural

section ResMap

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- The map of compactly supported cochains induced by `g : A ⟶ B`, local modules the
restrictions. -/
noncomputable abbrev compactSupportCochainsResMap {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    (g : A ⟶ B) :
    compactSupportCochains φ A (fun v => Rep.res (φ v : Hv v →* G) A) (fun _ => 𝟙 _) ⟶
      compactSupportCochains φ B (fun v => Rep.res (φ v : Hv v →* G) B) (fun _ => 𝟙 _) :=
  compactSupportCochainsMap φ (Aᵥ := fun v => Rep.res (φ v : Hv v →* G) A)
    (Bᵥ := fun v => Rep.res (φ v : Hv v →* G) B) g
    (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The map `H_c^n(G, A) → H_c^n(G, B)` induced by `g : A ⟶ B`, local modules the restrictions. -/
noncomputable abbrev compactSupportCohomologyResMap {A B : Rep.{u} k G} [IsSmoothRep A]
    [IsSmoothRep B] (g : A ⟶ B) (n : ℕ) :
    compactSupportCohomologyRes φ A n ⟶ compactSupportCohomologyRes φ B n :=
  HomologicalComplex.homologyMap (compactSupportCochainsResMap φ g) n

variable {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] [IsSmoothRep C]

theorem compactSupportCochainsResMap_add (g₁ g₂ : A ⟶ B) :
    compactSupportCochainsResMap φ (g₁ + g₂) = compactSupportCochainsResMap φ g₁ + compactSupportCochainsResMap φ g₂ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A)) n) =>
      Prod.ext ?_ ?_)
  · exact congrArg (fun F => (F.f n).hom p.1) (cochainsMap_add g₁ g₂)
  · cases n with
    | zero => rfl
    | succ n =>
      refine funext fun v => ?_
      exact congrArg (fun F => (F.f n).hom (p.2 v)) (cochainsMap_add
        ((Rep.resFunctor (φ v : Hv v →* G)).map g₁) ((Rep.resFunctor (φ v : Hv v →* G)).map g₂))

theorem compactSupportCochainsResMap_zero :
    compactSupportCochainsResMap φ (0 : A ⟶ B) = 0 := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A)) n) =>
      Prod.ext ?_ ?_)
  · exact congrArg (fun F => (F.f n).hom p.1) (coeffCochainsMap_zero (A := A) (B := B))
  · cases n with
    | zero => rfl
    | succ n =>
      refine funext fun v => ?_
      exact congrArg (fun F => (F.f n).hom (p.2 v))
        (coeffCochainsMap_zero (A := Rep.res (φ v : Hv v →* G) A) (B := Rep.res (φ v : Hv v →* G) B))

theorem compactSupportCochainsResMap_id : compactSupportCochainsResMap φ (𝟙 A) = 𝟙 _ := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A)) n) =>
      Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compactSupportCochainsResMap_comp (g : A ⟶ B) (g' : B ⟶ C) :
    compactSupportCochainsResMap φ (g ≫ g') = compactSupportCochainsResMap φ g ≫ compactSupportCochainsResMap φ g' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : (cochains A).X n ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A)) n) =>
      Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compactSupportCohomologyResMap_add (g₁ g₂ : A ⟶ B) (n : ℕ) :
    compactSupportCohomologyResMap φ (g₁ + g₂) n =
      compactSupportCohomologyResMap φ g₁ n + compactSupportCohomologyResMap φ g₂ n := by
  rw [compactSupportCohomologyResMap, compactSupportCochainsResMap_add, HomologicalComplex.homologyMap_add]
  rfl

theorem compactSupportCohomologyResMap_zero (n : ℕ) : compactSupportCohomologyResMap φ (0 : A ⟶ B) n = 0 := by
  rw [compactSupportCohomologyResMap, compactSupportCochainsResMap_zero, HomologicalComplex.homologyMap_zero]
  rfl

theorem compactSupportCohomologyResMap_id (n : ℕ) : compactSupportCohomologyResMap φ (𝟙 A) n = 𝟙 _ := by
  rw [compactSupportCohomologyResMap, compactSupportCochainsResMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem compactSupportCohomologyResMap_comp (g : A ⟶ B) (g' : B ⟶ C) (n : ℕ) :
    compactSupportCohomologyResMap φ (g ≫ g') n =
      compactSupportCohomologyResMap φ g n ≫ compactSupportCohomologyResMap φ g' n := by
  rw [compactSupportCohomologyResMap, compactSupportCochainsResMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem compactSupportCohomologyResMap_finsetSum {J : Type*} (s : Finset J) (f : J → (A ⟶ B)) (m : ℕ) :
    compactSupportCohomologyResMap φ (∑ j ∈ s, f j) m = ∑ j ∈ s, compactSupportCohomologyResMap φ (f j) m := by
  classical
  induction s using Finset.induction with
  | empty => simp [compactSupportCohomologyResMap_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, compactSupportCohomologyResMap_add, ih]

theorem nsmul_compactSupportCohomologyRes_eq_zero {m : ℕ} (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : compactSupportCohomologyRes φ A n) : m • x = 0 := by
  have h0 : (∑ _j ∈ Finset.range m, 𝟙 A) = 0 := by
    rw [Finset.sum_const, Finset.card_range]
    ext a
    exact hm a
  have e : (compactSupportCohomologyResMap φ (∑ _j ∈ Finset.range m, 𝟙 A) n).hom x =
      (compactSupportCohomologyResMap φ (0 : A ⟶ A) n).hom x := by rw [h0]
  rw [compactSupportCohomologyResMap_finsetSum, compactSupportCohomologyResMap_zero] at e
  simp only [compactSupportCohomologyResMap_id, Finset.sum_const, Finset.card_range] at e
  simpa using e

end ResMap

section CupNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem cupCochain_naturality {X X' Y Y' Z : Rep.{u} k G} (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y' ⟶ Z)
    (α : X' ⟶ X) (β : Y ⟶ Y') (hν : (α ⊗ₘ 𝟙 Y) ≫ ν = (𝟙 X' ⊗ₘ β) ≫ ν') {r s n : ℕ}
    (h : r + s = n) (F : (Fin r → G) → X') (E : (Fin s → G) → Y) (σ : Fin n → G) :
    ν'.hom (cupCochain h F (fun τ => β.hom (E τ)) σ) =
      ν.hom (cupCochain h (fun τ => α.hom (F τ)) E σ) :=
  (cupCochain_tensorHom_eq ((α ⊗ₘ 𝟙 Y) ≫ ν) ν' β hν h F E σ).symm.trans
    (cupCochain_tensorHom_eq' _ ν α rfl h F E σ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem resFunctor_map_naturality {K : Type u} [Group K] (ψ : K →* G)
    {X X' Y Y' Z : Rep.{u} k G} (ν : X ⊗ Y ⟶ Z) (ν' : X' ⊗ Y' ⟶ Z) (α : X' ⟶ X) (β : Y ⟶ Y')
    (hν : (α ⊗ₘ 𝟙 Y) ≫ ν = (𝟙 X' ⊗ₘ β) ≫ ν') :
    ((Rep.resFunctor ψ).map α ⊗ₘ 𝟙 (Rep.res ψ Y)) ≫ (Rep.resFunctor ψ).map ν =
      (𝟙 (Rep.res ψ X') ⊗ₘ (Rep.resFunctor ψ).map β) ≫ (Rep.resFunctor ψ).map ν' := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact congrArg (fun F => F.hom (a ⊗ₜ[k] b : (X' ⊗ Y : Rep k G))) hν
  | add x y hx hy => simp only [map_add, hx, hy]

variable {A A' B B' C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep A'] [IsSmoothRep B]
  [IsSmoothRep B'] [IsSmoothRep C]

/-- The Leibniz pairing defining `compactCupRes`. -/
noncomputable abbrev compactCupResLeibniz (μ : A ⊗ B ⟶ C) :
    LeibnizPairing (compactSupportCochains φ A (fun v => Rep.res (φ v : Hv v →* G) A) (fun _ => 𝟙 _))
      (cochains B)
      (compactSupportCochains φ C (fun v => Rep.res (φ v : Hv v →* G) C) (fun _ => 𝟙 _)) :=
  compactCupLeibniz φ μ (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map μ)
    (fun v => resFunctor_map_comp_id (φ v : Hv v →* G) μ)

theorem compactCupRes_eq_homology (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    compactCupRes φ μ h = (compactCupResLeibniz φ μ).homology h :=
  rfl

theorem compactCupRes_compactSupportCohomologyResMap (μ : A ⊗ B ⟶ C) (μ' : A' ⊗ B' ⟶ C) (g : A' ⟶ A)
    (f : B ⟶ B') (hμ : (g ⊗ₘ 𝟙 B) ≫ μ = (𝟙 A' ⊗ₘ f) ≫ μ') {r s n : ℕ} (h : r + s = n)
    (y : compactSupportCohomologyRes φ A' r) (x : cohomology B s) :
    compactCupRes φ μ h ((compactSupportCohomologyResMap φ g r).hom y) x =
      compactCupRes φ μ' h y ((coeffMap f s).hom x) := by
  rw [compactCupRes_eq_homology, compactCupRes_eq_homology]
  refine (LeibnizPairing.homology_homologyMap (compactCupResLeibniz φ μ')
    (compactCupResLeibniz φ μ) (compactSupportCochainsResMap φ g) (coeffCochainsMap f) ?_ h y x).symm
  intro r s n h p z
  revert p
  intro (p : (cochains A').X r ×
    shiftNegOneX (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A')) r)
  obtain ⟨x0, b⟩ := p
  refine Prod.ext ?_ ?_
  · apply cochainOf_injective
    funext σ
    exact cupCochain_naturality μ μ' g f hμ h (cochainOf _ x0) (cochainOf _ z) σ
  · cases r with
    | zero => rfl
    | succ r =>
      cases n with
      | zero => rfl
      | succ m =>
        revert b
        intro (b : (piComplex fun v => cochains (Rep.res (φ v : Hv v →* G) A')).X r)
        refine funext fun v => ?_
        apply cochainOf_injective
        funext σ
        exact cupCochain_naturality ((Rep.resFunctor (φ v : Hv v →* G)).map μ)
          ((Rep.resFunctor (φ v : Hv v →* G)).map μ') ((Rep.resFunctor (φ v : Hv v →* G)).map g)
          ((Rep.resFunctor (φ v : Hv v →* G)).map f)
          (resFunctor_map_naturality (φ v : Hv v →* G) μ μ' g f hμ) (show r + s = m by omega)
          (cochainOf _ (b v)) (fun τ => cochainOf B z (⇑(φ v : Hv v →* G) ∘ τ)) σ

end CupNatural

section DualityNatural

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (D : Rep.{u} k G) [IsSmoothRep D]
  {n m r s : ℕ} (h : r + s = m) (t : compactSupportCohomologyRes φ D m →+ ZMod n)

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem tensorHom_dualEvalPairing {A B : Rep.{u} k G} (f : A ⟶ B) :
    (dualMap D f ⊗ₘ 𝟙 A) ≫ dualEvalPairing D A = (𝟙 (dualRep D B) ⊗ₘ f) ≫ dualEvalPairing D B := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compactDualityMap_cohomologyMap {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep (dualRep D A)] [IsSmoothRep (dualRep D B)] (f : A ⟶ B)
    (x : cohomology A r) (y : compactSupportCohomologyRes φ (dualRep D B) s) :
    compactDualityMap φ D h t B ((coeffMap f r).hom x) y =
      compactDualityMap φ D h t A x ((compactSupportCohomologyResMap φ (dualMap D f) s).hom y) := by
  rw [compactDualityMap_apply, compactDualityMap_apply,
    compactCupRes_compactSupportCohomologyResMap φ (dualEvalPairing D A) (dualEvalPairing D B)
      (dualMap D f) f (tensorHom_dualEvalPairing D f)]

theorem bijective_compactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, IsSmoothRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsSmoothRep P] [IsSmoothRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (compactDualityMap φ D h t (X j))) :
    Function.Bijective (compactDualityMap φ D h t P) := by
  have hdecomp : ∀ x : cohomology P r,
      x = ∑ j, (coeffMap (i j) r).hom ((coeffMap (p j) r).hom x) := by
    intro x
    have e := congrArg (fun φ => (coeffMap φ r).hom x) hsum
    simp only [cohomologyMap_finsetSum, coeffMap_id, coeffMap_comp, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at e
    exact e.symm
  have hdual : ∀ y : compactSupportCohomologyRes φ (dualRep D P) s,
      ∑ j, (compactSupportCohomologyResMap φ (dualMap D (p j)) s).hom
        ((compactSupportCohomologyResMap φ (dualMap D (i j)) s).hom y) = y := by
    intro y
    have e := congrArg (fun F => (compactSupportCohomologyResMap φ (dualMap D F) s).hom y) hsum
    simp only [dualMap_finsetSum, dualMap_comp, compactSupportCohomologyResMap_finsetSum, dualMap_id,
      compactSupportCohomologyResMap_id, compactSupportCohomologyResMap_comp, ModuleCat.hom_sum,
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
      rw [AddMonoidHom.zero_apply, compactDualityMap_cohomologyMap, hx, AddMonoidHom.zero_apply]
    rw [hdecomp x]
    simp [hj]
  · intro χ
    choose a ha using fun j => (hX j).2
      (χ.comp (compactSupportCohomologyResMap φ (dualMap D (p j)) s).hom.toAddMonoidHom)
    refine ⟨∑ j, (coeffMap (i j) r).hom (a j), ?_⟩
    ext y
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    conv_rhs => rw [← hdual y, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [compactDualityMap_cohomologyMap, ha j]
    rfl

theorem bijective_compactDualityMap_biproduct {J : Type} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, Finite (X j)]
    (hX : ∀ j, Function.Bijective (compactDualityMap φ D h t (X j))) :
    Function.Bijective (compactDualityMap φ D h t (⨁ X)) :=
  bijective_compactDualityMap_of_sum φ D h t X (⨁ X) (biproduct.ι X) (biproduct.π X)
    (biproduct.total (f := X)) hX

end DualityNatural

end

end Natural

end Langlands.GaloisCohomology
