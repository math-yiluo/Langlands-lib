import Langlands.Algebra.GradedStableGeneration
import Langlands.AlgebraicGeometry.Modules.IntegralIdealFiltration.Filtered
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Good

/-! # Families of modules with commuting degree-raising actions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules

/-- A sequence of module sheaves with `r` pairwise commuting maps raising the degree. -/
structure ActionFamily (X : Scheme.{u}) (r : ℕ) where
  /-- The module in each degree. -/
  obj : ℕ → X.Modules
  /-- The `i`-th action from degree `n` to degree `n + 1`. -/
  act : Fin r → ∀ n, obj n ⟶ obj (n + 1)
  comm : ∀ i j n, act j n ≫ act i (n + 1) = act i n ≫ act j (n + 1)

namespace ActionFamily

open IntegralIdealFiltration (secHom)
open DerivedSections

variable {X : Scheme.{u}} {r : ℕ}

lemma secHom_comp_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (V : X.Opens)
    (x : Γ(M, V)) : secHom (φ ≫ ψ) V x = secHom ψ V (secHom φ V x) :=
  rfl

/-- Membership in the span of the ranges of finitely many linear maps. -/
lemma mem_iSup_range_iff {C A B : Type*} [CommRing C] [AddCommGroup A] [Module C A]
    [AddCommGroup B] [Module C B] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → A →ₗ[C] B) (y : B) :
    y ∈ ⨆ i, LinearMap.range (t i) ↔ ∃ x : κ → A, ∑ i, t i (x i) = y := by
  constructor
  · intro hy
    induction hy using Submodule.iSup_induction' with
    | mem i y hy =>
        obtain ⟨a, rfl⟩ := hy
        refine ⟨Pi.single i a, ?_⟩
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
          (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
        obtain ⟨x, rfl⟩ := hy
        obtain ⟨x', rfl⟩ := hz
        exact ⟨x + x', by simp [Finset.sum_add_distrib]⟩
  · rintro ⟨x, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x i, rfl⟩

/-- The kernels of the last action, with the remaining actions. -/
def ker (F : ActionFamily X (r + 1)) : ActionFamily X r where
  obj n := kernel (F.act (Fin.last r) n)
  act i n := kernel.map _ _ (F.act i.castSucc n) (F.act i.castSucc (n + 1))
    (F.comm i.castSucc (Fin.last r) n)
  comm i j n := by
    apply equalizer.hom_ext
    simp [F.comm]

@[reassoc (attr := simp)]
lemma ker_act_ι (F : ActionFamily X (r + 1)) (i : Fin r) (n : ℕ) :
    F.ker.act i n ≫ kernel.ι (F.act (Fin.last r) (n + 1)) =
      kernel.ι (F.act (Fin.last r) n) ≫ F.act i.castSucc n :=
  kernel.lift_ι _ _ _

/-- The cokernels of the last action, with the remaining actions. -/
def coker (F : ActionFamily X (r + 1)) : ActionFamily X r where
  obj n := cokernel (F.act (Fin.last r) n)
  act i n := cokernel.map _ _ (F.act i.castSucc n) (F.act i.castSucc (n + 1))
    (F.comm i.castSucc (Fin.last r) n)
  comm i j n := by
    apply coequalizer.hom_ext
    simp [reassoc_of% F.comm]

@[reassoc (attr := simp)]
lemma π_coker_act (F : ActionFamily X (r + 1)) (i : Fin r) (n : ℕ) :
    cokernel.π (F.act (Fin.last r) n) ≫ F.coker.act i n =
      F.act i.castSucc (n + 1) ≫ cokernel.π (F.act (Fin.last r) (n + 1)) :=
  cokernel.π_desc _ _ _

variable {ι : Type u} (U : ι → X.Opens)

/-- On each open of the family, the actions jointly generate the sections in
every degree above a fixed bound. -/
def IsGeneratedOn (F : ActionFamily X r) : Prop :=
  ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ l, ⨆ i, LinearMap.range (secHom (F.act i n) (U l)) = ⊤

variable {U}

/-- Generation passes to the kernel family over noetherian affine opens. -/
lemma isGeneratedOn_ker [IsLocallyNoetherian X] [Finite ι] (hU : ∀ l, IsAffineOpen (U l))
    (F : ActionFamily X (r + 1)) (hf : ∀ n, HasFiniteAffineSections (F.obj n))
    (hF : F.IsGeneratedOn U) : F.ker.IsGeneratedOn U := by
  classical
  obtain ⟨N₀, hN₀⟩ := hF
  have key : ∀ l, ∃ N₁ : ℕ, ∀ n, N₁ ≤ n →
      ⨆ i, LinearMap.range (secHom (F.ker.act i n) (U l)) = ⊤ := by
    intro l
    have := IsLocallyNoetherian.component_noetherian ⟨U l, hU l⟩
    have : ∀ n, Module.Finite Γ(X, U l) Γ(F.obj n, U l) := fun n => hf n ⟨U l, hU l⟩
    let t : Fin (r + 1) → ∀ n, Γ(F.obj n, U l) →ₗ[Γ(X, U l)] Γ(F.obj (n + 1), U l) :=
      fun i n => secHom (F.act i n) (U l)
    let K : ∀ n, Submodule Γ(X, U l) Γ(F.obj n, U l) :=
      fun n => LinearMap.ker (t (Fin.last r) n)
    have hcomm : ∀ i j n (x : Γ(F.obj n, U l)), t i (n + 1) (t j n x) = t j (n + 1) (t i n x) :=
      fun i j n x => by
        change secHom (F.act j n ≫ F.act i (n + 1)) (U l) x =
          secHom (F.act i n ≫ F.act j (n + 1)) (U l) x
        rw [F.comm]
    have hK : ∀ i n, (K n).map (t i n) ≤ K (n + 1) := by
      rintro i n _ ⟨x, hx, rfl⟩
      change t (Fin.last r) (n + 1) (t i n x) = 0
      rw [hcomm, show t (Fin.last r) n x = 0 from hx, map_zero]
    obtain ⟨N₁, hN₁⟩ := Langlands.Algebra.GradedStableGeneration.exists_stable_generation t hcomm N₀
      (fun n hn => hN₀ n hn l) K hK
    refine ⟨N₁, fun n hn => ?_⟩
    rw [eq_top_iff]
    rintro s -
    let ιK := fun m => secHom (kernel.ι (F.act (Fin.last r) m)) (U l)
    have hs : ιK (n + 1) s ∈ K (n + 1) :=
      QuasicoherentLocal.app_kernel_ι_app (F.act (Fin.last r) (n + 1)) (U l) s
    rw [hN₁ n hn] at hs
    have hle : ⨆ i, (K n).map (t i n) ≤
        (⨆ i, LinearMap.range (secHom (F.ker.act i n) (U l))).map (ιK (n + 1)) := by
      refine iSup_le fun i => ?_
      induction i using Fin.lastCases with
      | last =>
          rintro _ ⟨x, hx, rfl⟩
          rw [show t (Fin.last r) n x = 0 from hx]
          exact Submodule.zero_mem _
      | cast j =>
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨k, rfl⟩ := QuasicoherentLocal.exists_kernel_ι_app_eq _ x hx
          refine ⟨secHom (F.ker.act j n) (U l) k,
            Submodule.mem_iSup_of_mem j ⟨k, rfl⟩, ?_⟩
          change secHom (F.ker.act j n ≫ kernel.ι (F.act (Fin.last r) (n + 1))) (U l) k =
            secHom (kernel.ι (F.act (Fin.last r) n) ≫ F.act j.castSucc n) (U l) k
          rw [ker_act_ι]
          rfl
    obtain ⟨y, hy, hys⟩ := hle hs
    rw [QuasicoherentLocal.kernel_ι_app_injective _ (U l) hys] at hy
    exact hy
  choose N₁ hN₁ using key
  have := Fintype.ofFinite ι
  refine ⟨Finset.univ.sup N₁, fun n hn l => hN₁ l n ?_⟩
  exact (Finset.le_sup (Finset.mem_univ l)).trans hn

/-- Generation passes to the cokernel family over affine opens. -/
lemma isGeneratedOn_coker (hU : ∀ l, IsAffineOpen (U l))
    (F : ActionFamily X (r + 1)) (hq : ∀ n, (F.obj n).IsQuasicoherent)
    (hF : F.IsGeneratedOn U) : F.coker.IsGeneratedOn U := by
  classical
  obtain ⟨N₀, hN₀⟩ := hF
  refine ⟨N₀, fun n hn l => ?_⟩
  rw [eq_top_iff]
  rintro s -
  have := hq (n + 1)
  have := hq (n + 2)
  have := QuasicoherentLocal.isQuasicoherent_cokernel (F.act (Fin.last r) (n + 1))
  obtain ⟨y, rfl⟩ := QuasicoherentLocal.surjective_app_of_epi
    (cokernel.π (F.act (Fin.last r) (n + 1))) (U l) (hU l) s
  have hy : y ∈ ⨆ i, LinearMap.range (secHom (F.act i (n + 1)) (U l)) := by
    rw [hN₀ (n + 1) (by omega) l]
    trivial
  obtain ⟨x, rfl⟩ := (mem_iSup_range_iff _ _).1 hy
  change secHom (cokernel.π (F.act (Fin.last r) (n + 1))) (U l) _ ∈ _
  rw [map_sum, Fin.sum_univ_castSucc]
  have hlast : secHom (cokernel.π (F.act (Fin.last r) (n + 1))) (U l)
      (secHom (F.act (Fin.last r) (n + 1)) (U l) (x (Fin.last r))) = 0 := by
    rw [← secHom_comp_apply, cokernel.condition]
    rfl
  rw [hlast, add_zero]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j
    ⟨secHom (cokernel.π (F.act (Fin.last r) n)) (U l) (x j.castSucc), ?_⟩
  change secHom (cokernel.π (F.act (Fin.last r) n) ≫ F.coker.act j n) (U l) _ =
    secHom (F.act j.castSucc (n + 1) ≫ cokernel.π (F.act (Fin.last r) (n + 1))) (U l) _
  rw [π_coker_act]
  rfl

/-- Uniform vanishing of higher cohomology along a generated family. Let `P` be a class of
quasi-coherent modules with finite sections over affine opens, closed under kernels and
cokernels, and let `T d` be exact functors such that every module in `P` has vanishing higher
cohomology after `T d` for all large `d`. Then for a family whose modules lie in `P` and which
is generated on a finite affine open cover, one bound on `d` works in every degree `n`. -/
theorem exists_uniform_vanishing [IsLocallyNoetherian X] [Finite ι]
    (hU : ∀ l, IsAffineOpen (U l)) (hcov : ⨆ l, U l = ⊤)
    {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (P : X.Modules → Prop) (hPq : ∀ M, P M → M.IsQuasicoherent)
    (hPf : ∀ M, P M → HasFiniteAffineSections M)
    (hPker : ∀ {M N : X.Modules} (φ : M ⟶ N), P M → P N → P (kernel φ))
    (hPcoker : ∀ {M N : X.Modules} (φ : M ⟶ N), P M → P N → P (cokernel φ))
    (T : ℕ → X.Modules ⥤ X.Modules) [∀ d, (T d).PreservesZeroMorphisms]
    (hT : ∀ d (S : ShortComplex X.Modules), S.ShortExact → (S.map (T d)).ShortExact)
    (hserre : ∀ M, P M → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((T d).obj M)))
    (r : ℕ) (F : ActionFamily X r) (hP : ∀ n, P (F.obj n)) (hF : F.IsGeneratedOn U) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((T d).obj (F.obj n))) := by
  classical
  induction r with
  | zero =>
      obtain ⟨N₀, hN₀⟩ := hF
      choose e he using fun n => hserre (F.obj n) (hP n)
      refine ⟨(Finset.range (N₀ + 1)).sup e, fun d hd n p => ?_⟩
      by_cases hn : n ≤ N₀
      · exact he n d ((Finset.le_sup (Finset.mem_range.2 (by omega))).trans hd) p
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have := hPq _ (hP (m + 1))
        have hz : IsZero (F.obj (m + 1)) := by
          apply NoetherianVanishing.isZero_of_vanishesOn_top
          rw [← hcov]
          apply IntegralIdealFiltration.vanishesOn_iSup
          intro l
          apply IntegralIdealFiltration.vanishesOn_of_affine (hU l)
          intro t
          have ht : t ∈ ⨆ i : Fin 0, LinearMap.range (secHom (F.act i m) (U l)) := by
            rw [hN₀ m (by omega) l]
            trivial
          rw [iSup_of_empty] at ht
          exact (Submodule.mem_bot _).1 ht
        exact NoetherianVanishing.isZero_relativeCohomology_of_isZero f
          ((T d).map_isZero hz) (p + 1)
  | succ r ih =>
      obtain ⟨d₁, hd₁⟩ := ih F.ker (fun n => hPker _ (hP n) (hP (n + 1)))
        (isGeneratedOn_ker hU F (fun n => hPf _ (hP n)) hF)
      obtain ⟨d₂, hd₂⟩ := ih F.coker (fun n => hPcoker _ (hP n) (hP (n + 1)))
        (isGeneratedOn_coker hU F (fun n => hPq _ (hP n)) hF)
      obtain ⟨d₃, hd₃⟩ := hserre _ (hP 0)
      refine ⟨max d₁ (max d₂ d₃), fun d hd n => ?_⟩
      induction n with
      | zero => exact hd₃ d (by omega)
      | succ n ihn =>
          intro p
          exact SerreVanishing.isZero_cohomology_target f (T d) (hT d)
            (F.act (Fin.last r) n) (p + 1) (hd₁ d (by omega) n (p + 1))
            (hd₂ d (by omega) n p) (ihn p)

end ActionFamily

end Langlands.AlgebraicGeometry.Modules
