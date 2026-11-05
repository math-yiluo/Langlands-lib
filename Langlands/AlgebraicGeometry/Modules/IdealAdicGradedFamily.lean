import Langlands.AlgebraicGeometry.Modules.IdealAdicScalarAction
import Langlands.AlgebraicGeometry.Modules.IdealAdicMultipleSections
import Langlands.AlgebraicGeometry.Modules.ActionFamily

/-! # The graded family of ideal-adic layers and uniform vanishing of its twists -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

open IntegralIdealFiltration (secHom)
open DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

lemma smulEnd_mul (a b : R) (M : X.Modules) :
    smulEnd f (a * b) M = smulEnd f b M ≫ smulEnd f a M := by
  ext U x
  change scalar f U (a * b) • x = scalar f U a • scalar f U b • x
  rw [map_mul, mul_smul]

/-- Multiplication by `a` from the multiple `IM` to the multiple `KM`, when `aI ⊆ K`. -/
def mulMultiple (a : R) {I K : Ideal R} (h : ∀ b ∈ I, a * b ∈ K) (M : X.Modules) :
    multiple f I M ⟶ multiple f K M :=
  Abelian.monoLift (inclusion f K M) (inclusion f I M ≫ smulEnd f a M) (by
    rw [Category.assoc]
    change inclusion f I M ≫ smulEnd f a M ≫ projection f K M = 0
    rw [inclusion_comp_eq_zero_iff]
    intro U b hb m
    have h0 := congrArg (fun φ => φ.app U m) (smulEnd_projection f K M (h b hb))
    rw [smulEnd_mul, Category.assoc] at h0
    exact h0)

@[reassoc (attr := simp)]
lemma mulMultiple_inclusion (a : R) {I K : Ideal R} (h : ∀ b ∈ I, a * b ∈ K)
    (M : X.Modules) :
    mulMultiple f a h M ≫ inclusion f K M = inclusion f I M ≫ smulEnd f a M :=
  Abelian.monoLift_comp _ _ _

/-- Multiplication maps commute with the maps induced by inclusions of ideals. -/
@[reassoc]
lemma multipleMap_mulMultiple (a : R) {I I' K K' : Ideal R} (hI : I ≤ I') (hK : K ≤ K')
    (h : ∀ b ∈ I, a * b ∈ K) (h' : ∀ b ∈ I', a * b ∈ K') (M : X.Modules) :
    multipleMap f hI M ≫ mulMultiple f a h' M = mulMultiple f a h M ≫ multipleMap f hK M := by
  rw [← cancel_mono (inclusion f K' M)]
  simp

/-- Multiplication maps by two scalars commute. -/
@[reassoc]
lemma mulMultiple_comm (a b : R) {I K K' L : Ideal R} (ha : ∀ c ∈ I, a * c ∈ K)
    (hb : ∀ c ∈ K, b * c ∈ L) (hb' : ∀ c ∈ I, b * c ∈ K') (ha' : ∀ c ∈ K', a * c ∈ L)
    (M : X.Modules) :
    mulMultiple f a ha M ≫ mulMultiple f b hb M =
      mulMultiple f b hb' M ≫ mulMultiple f a ha' M := by
  rw [← cancel_mono (inclusion f L M)]
  simp only [Category.assoc, mulMultiple_inclusion, mulMultiple_inclusion_assoc]
  rw [smulEnd_naturality f a (smulEnd f b M)]

/-- On an ideal multiple, a base scalar factors through a smaller ideal multiple. -/
lemma smulEnd_multiple (a : R) {I K : Ideal R} (h : ∀ b ∈ I, a * b ∈ K) (hK : K ≤ I)
    (M : X.Modules) :
    smulEnd f a (multiple f I M) = mulMultiple f a h M ≫ multipleMap f hK M := by
  rw [← cancel_mono (inclusion f I M), smulEnd_naturality, Category.assoc,
    multipleMap_inclusion, mulMultiple_inclusion]

lemma mul_mem_pow_succ {J : Ideal R} {a : R} (ha : a ∈ J) (n : ℕ) :
    ∀ b ∈ J ^ n, a * b ∈ J ^ (n + 1) := fun b hb => by
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha hb

/-- Multiplication by `a ∈ J` from `JⁿM / Jⁿ⁺¹M` to `Jⁿ⁺¹M / Jⁿ⁺²M`. -/
def layerMul {J : Ideal R} {a : R} (ha : a ∈ J) (M : X.Modules) (n : ℕ) :
    adicLayer f J M n ⟶ adicLayer f J M (n + 1) :=
  cokernel.map _ _ (mulMultiple f a (mul_mem_pow_succ ha (n + 1)) M)
    (mulMultiple f a (mul_mem_pow_succ ha n) M) (multipleMap_mulMultiple f a _ _ _ _ M)

@[reassoc (attr := simp)]
lemma π_layerMul {J : Ideal R} {a : R} (ha : a ∈ J) (M : X.Modules) (n : ℕ) :
    cokernel.π (multipleMap f (Ideal.pow_le_pow_right (Nat.le_succ n)) M) ≫
        layerMul f ha M n =
      mulMultiple f a (mul_mem_pow_succ ha n) M ≫
        cokernel.π (multipleMap f (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) M) :=
  cokernel.π_desc _ _ _

/-- The layers `JⁿM / Jⁿ⁺¹M` with the multiplications by finitely many elements of `J`. -/
def gradedFamily (J : Ideal R) {r : ℕ} (g : Fin r → R) (hg : ∀ j, g j ∈ J)
    (M : X.Modules) : ActionFamily X r where
  obj n := adicLayer f J M n
  act j n := layerMul f (hg j) M n
  comm i j n := by
    apply coequalizer.hom_ext
    have h := mulMultiple_comm f (g j) (g i) (mul_mem_pow_succ (hg j) n)
      (mul_mem_pow_succ (hg i) (n + 1)) (mul_mem_pow_succ (hg i) n)
      (mul_mem_pow_succ (hg j) (n + 1)) M
    simp [reassoc_of% h]

/-- Quasi-coherent modules with finite affine sections on which every element of `J`
acts by zero. -/
def AnnihilatedCoherent (J : Ideal R) (G : X.Modules) : Prop :=
  G.IsQuasicoherent ∧ HasFiniteAffineSections G ∧ ∀ a ∈ J, smulEnd f a G = 0

lemma annihilatedCoherent_kernel [IsLocallyNoetherian X] {J : Ideal R} {G H : X.Modules}
    (φ : G ⟶ H) (hG : AnnihilatedCoherent f J G) (hH : AnnihilatedCoherent f J H) :
    AnnihilatedCoherent f J (kernel φ) := by
  obtain ⟨hGq, hGf, hGa⟩ := hG
  obtain ⟨hHq, -, -⟩ := hH
  refine ⟨QuasicoherentLocal.isQuasicoherent_kernel φ, HasFiniteAffineSections.kernel φ hGf,
    fun a ha => ?_⟩
  rw [← cancel_mono (kernel.ι φ), smulEnd_naturality, hGa a ha, comp_zero, zero_comp]

lemma annihilatedCoherent_cokernel {J : Ideal R} {G H : X.Modules}
    (φ : G ⟶ H) (hG : AnnihilatedCoherent f J G) (hH : AnnihilatedCoherent f J H) :
    AnnihilatedCoherent f J (cokernel φ) := by
  obtain ⟨hGq, -, -⟩ := hG
  obtain ⟨hHq, hHf, hHa⟩ := hH
  refine ⟨QuasicoherentLocal.isQuasicoherent_cokernel φ,
    HasFiniteAffineSections.cokernel φ hHf, fun a ha => ?_⟩
  rw [← cancel_epi (cokernel.π φ), ← smulEnd_naturality, hHa a ha, zero_comp, comp_zero]

/-- The layers of a quasi-coherent module with finite affine sections are annihilated
by `J` and lie in the same class. -/
lemma annihilatedCoherent_adicLayer [IsLocallyNoetherian X] (J : Ideal R) (hJ : J.FG)
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M) (n : ℕ) :
    AnnihilatedCoherent f J (adicLayer f J M n) := by
  have := isQuasicoherent_multiple f (J ^ n) M (Ideal.FG.pow hJ)
  have := isQuasicoherent_multiple f (J ^ (n + 1)) M (Ideal.FG.pow hJ)
  refine ⟨QuasicoherentLocal.isQuasicoherent_cokernel _,
    HasFiniteAffineSections.cokernel _
      (HasFiniteAffineSections.of_mono (inclusion f (J ^ n) M) hM), fun a ha => ?_⟩
  have hπ := smulEnd_naturality f a
    (cokernel.π (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n)) M))
  rw [smulEnd_multiple f a (mul_mem_pow_succ ha n) (Ideal.pow_le_pow_right (Nat.le_succ n)),
    Category.assoc, cokernel.condition, comp_zero] at hπ
  rw [← cancel_epi
    (cokernel.π (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n)) M)), comp_zero]
  exact hπ.symm

/-- On affine opens, the multiplications by generators of `J` generate the sections of
every layer from the previous layer. -/
lemma isGeneratedOn_gradedFamily {ι : Type u} {U : ι → X.Opens}
    (hU : ∀ l, IsAffineOpen (U l)) (J : Ideal R) {r : ℕ} (g : Fin r → R)
    (hg : ∀ j, g j ∈ J) (hJ : J ≤ Ideal.span (Set.range g)) (M : X.Modules)
    [M.IsQuasicoherent] : (gradedFamily f J g hg M).IsGeneratedOn U := by
  classical
  have hJeq : J = Ideal.span (Set.range g) :=
    le_antisymm hJ (Ideal.span_le.2 (Set.range_subset_iff.2 hg))
  have hfg : ∀ k, (J ^ k).FG := fun k =>
    Ideal.FG.pow (hJeq ▸ Submodule.fg_span (Set.finite_range g))
  refine ⟨0, fun n _ l => ?_⟩
  have hV := hU l
  have := isQuasicoherent_multiple f (J ^ (n + 1)) M (hfg _)
  have := isQuasicoherent_multiple f (J ^ (n + 1 + 1)) M (hfg _)
  have := QuasicoherentLocal.isQuasicoherent_cokernel
    (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) M)
  rw [eq_top_iff]
  rintro s -
  obtain ⟨t, rfl⟩ := QuasicoherentLocal.surjective_app_of_epi
    (cokernel.π (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) M))
    (U l) hV s
  let W := ⨆ i, LinearMap.range (secHom ((gradedFamily f J g hg M).act i n) (U l))
  let π' := secHom
    (cokernel.π (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ (n + 1))) M)) (U l)
  let ι' := secHom (inclusion f (J ^ (n + 1)) M) (U l)
  let S : Submodule Γ(X, U l) Γ(M, U l) := (W.comap π').map ι'
  have hgen : ∀ c ∈ J ^ (n + 1), ∀ m : Γ(M, U l), scalar f (U l) c • m ∈ S := by
    intro c hc
    rw [pow_succ'] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro a ha b hb
      refine Submodule.span_induction
        (p := fun a _ => ∀ b ∈ J ^ n, ∀ m : Γ(M, U l), scalar f (U l) (a * b) • m ∈ S)
        ?_ ?_ ?_ ?_ (hJ ha) b hb
      · rintro _ ⟨j, rfl⟩ b hb m
        obtain ⟨y, hy⟩ := (mem_range_inclusion_app_iff f (J ^ n) M (hfg n) hV
          (scalar f (U l) b • m)).2 (Submodule.subset_span ⟨b, hb, m, rfl⟩)
        refine ⟨(mulMultiple f (g j) (mul_mem_pow_succ (hg j) n) M).app (U l) y, ?_, ?_⟩
        · refine Submodule.mem_iSup_of_mem j ⟨secHom (cokernel.π
            (multipleMap f (Ideal.pow_le_pow_right (I := J) (Nat.le_succ n)) M)) (U l) y, ?_⟩
          change secHom (cokernel.π _ ≫ layerMul f (hg j) M n) (U l) y =
            secHom (mulMultiple f (g j) (mul_mem_pow_succ (hg j) n) M ≫ cokernel.π _) (U l) y
          rw [π_layerMul]
          rfl
        · change (mulMultiple f (g j) (mul_mem_pow_succ (hg j) n) M ≫
            inclusion f _ M).app (U l) y = _
          rw [mulMultiple_inclusion]
          change scalar f (U l) (g j) • (inclusion f (J ^ n) M).app (U l) y = _
          rw [hy, smul_smul, ← map_mul]
      · intro b _ m
        rw [zero_mul, map_zero, zero_smul]
        exact S.zero_mem
      · intro x y _ _ hx hy b hb m
        rw [add_mul, map_add, add_smul]
        exact S.add_mem (hx b hb m) (hy b hb m)
      · intro x y _ hy b hb m
        rw [show x • y * b = y * (x * b) by rw [smul_eq_mul]; ring]
        exact hy (x * b) (Ideal.mul_mem_left _ x hb) m
    · intro x y hx hy m
      rw [map_add, add_smul]
      exact S.add_mem (hx m) (hy m)
  have hle : ∀ x ∈ (multiplePresubmodule f (J ^ (n + 1)) M).obj (op (U l)), x ∈ S := by
    intro x hx
    refine Submodule.span_induction
      (p := fun (x : M.val.obj (op (U l))) _ => x ∈ S) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨c, hc, m, rfl⟩
      exact hgen c hc m
    · exact S.zero_mem
    · intro x y _ _ hx hy
      exact S.add_mem hx hy
    · intro a x _ hx
      exact S.smul_mem a hx
  obtain ⟨t', ht', heq⟩ := hle (ι' t)
    ((mem_range_inclusion_app_iff f (J ^ (n + 1)) M (hfg _) hV (ι' t)).1 ⟨t, rfl⟩)
  rw [inclusion_app_injective f _ M (U l) heq] at ht'
  exact ht'

/-- Uniform vanishing for the layers of a module. Let `T d` be exact functors such that
every module annihilated by `J` in the coherent class has vanishing higher cohomology
after `T d` for all large `d`. Then one bound on `d` works for all layers `JⁿM / Jⁿ⁺¹M`
and all positive degrees. -/
theorem exists_uniform_vanishing_adicLayer [IsNoetherian X] (J : Ideal R) (hJ : J.FG)
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (T : ℕ → X.Modules ⥤ X.Modules) [∀ d, (T d).PreservesZeroMorphisms]
    (hT : ∀ d (S : ShortComplex X.Modules), S.ShortExact → (S.map (T d)).ShortExact)
    (hserre : ∀ G, AnnihilatedCoherent f J G → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((T d).obj G))) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((T d).obj (adicLayer f J M n))) := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
  obtain ⟨ι, _, U, hU, hcov⟩ := IntegralIdealFiltration.exists_finite_affine_cover (X := X)
  have hgJ : ∀ j, g j ∈ J := fun j => by
    rw [← hg]
    exact Submodule.subset_span ⟨j, rfl⟩
  exact ActionFamily.exists_uniform_vanishing hU hcov f (AnnihilatedCoherent f J)
    (fun _ h => h.1) (fun _ h => h.2.1)
    (fun φ hG hH => annihilatedCoherent_kernel f φ hG hH)
    (fun φ hG hH => annihilatedCoherent_cokernel f φ hG hH) T hT hserre r
    (gradedFamily f J g hgJ M) (fun n => annihilatedCoherent_adicLayer f J hJ M hM n)
    (isGeneratedOn_gradedFamily f hU J g hgJ hg.ge M)

/-- Uniform vanishing for the layers of the powers of a locally free rank-one module. -/
theorem exists_uniform_vanishing_adicLayer_tensorPow [IsNoetherian X] (J : Ideal R)
    (hJ : J.FG) (N : X.Modules) (hN : Picard.IsLocallyFreeRankOne N)
    (hserre : ∀ G, AnnihilatedCoherent f J G → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj ((tensorBy (tensorPow N d)).obj G))) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n p : ℕ,
      IsZero ((relativeCohomology f (p + 1)).obj (adicLayer f J (tensorPow N d) n)) := by
  have : (structureSheaf X).IsQuasicoherent :=
    (Picard.LineBundle.trivial X).property.isQuasicoherent
  obtain ⟨d₀, hd₀⟩ := exists_uniform_vanishing_adicLayer f J hJ (structureSheaf X)
    (fun U => inferInstanceAs (Module.Finite Γ(X, U.1) Γ(X, U.1)))
    (fun d => tensorBy (tensorPow N d))
    (fun d S hS => shortExact_tensorBy S hS _ (SerreVanishing.rankOne_pow N hN d)) hserre
  refine ⟨d₀, fun d hd n p => ?_⟩
  exact (hd₀ d hd n p).of_iso ((relativeCohomology f (p + 1)).mapIso
    (layerTwistIso f (tensorPow N d) (SerreVanishing.rankOne_pow N hN d) _)).symm

end Langlands.AlgebraicGeometry.Modules.IdealAdic
