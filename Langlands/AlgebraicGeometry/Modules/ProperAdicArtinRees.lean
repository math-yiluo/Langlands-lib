import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Modules.ProperAdicCechKernelReduction
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Langlands.AlgebraicGeometry.Modules.PullbackFiniteAffineSections

/-! # A uniform Artin–Rees bound for Čech boundaries on proper schemes -/

noncomputable section

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

namespace Langlands.AlgebraicGeometry.Modules.ProperAdicArtinRees

section BaseChange

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
  (F : OModulePresheaf π) (S : Type u) [AddCommGroup S] [Module R S]

/-- The `Γ(V, U)`-module structure on `F(U) ⊗[R] S` through the first factor. -/
@[reducible] def baseChangeModuleSections (U : V.Opens) : Module Γ(V, U) (F.obj U ⊗[R] S) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  TensorProduct.leftModule

/-- The presheaf `U ↦ F(U) ⊗[R] S`, with restriction maps `res ⊗ id`. -/
def baseChange : OModulePresheaf π where
  obj U := F.obj U ⊗[R] S
  addCommGroup _ := inferInstance
  module _ := inferInstance
  moduleSections U := baseChangeModuleSections F S U
  isScalarTower U := by
    let := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact TensorProduct.isScalarTower_left
  res h := LinearMap.rTensor S (F.res h)
  res_smul {U U'} h a t := by
    let := baseChangeModuleSections F S U
    let := baseChangeModuleSections F S U'
    induction t using TensorProduct.inductionOn with
    | tmul x s => exact congrArg (· ⊗ₜ[R] s) (F.res_smul h a x)
    | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add]
  res_refl U := by rw [F.res_refl, LinearMap.rTensor_id]
  res_comp h h' := by rw [F.res_comp, LinearMap.rTensor_comp]

lemma baseChange_res_tmul {U U' : V.Opens} (h : U ≤ U') (x : F.obj U') (s : S) :
    (baseChange F S).res h (show (baseChange F S).obj U' from x ⊗ₜ[R] s) =
      (show (baseChange F S).obj U from F.res h x ⊗ₜ[R] s) := rfl

lemma baseChange_smul_tmul (U : V.Opens) (a : Γ(V, U)) (x : F.obj U) (s : S) :
    a • (show (baseChange F S).obj U from x ⊗ₜ[R] s) =
      (show (baseChange F S).obj U from (a • x) ⊗ₜ[R] s) := rfl

variable (s₀ : S)

/-- The map `x ↦ x ⊗ s₀` into the base change. -/
def toBaseChange : OModulePresheaf.Hom F (baseChange F S) where
  app U := (TensorProduct.mk R (F.obj U) S).flip s₀
  app_smul _ _ _ := rfl
  naturality _ := LinearMap.ext fun _ => rfl

lemma toBaseChange_app (U : V.Opens) (x : F.obj U) :
    (toBaseChange F S s₀).app U x = (show (baseChange F S).obj U from x ⊗ₜ[R] s₀) := rfl

/-- The image of `x ↦ x ⊗ s₀` has finite sections on affine opens if `F` does. -/
lemma isCoherent_im_toBaseChange (hF : F.IsCoherent) :
    (OModulePresheaf.im (toBaseChange F S s₀)).IsCoherent := fun U => by
  have := hF U
  exact Module.Finite.of_surjective
    ((OModulePresheaf.kerImSES (toBaseChange F S s₀)).proj.appSections U.1)
    ((OModulePresheaf.kerImSES (toBaseChange F S s₀)).surjective U.1)

/-- Sections of the base change that vanish on a basic open are killed by a power of the
function, if `F` is quasi-coherent. -/
lemma exists_pow_smul_eq_zero_baseChange (hF : F.IsQuasicoherent) (U : V.affineOpens)
    (f : Γ(V, U.1)) (t : (baseChange F S).obj U.1)
    (ht : (baseChange F S).res (V.basicOpen_le f) t = 0) :
    ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • t = 0 := by
  obtain ⟨hsurj, hker⟩ := hF U f
  have hle : V.basicOpen f ≤ U.1 := V.basicOpen_le f
  let : Algebra R Γ(V, U.1) := Scheme.TwoAffineOpenCover.algebraOfHom π U.1
  let : Algebra Γ(V, U.1) Γ(V, V.basicOpen f) := (V.presheaf.map (homOfLE hle).op).hom.toAlgebra
  let : Module Γ(V, U.1) (F.obj (V.basicOpen f)) :=
    Module.compHom _ (V.presheaf.map (homOfLE hle).op).hom
  have : IsScalarTower Γ(V, U.1) Γ(V, V.basicOpen f) (F.obj (V.basicOpen f)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsScalarTower R Γ(V, U.1) (F.obj (V.basicOpen f)) := by
    let : Algebra R Γ(V, V.basicOpen f) := Scheme.TwoAffineOpenCover.algebraOfHom π _
    have := F.isScalarTower (V.basicOpen f)
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    change (V.presheaf.map (homOfLE hle).op).hom (algebraMap R Γ(V, U.1) r) • x = r • x
    rw [show (V.presheaf.map (homOfLE hle).op).hom (algebraMap R Γ(V, U.1) r) =
      algebraMap R Γ(V, V.basicOpen f) r from
        (Scheme.TwoAffineOpenCover.restrictAlgHom π hle).commutes r]
    exact algebraMap_smul Γ(V, V.basicOpen f) r x
  have hU := U.2
  have := hU.isLocalization_basicOpen f
  let g : F.obj U.1 →ₗ[Γ(V, U.1)] F.obj (V.basicOpen f) :=
    { toFun := F.res hle
      map_add' := map_add _
      map_smul' := F.res_smul hle }
  have : IsLocalizedModule (Submonoid.powers f) g := by
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
    · rw [← (Algebra.lsmul Γ(V, U.1) (A := Γ(V, V.basicOpen f)) Γ(V, U.1)
        (F.obj (V.basicOpen f))).commutes]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(V, V.basicOpen f)) f).map _
    · intro x
      obtain ⟨n, y, hy⟩ := hsurj x
      refine ⟨n, y, ?_⟩
      exact hy.symm
    · exact hker
  have : IsLocalizedModule (Submonoid.powers f) (AlgebraTensorModule.rTensor R S g) :=
    inferInstance
  have key : ∀ t' : F.obj U.1 ⊗[R] S,
      AlgebraTensorModule.rTensor R S g t' = LinearMap.rTensor S (F.res hle) t' := by
    intro t'
    induction t' using TensorProduct.inductionOn with
    | tmul x s => rfl
    | add t t' h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hg : AlgebraTensorModule.rTensor R S g (show F.obj U.1 ⊗[R] S from t) =
      AlgebraTensorModule.rTensor R S g 0 := by
    rw [map_zero, key]
    exact ht
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) hg
  rw [smul_zero] at hc
  exact ⟨n, hc⟩

/-- The image of `x ↦ x ⊗ s₀` is quasi-coherent in the sense of the FLT presheaves if `F` is. -/
lemma isQuasicoherent_im_toBaseChange (hF : F.IsQuasicoherent) :
    (OModulePresheaf.im (toBaseChange F S s₀)).IsQuasicoherent := by
  intro U f
  have hle : V.basicOpen f ≤ U.1 := V.basicOpen_le f
  constructor
  · intro x
    obtain ⟨y, hy⟩ := x.2
    obtain ⟨n, y₀, hy₀⟩ := (hF U f).1 y
    refine ⟨n, ⟨_, y₀, rfl⟩, Subtype.ext ?_⟩
    change (show (baseChange F S).obj (V.basicOpen f) from F.res hle y₀ ⊗ₜ[R] s₀) = _
    rw [hy₀]
    change _ = ((V.presheaf.map (homOfLE hle).op).hom (f ^ n)) • x.1
    rw [← hy]
    rfl
  · intro y hy
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_baseChange F S hF U f y.1
      (congrArg Subtype.val hy)
    exact ⟨n, Subtype.ext hn⟩

end BaseChange

open scoped P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.SolKS
open P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_d_of_forall_d_mem_pow_of_isProper.SolKS
open Polynomial Langlands.Scheme.Modules

section Rees

variable {A : Type u} [CommRing A] (I : Ideal A) {P : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) (M : P.Modules)

/-- Polynomials over `A` as an algebra over the Rees algebra `⊕ₙ Iⁿ`. -/
@[reducible] def reesPolynomialAlgebra : Algebra (Rr I) A[X] := (Rr.incl I).toAlgebra

attribute [local instance] reesPolynomialAlgebra

/-- The pullback of `M` to `P' = P ×_A Spec (⊕ₙ Iⁿ)`. -/
abbrev reesPullback : (P' I q).Modules := (Scheme.Modules.pullback (fst' I q)).obj M

/-- Sections of the pullback of `M`, as an FLT presheaf over the Rees algebra. -/
abbrev reesPullbackPresheaf : OModulePresheaf (π' I q) :=
  OModulePresheaf.ofModules (π' I q) (reesPullback I q M)

/-- The presheaf `W ↦ Γ(W, fst'^* M) ⊗_{⊕ Iⁿ} A[X]`. -/
abbrev reesTensor : OModulePresheaf (π' I q) := baseChange (reesPullbackPresheaf I q M) A[X]

/-- The Rees presheaf: the image of `x ↦ x ⊗ 1` from the pullback of `M`. -/
abbrev reesPresheaf : OModulePresheaf (π' I q) :=
  OModulePresheaf.im (toBaseChange (reesPullbackPresheaf I q M) A[X] 1)

lemma fst_appLE_alg {W : (P' I q).Opens} {U : P.Opens} (e : W ≤ fst' I q ⁻¹ᵁ U) (a : A) :
    ((fst' I q).appLE U W e).hom (alg q U a) = algR I q W (algebraMap A (Rr I) a) := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A (Rr I)))
  have h1 := congrArg (fun ψ : CommRingCat.of A ⟶ _ => ψ.hom a) hn
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h1
  have hL : q.appLE ⊤ U le_top ≫ (fst' I q).appLE U W e =
      (fst' I q ≫ q).appLE ⊤ W le_top := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hR : (sA I).appLE ⊤ ⊤ le_top ≫ (π' I q).appLE ⊤ W le_top =
      (π' I q ≫ sA I).appLE ⊤ W le_top := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [alg, algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [h1, ← appLE_top_top]
  change (q.appLE ⊤ U le_top ≫ (fst' I q).appLE U W e).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
    ((sA I).appLE ⊤ ⊤ le_top ≫ (π' I q).appLE ⊤ W le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [hL, hR]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
    (appLE_congr_hom (isPullback_P' I q).w ⊤ W _ _)

/-- Ideal multiples of module sections are stable under functions. -/
lemma smul_mem_ideal_smul_top {U : P.Opens} (J : Ideal A) (d : Γ(P, U))
    {x : (OModulePresheaf.ofModules q M).obj U}
    (hx : x ∈ J • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj U))) :
    d • x ∈ J • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj U)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom q U
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha m _
    rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro x y hx hy
    rw [smul_add]
    exact add_mem hx hy

/-- Products with functions in the image of an ideal lie in the ideal multiple. -/
lemma mem_ideal_smul_top_of_mem_map {U : P.Opens} (J : Ideal A) {c : Γ(P, U)}
    (hc : c ∈ J.map (alg q U)) (m : Γ(M, U)) :
    (show (OModulePresheaf.ofModules q M).obj U from c • m) ∈
      J • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj U)) := by
  unfold Ideal.map at hc
  induction hc using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, rfl⟩ := h
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  | zero =>
    rw [zero_smul]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [add_smul]
    exact add_mem hx hy
  | smul d x _ hx =>
    rw [smul_eq_mul, mul_smul]
    exact smul_mem_ideal_smul_top q M J d hx

variable [IsSeparated q] (K : P.OrderedAffineCover)

/-- Sections of `𝒪_{P'}` over a Čech intersection, as polynomials over sections of `𝒪_P`. -/
def reesRho {i : ℕ} (s : K.Idx i) :
    Γ(P' I q, (K' I q K).inter s) →+* Γ(P, K.inter s)[X] :=
  (ΦC I q K s).toRingHom.comp
    ((g I q).appLE ((K' I q K).inter s) (g I q ⁻¹ᵁ (K' I q K).inter s) le_rfl).hom

lemma reesRho_fst {i : ℕ} (s : K.Idx i) (c : Γ(P, K.inter s)) :
    reesRho I q K s (((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c) =
      C c := by
  change ΦC I q K s (((g I q).appLE _ _ le_rfl).hom
    (((fst' I q).appLE (K.inter s) ((K' I q K).inter s) (e'_s I q K s)).hom c)) = C c
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← θ_C I q _ _ (e_s I q K s), ΦC_θ]

lemma reesRho_algR {i : ℕ} (s : K.Idx i) (r : Rr I) :
    reesRho I q K s (algR I q _ r) = Polynomial.map (alg q (K.inter s)) (Rr.val I r) := by
  change ΦC I q K s (((g I q).appLE _ _ le_rfl).hom (algR I q _ r)) = _
  rw [g_appLE_algR, ΦC_algR₁]

lemma reesRho_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (x : Γ(P' I q, (K' I q K).inter (K.face s j))) :
    reesRho I q K s ((P' I q).presheaf.map (homOfLE ((K' I q K).inter_le_inter_face s j)).op x) =
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom
        (reesRho I q K (K.face s j) x) := by
  exact (congrArg (ΦC I q K s)
    (g_appLE_res I q ((K' I q K).inter_le_inter_face s j) x).symm).trans (ΦC_res I q K s j _)

lemma reesRho_mem {i : ℕ} (s : K.Idx i) (x : Γ(P' I q, (K' I q K).inter s)) :
    reesRho I q K s x ∈ reesAlgebra (I.map (alg q (K.inter s))) := by
  set J : Ideal Γ(P, K.inter s) := I.map (alg q (K.inter s)) with hJ
  let S : Subring Γ(P' I q, (K' I q K).inter s) :=
    (reesAlgebra J).toSubring.comap (reesRho I q K s)
  have hS : Subring.closure (Set.range ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
      (e'_s I q K s)).hom ∪ Set.range ((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom) ≤ S := by
    rw [Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨r₀, rfl⟩)
    · change reesRho I q K s _ ∈ reesAlgebra J
      rw [reesRho_fst]
      exact Subalgebra.algebraMap_mem (reesAlgebra J) c
    · change reesRho I q K s _ ∈ reesAlgebra J
      have hr₀ : r₀ = (Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).hom.hom r₀) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [hr₀]
      change reesRho I q K s (algR I q _ _) ∈ _
      rw [reesRho_algR]
      intro n
      rw [coeff_map, hJ, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Rr.coeff_mem I _ n)
  rw [closure_eq_top I q (haff q K s) (hW' I q K s)] at hS
  exact hS (Subring.mem_top x)

lemma reesInter_isAffineOpen {i : ℕ} (s : K.Idx i) : IsAffineOpen ((K' I q K).inter s) := by
  rw [K'_inter]
  exact (haff q K s).preimage _

/-- Section pullback of `M` to a Čech intersection of `P'`. -/
abbrev reesGam {i : ℕ} (s : K.Idx i) (m : Γ(M, K.inter s)) :
    Γ(reesPullback I q M, (K' I q K).inter s) :=
  sectionPullbackLE (fst' I q) M (e'_s I q K s) m

/-- Section pullback as an additive map. -/
def reesGamHom {i : ℕ} (s : K.Idx i) : Γ(M, K.inter s) →+ Γ(reesPullback I q M, (K' I q K).inter s) where
  toFun := reesGam I q M K s
  map_zero' := sectionPullbackLE_zero _ _ _
  map_add' := sectionPullbackLE_add _ _ _

variable [M.IsQuasicoherent]

/-- Sections of the pullback over a Čech intersection, as a base change. -/
def reesTensorEquiv {i : ℕ} (s : K.Idx i) :
    (ModuleCat.extendScalars ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
        (e'_s I q K s)).hom).obj (ModuleCat.of Γ(P, K.inter s) Γ(M, K.inter s)) ≃ₗ[Γ(P' I q, (K' I q K).inter s)]
      Γ(reesPullback I q M, (K' I q K).inter s) :=
  LinearEquiv.ofBijective (pullbackTensorMap (fst' I q) M (e'_s I q K s)).hom
    (pullbackTensorMap_bijective (fst' I q) M (e'_s I q K s) (reesInter_isAffineOpen I q K s)
      (haff q K s))

/-- The polynomial module of sections of `M` over a Čech intersection. -/
abbrev reesPoly {i : ℕ} (s : K.Idx i) : Type u := PolynomialModule Γ(P, K.inter s) Γ(M, K.inter s)

/-- On base-change generators: `y ⊗ m ↦ ρ(y) • m`. -/
def reesPsi0 {i : ℕ} (s : K.Idx i) :
    (ModuleCat.extendScalars ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
        (e'_s I q K s)).hom).obj (ModuleCat.of Γ(P, K.inter s) Γ(M, K.inter s)) →+
      reesPoly M K s :=
  TensorProduct.liftAddHom
    { toFun := fun y =>
        (DistribSMul.toAddMonoidHom (reesPoly M K s)
          (reesRho I q K s (show Γ(P' I q, (K' I q K).inter s) from y))).comp
          (PolynomialModule.lsingle Γ(P, K.inter s) 0).toAddMonoidHom
      map_zero' := AddMonoidHom.ext fun m => by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
          AddMonoidHom.zero_apply]
        exact (congrArg (· • _) (map_zero (reesRho I q K s))).trans (zero_smul _ _)
      map_add' := fun y y' => AddMonoidHom.ext fun m => by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply,
          AddMonoidHom.add_apply]
        exact (congrArg (· • _) (map_add (reesRho I q K s) y y')).trans (add_smul _ _ _) }
    (fun c y m => by
      change reesRho I q K s (((fst' I q).appLE _ _ (e'_s I q K s)).hom c *
          (show Γ(P' I q, (K' I q K).inter s) from y)) •
          PolynomialModule.single Γ(P, K.inter s) 0 m =
        reesRho I q K s (show Γ(P' I q, (K' I q K).inter s) from y) •
          PolynomialModule.single Γ(P, K.inter s) 0 (c • m)
      rw [map_mul, reesRho_fst, mul_comm, mul_smul, ← Polynomial.monomial_zero_left,
        PolynomialModule.monomial_smul_single, zero_add])

/-- Sections of the pullback over a Čech intersection, as polynomials with coefficients
in sections of `M`. -/
def reesPsi {i : ℕ} (s : K.Idx i) :
    Γ(reesPullback I q M, (K' I q K).inter s) →+ reesPoly M K s :=
  (reesPsi0 I q M K s).comp (reesTensorEquiv I q M K s).symm.toLinearMap.toAddMonoidHom

lemma reesPsi_tensorMap {i : ℕ} (s : K.Idx i) (τ) :
    reesPsi I q M K s ((pullbackTensorMap (fst' I q) M (e'_s I q K s)).hom τ) =
      reesPsi0 I q M K s τ := by
  have h : (reesTensorEquiv I q M K s).symm
      ((pullbackTensorMap (fst' I q) M (e'_s I q K s)).hom τ) = τ :=
    (reesTensorEquiv I q M K s).symm_apply_apply τ
  change reesPsi0 I q M K s ((reesTensorEquiv I q M K s).symm _) = _
  rw [h]

lemma reesPsi_smul_gam {i : ℕ} (s : K.Idx i) (y : Γ(P' I q, (K' I q K).inter s))
    (m : Γ(M, K.inter s)) :
    reesPsi I q M K s (y • reesGam I q M K s m) =
      reesRho I q K s y • PolynomialModule.single Γ(P, K.inter s) 0 m := by
  have h := pullbackTensorMap_tmul (fst' I q) M (e'_s I q K s) y m
  rw [← h]
  exact reesPsi_tensorMap I q M K s _

lemma reesPsi_gam {i : ℕ} (s : K.Idx i) (m : Γ(M, K.inter s)) :
    reesPsi I q M K s (reesGam I q M K s m) = PolynomialModule.single Γ(P, K.inter s) 0 m := by
  have h := reesPsi_smul_gam I q M K s 1 m
  rwa [one_smul, map_one, one_smul] at h

lemma reesTensorEquiv_apply {i : ℕ} (s : K.Idx i) (τ) :
    reesTensorEquiv I q M K s τ = (pullbackTensorMap (fst' I q) M (e'_s I q K s)).hom τ := rfl

lemma reesPsi_equiv {i : ℕ} (s : K.Idx i) (τ) :
    reesPsi I q M K s (reesTensorEquiv I q M K s τ) = reesPsi0 I q M K s τ := by
  change reesPsi0 I q M K s ((reesTensorEquiv I q M K s).symm (reesTensorEquiv I q M K s τ)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Sections of the pullback over a Čech intersection are generated by pulled back sections. -/
@[elab_as_elim]
lemma reesGam_induction {i : ℕ} (s : K.Idx i)
    {p : Γ(reesPullback I q M, (K' I q K).inter s) → Prop}
    (smul_gam : ∀ (y : Γ(P' I q, (K' I q K).inter s)) (m : Γ(M, K.inter s)),
      p (y • reesGam I q M K s m))
    (add : ∀ g g', p g → p g' → p (g + g')) (g : Γ(reesPullback I q M, (K' I q K).inter s)) :
    p g := by
  obtain ⟨τ, rfl⟩ := (reesTensorEquiv I q M K s).surjective g
  induction τ using TensorProduct.inductionOn with
  | tmul y m =>
    exact (congrArg p (pullbackTensorMap_tmul (fst' I q) M (e'_s I q K s) y m)).mpr (smul_gam y m)
  | add τ τ' h h' =>
    exact (congrArg p (map_add (reesTensorEquiv I q M K s) τ τ')).mpr (add _ _ h h')

lemma reesPsi_smul {i : ℕ} (s : K.Idx i) (x : Γ(P' I q, (K' I q K).inter s))
    (g : Γ(reesPullback I q M, (K' I q K).inter s)) :
    reesPsi I q M K s (x • g) = reesRho I q K s x • reesPsi I q M K s g := by
  revert x
  refine reesGam_induction I q M K s (p := fun g => ∀ x : Γ(P' I q, (K' I q K).inter s),
    reesPsi I q M K s (x • g) = reesRho I q K s x • reesPsi I q M K s g) ?_ ?_ g
  · intro y m x
    rw [← mul_smul, reesPsi_smul_gam, reesPsi_smul_gam, map_mul, mul_smul]
  · intro g g' h h' x
    rw [smul_add, map_add, map_add, h, h', smul_add]

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma algebraOfHom_algebraMap_eq_algR (W : (P' I q).Opens) (r : Rr I) :
    (Scheme.TwoAffineOpenCover.algebraOfHom (π' I q) W).algebraMap r = algR I q W r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [algR, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]

lemma reesPsi_rsmul {i : ℕ} (s : K.Idx i) (r : Rr I)
    (g : (reesPullbackPresheaf I q M).obj ((K' I q K).inter s)) :
    reesPsi I q M K s (r • g) =
      Polynomial.map (alg q (K.inter s)) (Rr.val I r) • reesPsi I q M K s g := by
  have e : r • g = (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from
      algR I q ((K' I q K).inter s) r •
        (show Γ(reesPullback I q M, (K' I q K).inter s) from g)) := by
    rw [OModulePresheaf.ofModules_algebraMap_smul, algebraOfHom_algebraMap_eq_algR]
    rfl
  rw [e]
  exact (reesPsi_smul I q M K s _ _).trans (by rw [reesRho_algR])

/-- The comparison `Γ(W, fst'^* M) ⊗_{⊕ Iⁿ} A[X] → Γ(U, M)[X]` on a Čech intersection. -/
def reesPsiT {i : ℕ} (s : K.Idx i) :
    (reesTensor I q M).obj ((K' I q K).inter s) →+ reesPoly M K s :=
  TensorProduct.liftAddHom
    { toFun := fun g =>
        { toFun := fun p => Polynomial.map (alg q (K.inter s)) p • reesPsi I q M K s g
          map_zero' := by rw [Polynomial.map_zero, zero_smul]
          map_add' := fun p p' => by rw [Polynomial.map_add, add_smul] }
      map_zero' := AddMonoidHom.ext fun p =>
        (congrArg (Polynomial.map (alg q (K.inter s)) p • ·) (map_zero (reesPsi I q M K s))).trans
          (smul_zero _)
      map_add' := fun g g' => AddMonoidHom.ext fun p =>
        (congrArg (Polynomial.map (alg q (K.inter s)) p • ·)
          (map_add (reesPsi I q M K s) g g')).trans (smul_add _ _ _) }
    (fun r g p => by
      change Polynomial.map (alg q (K.inter s)) p • reesPsi I q M K s (r • g) =
        Polynomial.map (alg q (K.inter s)) (Rr.incl I r * p) • reesPsi I q M K s g
      rw [reesPsi_rsmul, Polynomial.map_mul, mul_comm, mul_smul]
      rfl)

lemma reesPsiT_tmul {i : ℕ} (s : K.Idx i)
    (g : (reesPullbackPresheaf I q M).obj ((K' I q K).inter s)) (p : A[X]) :
    reesPsiT I q M K s (show (reesTensor I q M).obj ((K' I q K).inter s) from g ⊗ₜ[Rr I] p) =
      Polynomial.map (alg q (K.inter s)) p • reesPsi I q M K s g := rfl

/-- The inverse comparison `m Xʲ ↦ fst'^* m ⊗ Xʲ`. -/
def reesInv {i : ℕ} (s : K.Idx i) :
    reesPoly M K s →+ (reesTensor I q M).obj ((K' I q K).inter s) :=
  (Finsupp.liftAddHom fun j =>
      (((TensorProduct.mk (Rr I) ((reesPullbackPresheaf I q M).obj ((K' I q K).inter s))
        A[X]).flip (X ^ j)).toAddMonoidHom.comp (reesGamHom I q M K s))).comp
    (PolynomialModule.coeffAddEquiv (R := Γ(P, K.inter s))).toAddMonoidHom

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma reesInv_single {i : ℕ} (s : K.Idx i) (j : ℕ) (m : Γ(M, K.inter s)) :
    reesInv I q M K s (PolynomialModule.single Γ(P, K.inter s) j m) =
      (show (reesTensor I q M).obj ((K' I q K).inter s) from
        (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from
          reesGam I q M K s m) ⊗ₜ[Rr I] (X ^ j : A[X])) := by
  change (Finsupp.liftAddHom _) (Finsupp.single j m) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma reesInv_map_smul_single {i : ℕ} (s : K.Idx i) (p : A[X]) (j : ℕ) (m : Γ(M, K.inter s)) :
    reesInv I q M K s (Polynomial.map (alg q (K.inter s)) p •
        PolynomialModule.single Γ(P, K.inter s) j m) =
      (show (reesTensor I q M).obj ((K' I q K).inter s) from
        (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from
          reesGam I q M K s m) ⊗ₜ[Rr I] (p * X ^ j)) := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' =>
    rw [Polynomial.map_add, add_smul, map_add, hp, hp', add_mul]
    exact (TensorProduct.tmul_add _ _ _).symm
  | monomial l a =>
    rw [Polynomial.map_monomial, PolynomialModule.monomial_smul_single, reesInv_single]
    have h1 : (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from
        reesGam I q M K s (alg q (K.inter s) a • m)) =
        (algebraMap A (Rr I) a) • (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from
          reesGam I q M K s m) := by
      rw [OModulePresheaf.ofModules_algebraMap_smul, algebraOfHom_algebraMap_eq_algR,
        ← fst_appLE_alg I q (e'_s I q K s)]
      exact sectionPullbackLE_smul _ _ _ _ _
    rw [h1]
    refine (TensorProduct.smul_tmul (R := Rr I) (algebraMap A (Rr I) a) _ (X ^ (l + j) : A[X])).trans ?_
    congr 1
    change algebraMap A A[X] a * X ^ (l + j) = monomial l a * X ^ j
    rw [← Polynomial.C_eq_algebraMap, pow_add, ← mul_assoc, C_mul_X_pow_eq_monomial]

omit [M.IsQuasicoherent] in
lemma reesInv_algR_smul {i : ℕ} (s : K.Idx i) (r : Rr I) (v : reesPoly M K s) :
    reesInv I q M K s (reesRho I q K s (algR I q ((K' I q K).inter s) r) • v) =
      algR I q ((K' I q K).inter s) r • reesInv I q M K s v := by
  rw [reesRho_algR]
  induction v using PolynomialModule.induction_linear with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add v v' h h' => rw [smul_add, map_add, h, h', map_add, smul_add]
  | single j m =>
    rw [reesInv_map_smul_single, reesInv_single]
    refine (TensorProduct.smul_tmul (R := Rr I) (R' := Rr I) r
      (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from reesGam I q M K s m)
      (X ^ j : A[X])).symm.trans ?_
    change _ = (show (reesTensor I q M).obj ((K' I q K).inter s) from
      (algR I q ((K' I q K).inter s) r •
        (show (reesPullbackPresheaf I q M).obj ((K' I q K).inter s) from reesGam I q M K s m))
          ⊗ₜ[Rr I] (X ^ j : A[X]))
    congr 1

omit [M.IsQuasicoherent] in
lemma reesInv_rho_smul {i : ℕ} (s : K.Idx i) (x : Γ(P' I q, (K' I q K).inter s))
    (v : reesPoly M K s) :
    reesInv I q M K s (reesRho I q K s x • v) = x • reesInv I q M K s v := by
  let S : Subring Γ(P' I q, (K' I q K).inter s) :=
    { carrier := {x | ∀ v, reesInv I q M K s (reesRho I q K s x • v) = x • reesInv I q M K s v}
      mul_mem' := fun {x y} hx hy v => by rw [map_mul, mul_smul, hx, hy, mul_smul]
      one_mem' := fun v => by rw [map_one, one_smul, one_smul]
      add_mem' := fun {x y} hx hy v => by rw [map_add, add_smul, map_add, hx, hy, add_smul]
      zero_mem' := fun v => by rw [map_zero, zero_smul, map_zero, zero_smul]
      neg_mem' := fun {x} hx v => by rw [map_neg, neg_smul, map_neg, hx, neg_smul] }
  have hS : Subring.closure (Set.range ((fst' I q).appLE (K.inter s) ((K' I q K).inter s)
      (e'_s I q K s)).hom ∪ Set.range ((π' I q).appLE ⊤ ((K' I q K).inter s) le_top).hom) ≤ S := by
    rw [Subring.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨r₀, rfl⟩) v
    · rw [reesRho_fst]
      induction v using PolynomialModule.induction_linear with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add v v' h h' => rw [smul_add, map_add, h, h', map_add, smul_add]
      | single j m =>
        rw [← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_single, zero_add,
          reesInv_single, reesInv_single]
        exact congrArg (· ⊗ₜ[Rr I] (X ^ j : A[X])) (sectionPullbackLE_smul _ _ _ _ _)
    · have hr₀ : r₀ = (Scheme.ΓSpecIso (CommRingCat.of (Rr I))).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Rr I))).hom.hom r₀) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [hr₀]
      exact reesInv_algR_smul I q M K s _ v
  rw [closure_eq_top I q (haff q K s) (hW' I q K s)] at hS
  exact hS (Subring.mem_top x) v

lemma reesInv_psiT {i : ℕ} (s : K.Idx i) (t : (reesTensor I q M).obj ((K' I q K).inter s)) :
    reesInv I q M K s (reesPsiT I q M K s t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul g p =>
    refine reesGam_induction I q M K s (p := fun g =>
      reesInv I q M K s (reesPsiT I q M K s
        (show (reesTensor I q M).obj ((K' I q K).inter s) from g ⊗ₜ[Rr I] p)) =
      (show (reesTensor I q M).obj ((K' I q K).inter s) from g ⊗ₜ[Rr I] p)) ?_ ?_ g
    · intro y m
      rw [reesPsiT_tmul, reesPsi_smul_gam, smul_comm, reesInv_rho_smul, reesInv_map_smul_single,
        pow_zero, mul_one]
      rfl
    · intro g g' h h'
      have e : (show (reesTensor I q M).obj ((K' I q K).inter s) from (g + g') ⊗ₜ[Rr I] p) =
          (show (reesTensor I q M).obj ((K' I q K).inter s) from g ⊗ₜ[Rr I] p) +
            (show (reesTensor I q M).obj ((K' I q K).inter s) from g' ⊗ₜ[Rr I] p) :=
        TensorProduct.add_tmul _ _ _
      rw [e, map_add, map_add, h, h']
  | add t t' h h' =>
    exact (congrArg (reesInv I q M K s) (map_add (reesPsiT I q M K s) t t')).trans
      ((map_add (reesInv I q M K s) _ _).trans (congrArg₂ (· + ·) h h'))

lemma reesPsiT_injective {i : ℕ} (s : K.Idx i) : Function.Injective (reesPsiT I q M K s) :=
  Function.LeftInverse.injective (reesInv_psiT I q M K s)

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma reesGam_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (m : Γ(M, K.inter (K.face s j))) :
    (reesPullback I q M).presheaf.map (homOfLE ((K' I q K).inter_le_inter_face s j)).op
        (reesGam I q M K (K.face s j) m) =
      reesGam I q M K s (M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op m) :=
  (map_sectionPullbackLE _ _ _ _ _).trans (sectionPullbackLE_restrict _ _ _ _ _).symm

lemma reesPsi_res_smul_gam {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (y : Γ(P' I q, (K' I q K).inter (K.face s j))) (m : Γ(M, K.inter (K.face s j))) (n : ℕ) :
    (reesPsi I q M K s ((reesPullback I q M).presheaf.map
        (homOfLE ((K' I q K).inter_le_inter_face s j)).op (y • reesGam I q M K (K.face s j) m))).coeff n =
      M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op
        ((reesPsi I q M K (K.face s j) (y • reesGam I q M K (K.face s j) m)).coeff n) := by
  have e : (reesPullback I q M).presheaf.map (homOfLE ((K' I q K).inter_le_inter_face s j)).op
      (y • reesGam I q M K (K.face s j) m) =
      (P' I q).presheaf.map (homOfLE ((K' I q K).inter_le_inter_face s j)).op y •
        reesGam I q M K s (M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op m) :=
    (Scheme.Modules.map_smul _ _ _ _).trans (congrArg _ (reesGam_res I q M K s j m))
  have e' := (congrArg (reesPsi I q M K s) e).trans ((reesPsi_smul_gam I q M K s _ _).trans
    (congrArg (· • PolynomialModule.single Γ(P, K.inter s) 0
      (M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op m)) (reesRho_res I q K s j y)))
  have e'' := reesPsi_smul_gam I q M K (K.face s j) y m
  refine (congrArg (fun v => PolynomialModule.coeff v n) e').trans ?_
  refine Eq.trans ?_ (congrArg (fun v => M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op
    (PolynomialModule.coeff v n)) e'').symm
  rw [PolynomialModule.smul_single_apply, PolynomialModule.smul_single_apply]
  simp only [zero_le, ↓reduceIte, Nat.sub_zero, Polynomial.coeff_map]
  exact (Scheme.Modules.map_smul _ _ _ _).symm

lemma reesPsi_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (g : Γ(reesPullback I q M, (K' I q K).inter (K.face s j))) (n : ℕ) :
    (reesPsi I q M K s ((reesPullback I q M).presheaf.map
        (homOfLE ((K' I q K).inter_le_inter_face s j)).op g)).coeff n =
      M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op
        ((reesPsi I q M K (K.face s j) g).coeff n) := by
  refine reesGam_induction I q M K (K.face s j) ?_ ?_ g
  · exact fun y m => reesPsi_res_smul_gam I q M K s j y m n
  · intro g g' h h'
    have e₁ := (ConcreteCategory.hom ((reesPullback I q M).presheaf.map
      (homOfLE ((K' I q K).inter_le_inter_face s j)).op)).map_add g g'
    have e₂ := map_add (reesPsi I q M K s) (((reesPullback I q M).presheaf.map
      (homOfLE ((K' I q K).inter_le_inter_face s j)).op) g) (((reesPullback I q M).presheaf.map
      (homOfLE ((K' I q K).inter_le_inter_face s j)).op) g')
    have e₃ := map_add (reesPsi I q M K (K.face s j)) g g'
    refine (congrArg (fun v => PolynomialModule.coeff v n)
      ((congrArg (reesPsi I q M K s) e₁).trans e₂)).trans ?_
    refine Eq.trans ?_ (congrArg (fun v => M.presheaf.map (homOfLE
      (K.inter_le_inter_face s j)).op (PolynomialModule.coeff v n)) e₃).symm
    refine (congrArg₂ (· + ·) h h').trans ?_
    exact (map_add _ _ _).symm

lemma reesPsiT_res {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2))
    (t : (reesTensor I q M).obj ((K' I q K).inter (K.face s j))) (n : ℕ) :
    (reesPsiT I q M K s ((reesTensor I q M).res ((K' I q K).inter_le_inter_face s j) t)).coeff n =
      M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op
        ((reesPsiT I q M K (K.face s j) t).coeff n) := by
  induction t using TensorProduct.inductionOn with
  | tmul g p =>
    change (reesPsiT I q M K s (show (reesTensor I q M).obj ((K' I q K).inter s) from
      ((reesPullbackPresheaf I q M).res ((K' I q K).inter_le_inter_face s j) g) ⊗ₜ[Rr I] p)).coeff n =
        M.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op
          ((reesPsiT I q M K (K.face s j)
            (show (reesTensor I q M).obj ((K' I q K).inter (K.face s j)) from g ⊗ₜ[Rr I] p)).coeff n)
    rw [reesPsiT_tmul, reesPsiT_tmul, PolynomialModule.smul_apply, PolynomialModule.smul_apply,
      map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Scheme.Modules.map_smul, alg_res]
    congr 1
    exact reesPsi_res I q M K s j g x.2
  | add t t' h h' =>
    have e₁ := map_add ((reesTensor I q M).res ((K' I q K).inter_le_inter_face s j)) t t'
    have e₂ := map_add (reesPsiT I q M K s) (((reesTensor I q M).res
      ((K' I q K).inter_le_inter_face s j)) t) (((reesTensor I q M).res
        ((K' I q K).inter_le_inter_face s j)) t')
    have e₃ := map_add (reesPsiT I q M K (K.face s j)) t t'
    refine (congrArg (fun v => PolynomialModule.coeff v n)
      ((congrArg (reesPsiT I q M K s) e₁).trans e₂)).trans ?_
    refine Eq.trans ?_ (congrArg (fun v => M.presheaf.map (homOfLE
      (K.inter_le_inter_face s j)).op (PolynomialModule.coeff v n)) e₃).symm
    rw [PolynomialModule.coeff_add, PolynomialModule.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, h, h', map_add]
    rfl

lemma reesPsiT_rsmul {i : ℕ} (s : K.Idx i) (r : Rr I)
    (t : (reesTensor I q M).obj ((K' I q K).inter s)) :
    reesPsiT I q M K s (r • t) =
      Polynomial.map (alg q (K.inter s)) (Rr.val I r) • reesPsiT I q M K s t := by
  induction t using TensorProduct.inductionOn with
  | tmul g p =>
    change reesPsiT I q M K s (show (reesTensor I q M).obj ((K' I q K).inter s) from
      (r • g) ⊗ₜ[Rr I] p) = _
    rw [reesPsiT_tmul, reesPsiT_tmul, reesPsi_rsmul, smul_comm]
  | add t t' h h' =>
    have e₁ : r • (t + t') = r • t + r • t' := smul_add r t t'
    refine (congrArg (reesPsiT I q M K s) e₁).trans ?_
    exact (map_add (reesPsiT I q M K s) _ _).trans
      ((congrArg₂ (· + ·) h h').trans ((smul_add _ _ _).symm.trans
        (congrArg _ (map_add (reesPsiT I q M K s) t t').symm)))

lemma reesPsiT_toBaseChange {i : ℕ} (s : K.Idx i)
    (g : (reesPullbackPresheaf I q M).obj ((K' I q K).inter s)) :
    reesPsiT I q M K s ((toBaseChange (reesPullbackPresheaf I q M) A[X] 1).app _ g) =
      reesPsi I q M K s g := by
  rw [toBaseChange_app, reesPsiT_tmul, Polynomial.map_one, one_smul]

lemma reesPsi_coeff_mem {i : ℕ} (s : K.Idx i) (g : Γ(reesPullback I q M, (K' I q K).inter s))
    (n : ℕ) :
    (show (OModulePresheaf.ofModules q M).obj (K.inter s) from (reesPsi I q M K s g).coeff n) ∈
      (I ^ n) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s))) := by
  refine reesGam_induction I q M K s (p := fun g =>
    (show (OModulePresheaf.ofModules q M).obj (K.inter s) from (reesPsi I q M K s g).coeff n) ∈
      (I ^ n) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) ?_ ?_ g
  · intro y m
    rw [reesPsi_smul_gam, PolynomialModule.smul_single_apply]
    simp only [zero_le, ite_true, Nat.sub_zero]
    have hc := (mem_reesAlgebra_iff _ _).mp (reesRho_mem I q K s y) n
    rw [← Ideal.map_pow] at hc
    exact mem_ideal_smul_top_of_mem_map q M (I ^ n) hc m
  · intro g g' h h'
    rw [map_add, PolynomialModule.coeff_add, Finsupp.add_apply]
    exact add_mem h h'

lemma exists_reesPsi_eq_single {i : ℕ} (s : K.Idx i) (k : ℕ)
    {b : (OModulePresheaf.ofModules q M).obj (K.inter s)}
    (hb : b ∈ (I ^ k) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) :
    ∃ g : (reesPullbackPresheaf I q M).obj ((K' I q K).inter s),
      reesPsi I q M K s g = PolynomialModule.single Γ(P, K.inter s) k b := by
  refine Submodule.smul_induction_on hb ?_ ?_
  · intro a ha m _
    refine ⟨algR I q ((K' I q K).inter s) (Rr.mk I (monomial k a)
      (reesAlgebra.monomial_mem.mpr ha)) • reesGam I q M K s m, ?_⟩
    rw [reesPsi_smul_gam, reesRho_algR]
    change Polynomial.map (alg q (K.inter s)) (monomial k a) •
      PolynomialModule.single Γ(P, K.inter s) 0 m = _
    rw [Polynomial.map_monomial, PolynomialModule.monomial_smul_single, add_zero]
    rfl
  · rintro x y ⟨gx, hgx⟩ ⟨gy, hgy⟩
    exact ⟨gx + gy, (map_add (reesPsi I q M K s) gx gy).trans
      ((congrArg₂ (· + ·) hgx hgy).trans (PolynomialModule.single_add _ _ _).symm)⟩

/-! ### Coefficients of Rees cochains -/

/-- The `j`-th coefficient of a section of the Rees presheaf over a Čech intersection. -/
def reesCoeffHom {i : ℕ} (s : K.Idx i) (j : ℕ) :
    (reesPresheaf I q M).obj ((K' I q K).inter s) →+ Γ(M, K.inter s) :=
  (Finsupp.applyAddHom j).comp ((PolynomialModule.coeffAddEquiv (R := Γ(P, K.inter s))).toAddMonoidHom.comp
    ((reesPsiT I q M K s).comp (LinearMap.range ((toBaseChange (reesPullbackPresheaf I q M) A[X]
      1).app ((K' I q K).inter s))).subtype.toAddMonoidHom))

lemma reesCoeffHom_apply {i : ℕ} (s : K.Idx i) (j : ℕ)
    (y : (reesPresheaf I q M).obj ((K' I q K).inter s)) :
    reesCoeffHom I q M K s j y = (reesPsiT I q M K s y.1).coeff j := rfl

/-- The `j`-th coefficient cochain of a Rees cochain. -/
def reesCoeff (i j : ℕ) (z : (reesPresheaf I q M).cochain (K' I q K) i) :
    (OModulePresheaf.ofModules q M).cochain K i :=
  fun s => reesCoeffHom I q M K s j (z s)

lemma reesCoeff_add (i j : ℕ) (z z' : (reesPresheaf I q M).cochain (K' I q K) i) :
    reesCoeff I q M K i j (z + z') = reesCoeff I q M K i j z + reesCoeff I q M K i j z' :=
  funext fun s => map_add (reesCoeffHom I q M K s j) (z s) (z' s)

lemma reesCoeff_zero (i j : ℕ) : reesCoeff I q M K i j 0 = 0 :=
  funext fun s => map_zero (reesCoeffHom I q M K s j)

lemma reesCoeff_sub (i j : ℕ) (z z' : (reesPresheaf I q M).cochain (K' I q K) i) :
    reesCoeff I q M K i j (z - z') = reesCoeff I q M K i j z - reesCoeff I q M K i j z' :=
  funext fun s => map_sub (reesCoeffHom I q M K s j) (z s) (z' s)

lemma reesCoeff_d (i j : ℕ) (z : (reesPresheaf I q M).cochain (K' I q K) i) :
    reesCoeff I q M K (i + 1) j ((reesPresheaf I q M).d (K' I q K) i z) =
      (OModulePresheaf.ofModules q M).d K i (reesCoeff I q M K i j z) := by
  funext s
  rw [reesCoeff, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [map_zsmul]
  congr 1
  exact reesPsiT_res I q M K s j' (z (K.face s j')).1 j

lemma reesCoeff_smul (i j : ℕ) (r : Rr I) (z : (reesPresheaf I q M).cochain (K' I q K) i) :
    reesCoeff I q M K i j (r • z) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j,
        (Rr.val I r).coeff x.1 • reesCoeff I q M K i x.2 z := by
  funext s
  rw [Finset.sum_apply]
  change (reesPsiT I q M K s (r • (z s).1)).coeff j = _
  rw [reesPsiT_rsmul, PolynomialModule.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.coeff_map]
  rfl

lemma reesCoeff_mem (i j : ℕ) (z : (reesPresheaf I q M).cochain (K' I q K) i) (s : K.Idx i) :
    reesCoeff I q M K i j z s ∈
      (I ^ j) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s))) := by
  obtain ⟨g, hg⟩ := (z s).2
  change (reesPsiT I q M K s (z s).1).coeff j ∈ _
  rw [← hg, reesPsiT_toBaseChange]
  exact reesPsi_coeff_mem I q M K s g j

/-- A Rees cochain concentrated in degree `k` with prescribed coefficient. -/
def reesZ (i k : ℕ) (b : (OModulePresheaf.ofModules q M).cochain K i)
    (hb : ∀ s : K.Idx i, b s ∈
      (I ^ k) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) :
    (reesPresheaf I q M).cochain (K' I q K) i :=
  fun s => ⟨(toBaseChange (reesPullbackPresheaf I q M) A[X] 1).app _
    (Classical.choose (exists_reesPsi_eq_single I q M K s k (hb s))), LinearMap.mem_range_self _ _⟩

lemma reesCoeff_reesZ (i k j : ℕ) (b : (OModulePresheaf.ofModules q M).cochain K i) (hb) :
    reesCoeff I q M K i j (reesZ I q M K i k b hb) = if j = k then b else 0 := by
  funext s
  change (reesPsiT I q M K s ((toBaseChange (reesPullbackPresheaf I q M) A[X] 1).app _
    (Classical.choose (exists_reesPsi_eq_single I q M K s k (hb s))))).coeff j = _
  rw [reesPsiT_toBaseChange, Classical.choose_spec (exists_reesPsi_eq_single I q M K s k (hb s)),
    PolynomialModule.coeff_single]
  by_cases h : j = k
  · subst h
    simp only [↓reduceIte]
    exact Finsupp.single_eq_same
  · simp only [h, ↓reduceIte]
    exact Finsupp.single_eq_of_ne h

lemma d_reesZ_eq_zero (i k : ℕ) (b : (OModulePresheaf.ofModules q M).cochain K i) (hb)
    (hdb : (OModulePresheaf.ofModules q M).d K i b = 0) :
    (reesPresheaf I q M).d (K' I q K) i (reesZ I q M K i k b hb) = 0 := by
  funext s
  apply Subtype.ext
  apply reesPsiT_injective I q M K s
  apply PolynomialModule.coeff_injective
  ext j
  have h := congrFun (reesCoeff_d I q M K i j (reesZ I q M K i k b hb)) s
  rw [reesCoeff_reesZ] at h
  refine h.trans ?_
  split_ifs
  · rw [hdb]
    exact (congrArg (fun v => PolynomialModule.coeff v j) (map_zero (reesPsiT I q M K s))).symm
  · rw [map_zero]
    exact (congrArg (fun v => PolynomialModule.coeff v j) (map_zero (reesPsiT I q M K s))).symm

/-! ### Uniform stabilization -/

variable (i : ℕ)

/-- Čech cochains of `M` whose components lie in `Iᵐ` times sections. -/
def reesIC (m : ℕ) : Submodule A ((OModulePresheaf.ofModules q M).cochain K i) where
  carrier := {w | ∀ s, w s ∈
    (I ^ m) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))}
  add_mem' hw hw' s := add_mem (hw s) (hw' s)
  zero_mem' _ := zero_mem _
  smul_mem' a _ hw s := Submodule.smul_mem _ a (hw s)

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma reesIC_anti {m m' : ℕ} (h : m ≤ m') : reesIC I q M K i m' ≤ reesIC I q M K i m :=
  fun _ hw s => Submodule.smul_mono_left (Ideal.pow_le_pow_right h) (hw s)

omit [IsSeparated q] [M.IsQuasicoherent] in
lemma smul_mem_reesIC {a : A} {l m : ℕ} (ha : a ∈ I ^ l)
    {w : (OModulePresheaf.ofModules q M).cochain K i} (hw : w ∈ reesIC I q M K i m) :
    a • w ∈ reesIC I q M K i (l + m) := by
  intro s
  have h := Submodule.smul_mem_smul ha (hw s)
  rwa [← Submodule.mul_smul, ← pow_add] at h

/-- Coboundaries of cochains in `Iᵐ` times sections. -/
abbrev reesDg (m : ℕ) : Submodule A ((OModulePresheaf.ofModules q M).cochain K (i + 1)) :=
  (reesIC I q M K i m).map ((OModulePresheaf.ofModules q M).d K i)

/-- Cocycles of the Rees presheaf in degree `i + 1`. -/
abbrev reesCycles : Submodule (Rr I) ((reesPresheaf I q M).cochain (K' I q K) (i + 1)) :=
  LinearMap.ker ((reesPresheaf I q M).d (K' I q K) (i + 1))

/-- Coboundaries of the Rees presheaf in degree `i + 1`. -/
abbrev reesBoundaries : Submodule (Rr I) (reesCycles I q M K i) :=
  (LinearMap.range ((reesPresheaf I q M).d (K' I q K) i)).comap (reesCycles I q M K i).subtype

/-- Čech cohomology of the Rees presheaf in degree `i + 1`. -/
abbrev reesH : Type u := reesCycles I q M K i ⧸ reesBoundaries I q M K i

/-- The Rees cocycle of a coboundary `b` in `Iᵏ` times sections, placed in degree `k`. -/
def reesZZ (k : ℕ) (b : (OModulePresheaf.ofModules q M).cochain K (i + 1))
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.ofModules q M).d K i))
    (hb₂ : ∀ s : K.Idx (i + 1), b s ∈
      (I ^ k) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) :
    reesCycles I q M K i :=
  ⟨reesZ I q M K (i + 1) k b hb₂, LinearMap.mem_ker.mpr (d_reesZ_eq_zero I q M K (i + 1) k b hb₂ (by
    obtain ⟨w, rfl⟩ := hb₁
    exact LinearMap.congr_fun ((OModulePresheaf.ofModules q M).d_comp_d K i) w))⟩

/-- The cohomology class of `reesZZ`. -/
def reesCls (k : ℕ) (b : (OModulePresheaf.ofModules q M).cochain K (i + 1))
    (hb₁ : b ∈ LinearMap.range ((OModulePresheaf.ofModules q M).d K i))
    (hb₂ : ∀ s : K.Idx (i + 1), b s ∈
      (I ^ k) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) :
    reesH I q M K i :=
  Submodule.Quotient.mk (reesZZ I q M K i k b hb₁ hb₂)

/-- The classes coming from degrees at most `m`. -/
def reesGens (m : ℕ) : Set (reesH I q M K i) :=
  {x | ∃ k, k ≤ m ∧ ∃ b hb₁ hb₂, x = reesCls I q M K i k b hb₁ hb₂}

/-- The submodule generated by the classes coming from degrees at most `m`. -/
def reesN (m : ℕ) : Submodule (Rr I) (reesH I q M K i) :=
  Submodule.span (Rr I) (reesGens I q M K i m)

lemma reesN_mono : Monotone (reesN I q M K i) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨k, hk, b, hb₁, hb₂, hx⟩ => ⟨k, hk.trans h, b, hb₁, hb₂, hx⟩

/-- A class has a representative whose `j`-th coefficient is a coboundary of a cochain in
`I^(j - c₀)` times sections, for every `j`. -/
def ReesGood (c₀ : ℕ) (x : reesH I q M K i) : Prop :=
  ∃ z : reesCycles I q M K i, Submodule.Quotient.mk z = x ∧
    ∀ j, reesCoeff I q M K (i + 1) j z.1 ∈ reesDg I q M K i (j - c₀)

lemma reesGood_of_mem (c₀ : ℕ) {x : reesH I q M K i} (hx : x ∈ reesN I q M K i c₀) :
    ReesGood I q M K i c₀ x := by
  unfold reesN at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, b, hb₁, hb₂, rfl⟩ := h
    refine ⟨reesZZ I q M K i k b hb₁ hb₂, rfl, fun j => ?_⟩
    change reesCoeff I q M K (i + 1) j (reesZ I q M K (i + 1) k b hb₂) ∈ _
    rw [reesCoeff_reesZ]
    split_ifs with hj
    · subst hj
      obtain ⟨w, rfl⟩ := hb₁
      refine Submodule.mem_map.mpr ⟨w, fun s => ?_, rfl⟩
      rw [Nat.sub_eq_zero_of_le hk, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    · exact Submodule.zero_mem _
  | zero =>
    exact ⟨0, rfl, fun j => by
      rw [Submodule.coe_zero, reesCoeff_zero]
      exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hy
    refine ⟨z + z', rfl, fun j => ?_⟩
    rw [Submodule.coe_add, reesCoeff_add]
    exact Submodule.add_mem _ (hz j) (hz' j)
  | smul r x _ hx =>
    obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨r • z, rfl, fun j => ?_⟩
    rw [Submodule.coe_smul, reesCoeff_smul]
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨w, hw, hdw⟩ := Submodule.mem_map.mp (hz x.2)
    rw [← hdw, ← LinearMap.map_smul]
    refine Submodule.mem_map.mpr ⟨_, reesIC_anti I q M K i ?_
      (smul_mem_reesIC I q M K i (Rr.coeff_mem I r x.1) hw), rfl⟩
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

end Rees

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {P : Scheme.{u}}
  (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q] (M : P.Modules) [M.IsQuasicoherent]
  (K : P.OrderedAffineCover) (i : ℕ)

attribute [local instance] reesPolynomialAlgebra

/-- **Čech Artin–Rees.** If the Rees presheaf is coherent and quasi-coherent, there is a
uniform `c` such that every Čech coboundary in `I^(n+c)` times sections is the coboundary of
a cochain in `Iⁿ` times sections. -/
theorem exists_uniform_d_eq_d (hFc : (reesPresheaf I q M).IsCoherent)
    (hFq : (reesPresheaf I q M).IsQuasicoherent) :
    ∃ c : ℕ, ∀ (n : ℕ) (w : (OModulePresheaf.ofModules q M).cochain K i),
      (∀ s : K.Idx (i + 1), (OModulePresheaf.ofModules q M).d K i w s ∈
        (I ^ (n + c)) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) →
      ∃ w' : (OModulePresheaf.ofModules q M).cochain K i,
        (∀ s : K.Idx i, w' s ∈
          (I ^ n) • (⊤ : Submodule A ((OModulePresheaf.ofModules q M).obj (K.inter s)))) ∧
        (OModulePresheaf.ofModules q M).d K i w' = (OModulePresheaf.ofModules q M).d K i w := by
  have hfin : Module.Finite (Rr I) (reesH I q M K i) :=
    (OModulePresheaf.cechFinite_of_isProper (reesPresheaf I q M) hFc hFq (K' I q K)).2 i
  have hnoeth : IsNoetherian (Rr I) (reesH I q M K i) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨c₀, hc₀⟩ := (monotone_stabilizes_iff_noetherian (R := Rr I)
    (M := reesH I q M K i)).mpr hnoeth ⟨reesN I q M K i, reesN_mono I q M K i⟩
  refine ⟨c₀, fun n w hw => ?_⟩
  set b := (OModulePresheaf.ofModules q M).d K i w with hb
  have hb₁ : b ∈ LinearMap.range ((OModulePresheaf.ofModules q M).d K i) := ⟨w, rfl⟩
  have hmem : reesCls I q M K i (n + c₀) b hb₁ hw ∈ reesN I q M K i (n + c₀) :=
    Submodule.subset_span ⟨n + c₀, le_rfl, b, hb₁, hw, rfl⟩
  have hstab : reesN I q M K i c₀ = reesN I q M K i (n + c₀) :=
    hc₀ (n + c₀) (Nat.le_add_left c₀ n)
  rw [← hstab] at hmem
  obtain ⟨z, hz, hgood⟩ := reesGood_of_mem I q M K i c₀ hmem
  have hdiff : reesZZ I q M K i (n + c₀) b hb₁ hw - z ∈ reesBoundaries I q M K i :=
    (Submodule.Quotient.eq _).mp hz.symm
  obtain ⟨w', hw'⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hdiff)
  change (reesPresheaf I q M).d (K' I q K) i w' = reesZ I q M K (i + 1) (n + c₀) b hw - z.1 at hw'
  have key := congrArg (reesCoeff I q M K (i + 1) (n + c₀)) hw'
  rw [reesCoeff_d, reesCoeff_sub, reesCoeff_reesZ] at key
  simp only [↓reduceIte] at key
  obtain ⟨w₁, hw₁, hdw₁⟩ := Submodule.mem_map.mp (hgood (n + c₀))
  rw [Nat.add_sub_cancel] at hw₁
  refine ⟨w₁ + reesCoeff I q M K i (n + c₀) w', fun s => ?_, ?_⟩
  · have h2 := Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c₀))
      (reesCoeff_mem I q M K i (n + c₀) w' s)
    exact add_mem (hw₁ s) h2
  · rw [map_add, hdw₁, key, add_sub_cancel]

omit [IsNoetherianRing A] [IsProper q] in
/-- Sections of the pullback of a quasi-coherent module satisfy the FLT localization
conditions on basic opens of affine opens. -/
lemma isQuasicoherent_reesPullbackPresheaf : (reesPullbackPresheaf I q M).IsQuasicoherent := by
  intro U a
  constructor
  · intro x
    obtain ⟨n, t, ht⟩ := AffineVanishing.exists_pow_smul_eq_res_aux U.2 (reesPullback I q M) a x
    refine ⟨n, t, ?_⟩
    change (reesPullback I q M).presheaf.map (homOfLE ((P' I q).basicOpen_le a)).op t =
      ((P' I q).presheaf.map (homOfLE ((P' I q).basicOpen_le a)).op).hom (a ^ n) • x
    rw [map_pow]
    exact ht
  · exact AffineVanishing.exists_pow_smul_eq_zero_aux U.2 (reesPullback I q M) a

omit [IsNoetherianRing A] [IsProper q] in
/-- The Rees presheaf is quasi-coherent in the sense of the FLT presheaves. -/
lemma isQuasicoherent_reesPresheaf : (reesPresheaf I q M).IsQuasicoherent :=
  isQuasicoherent_im_toBaseChange _ _ _ (isQuasicoherent_reesPullbackPresheaf I q M)

omit [IsNoetherianRing A] [IsProper q] in
/-- The Rees presheaf has finite sections on affine opens if `M` does. -/
lemma isCoherent_reesPresheaf (hM : HasFiniteAffineSections M) :
    (reesPresheaf I q M).IsCoherent :=
  isCoherent_im_toBaseChange _ _ _ (HasFiniteAffineSections.pullbackObj (fst' I q) hM)

end Main

section BoundaryLift

lemma mem_ideal_smul_top_pi_iff {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]
    {V : ι → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] (J : Ideal R)
    (x : ∀ i, V i) :
    x ∈ J • (⊤ : Submodule R (∀ i, V i)) ↔ ∀ i, x i ∈ J • (⊤ : Submodule R (V i)) := by
  classical
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro y z hy hz
      exact add_mem hy hz
  · intro hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.smul_induction_on (hx i) ?_ ?_
    · intro r hr m _
      change (LinearMap.single R V i) (r • m) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro y z hy hz
      change (LinearMap.single R V i) (y + z) ∈ _
      rw [map_add]
      exact add_mem hy hz

/-- **Uniform Čech boundary lifts.** For a proper morphism to the spectrum of a noetherian
ring and a quasi-coherent module with finite affine sections, there is one `c` such that,
for all `n + c ≤ k`, every Čech coboundary lying in `Iᵏ` times cochains is the coboundary
of a cochain in `Iⁿ` times cochains. -/
theorem exists_uniform_cechBoundaryLift {R : CommRingCat.{u}} [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsProper f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1))
    (𝒰 : X.OrderedAffineCover) (I : Ideal R) (p : ℕ) :
    ∃ c : ℕ, ∀ n k : ℕ, n + c ≤ k → IdealAdic.CechBoundaryLift f M 𝒰 (I ^ k) (I ^ n) p := by
  obtain ⟨c, hc⟩ := exists_uniform_d_eq_d (A := R) I f M 𝒰 p
    (isCoherent_reesPresheaf I f M hM) (isQuasicoherent_reesPresheaf I f M)
  refine ⟨c, fun n k h y hy => ?_⟩
  obtain ⟨y', hy'mem, hy'eq⟩ := hc n y fun s =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right h) ((mem_ideal_smul_top_pi_iff _ _).1 hy s)
  exact ⟨y', (mem_ideal_smul_top_pi_iff _ _).2 hy'mem, hy'eq⟩

end BoundaryLift

end Langlands.AlgebraicGeometry.Modules.ProperAdicArtinRees
