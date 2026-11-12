import Langlands.Algebra.PushoutCechNaturality
import Langlands.AlgebraicGeometry.Picard.RelativeAffineSections
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper

/-! # Base-changed Čech complexes of relative spaces and their comparison maps -/

set_option linter.style.haveILetI false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections Langlands.Algebra.PushoutIdealTensor

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

section Cover

variable {S A : Type u} [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

instance isAffineHom_relMap (s : S →ₐ[R] A) : IsAffineHom (relMap f s) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_relMap f s).flip inferInstance

/-- The ordered affine cover of the relative space of `A` pulled back along an algebra map. -/
abbrev pullCover (s : S →ₐ[R] A) (K : (relSpace f S).OrderedAffineCover) :
    (relSpace f A).OrderedAffineCover where
  ι := K.ι
  U i := relMap f s ⁻¹ᵁ K.U i
  isAffineOpen i := (K.isAffineOpen i).preimage _
  iSup_eq_top := by
    rw [← Scheme.Hom.preimage_iSup, K.iSup_eq_top, Scheme.Hom.preimage_top]

lemma preimage_iInf_of_finite {Y Z : Scheme.{u}} (g : Y ⟶ Z) {κ : Type*} [Finite κ]
    (U : κ → Z.Opens) : g ⁻¹ᵁ (⨅ j, U j) = ⨅ j, g ⁻¹ᵁ U j := by
  apply SetLike.coe_injective
  simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage, Set.preimage_iInter]

lemma pullCover_inter (s : S →ₐ[R] A) (K : (relSpace f S).OrderedAffineCover) {p : ℕ}
    (σ : K.Idx p) : (pullCover f s K).inter σ = relMap f s ⁻¹ᵁ K.inter σ := by
  simp only [Scheme.OrderedAffineCover.inter, pullCover, preimage_iInf_of_finite]

/-- On a relative space that is separated over its base, finite intersections of the opens of
an ordered affine cover are affine. -/
lemma isAffineOpen_inter [IsSeparated (relProj f S)] (K : (relSpace f S).OrderedAffineCover)
    {p : ℕ} (σ : K.Idx p) : IsAffineOpen (K.inter σ) := by
  have hinf : ∀ U V : (relSpace f S).Opens, IsAffineOpen U → IsAffineOpen V →
      IsAffineOpen (U ⊓ V) := fun U V hU hV =>
    (isAffineHom_diagonal_iff (f := relProj f S)).mp inferInstance ⊤ (isAffineOpen_top _) U (by simp) V (by simp)
      hU hV
  exact InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => hinf _ _ h h')
    (fun j => K.isAffineOpen (σ.1 j))

lemma isSeparated_relProj [IsSeparated f] (S : Type u) [CommRing S] [Algebra R S] :
    IsSeparated (relProj f S) := by
  change IsSeparated (pullback.fst _ f)
  exact MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback (affineBase R S).hom f).flip inferInstance

lemma isProper_relProj [IsProper f] (S : Type u) [CommRing S] [Algebra R S] :
    IsProper (relProj f S) := by
  change IsProper (pullback.fst _ f)
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback (affineBase R S).hom f).flip inferInstance

lemma appLE_congr {Y Z : Scheme.{u}} {g₁ g₂ : Y ⟶ Z} (h : g₁ = g₂) (U : Z.Opens) (V : Y.Opens)
    (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U) : g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
  subst h
  rfl

/-- The structure maps of relative spaces commute with the section maps of a base change. -/
lemma structureHom_comp_appLE (s : S →ₐ[R] A) (V : (relSpace f S).Opens)
    (W : (relSpace f A).Opens) (h : W ≤ relMap f s ⁻¹ᵁ V) :
    structureHom f S V ≫ (relMap f s).appLE V W h =
      CommRingCat.ofHom s.toRingHom ≫ structureHom f A W := by
  have e₁ : (relProj f S).appLE ⊤ V le_top ≫ (relMap f s).appLE V W h =
      (relMap f s ≫ relProj f S).appLE ⊤ W (h.trans (Scheme.Hom.preimage_mono _ le_top)) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have e₂ : (relMap f s ≫ relProj f S).appLE ⊤ W (h.trans (Scheme.Hom.preimage_mono _ le_top)) =
      (Spec.map (CommRingCat.ofHom s.toRingHom)).appTop ≫ (relProj f A).appLE ⊤ W le_top := by
    rw [appLE_congr (isPullback_relMap f s).w _ _ _
      (le_top.trans_eq (Scheme.Hom.preimage_top _).symm), Scheme.Hom.comp_appLE]
    rfl
  change (Scheme.ΓSpecIso _).inv ≫ (relProj f S).appLE ⊤ V le_top ≫ (relMap f s).appLE V W h =
    CommRingCat.ofHom s.toRingHom ≫ (Scheme.ΓSpecIso _).inv ≫ (relProj f A).appLE ⊤ W le_top
  rw [e₁, e₂, Scheme.ΓSpecIso_inv_naturality_assoc]

/-- `algebraIsPushout_sections` for an open equal to the preimage of an affine open. -/
lemma algebraIsPushout_sections_of_eq (s : S →ₐ[R] A) (V : (relSpace f S).Opens)
    (hV : IsAffineOpen V) (W : (relSpace f A).Opens) (hW : relMap f s ⁻¹ᵁ V = W)
    [Algebra S A] [Algebra S Γ(relSpace f S, V)] [Algebra A Γ(relSpace f A, W)]
    [Algebra Γ(relSpace f S, V) Γ(relSpace f A, W)] [Algebra S Γ(relSpace f A, W)]
    [IsScalarTower S A Γ(relSpace f A, W)] [IsScalarTower S Γ(relSpace f S, V) Γ(relSpace f A, W)]
    (h₁ : algebraMap S A = s.toRingHom)
    (h₂ : algebraMap S Γ(relSpace f S, V) = (structureHom f S V).hom)
    (h₃ : algebraMap A Γ(relSpace f A, W) = (structureHom f A W).hom)
    (h₄ : algebraMap Γ(relSpace f S, V) Γ(relSpace f A, W) =
      ((relMap f s).appLE V W hW.ge).hom) :
    Algebra.IsPushout S A Γ(relSpace f S, V) Γ(relSpace f A, W) := by
  subst hW
  exact algebraIsPushout_sections f s V hV h₁ h₂ h₃ h₄

end Cover

section Complex

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  (A₀ : Type u) [CommRing A₀] [Algebra P A₀]

/-- The ordered Čech cochains of the structure sheaf of the relative space of `P`,
base-changed to `A₀`. -/
abbrev cplx (p : ℕ) : Type u := A₀ ⊗[P] (OModulePresheaf.unit (relProj f P)).cochain K p

/-- The base-changed Čech differential. -/
def dif (p : ℕ) : cplx f K A₀ p →ₗ[A₀] cplx f K A₀ (p + 1) :=
  ((OModulePresheaf.unit (relProj f P)).d K p).baseChange A₀

lemma dif_comp_dif (p : ℕ) : dif f K A₀ (p + 1) ∘ₗ dif f K A₀ p = 0 := by
  rw [dif, dif, ← LinearMap.baseChange_comp, OModulePresheaf.d_comp_d,
    LinearMap.baseChange_zero]

lemma subsingleton_cplx {p : ℕ} (hp : Fintype.card K.ι < p) :
    Subsingleton (cplx f K A₀ p) := by
  have : IsEmpty (K.Idx p) := ⟨fun σ => by
    have := Fintype.card_le_of_injective σ.1 σ.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  infer_instance

instance flat_cochain [Flat f] [IsSeparated f] (p : ℕ) :
    Module.Flat P ((OModulePresheaf.unit (relProj f P)).cochain K p) := by
  have := isSeparated_relProj f P
  have : ∀ σ : K.Idx p, Module.Flat P ((OModulePresheaf.unit (relProj f P)).obj (K.inter σ)) :=
    fun σ => flat_structureHom f P _ (isAffineOpen_inter f K σ)
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := P)).symm

end Complex

section Comparison

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  (A : Type u) [CommRing A] [Algebra R A] [Algebra P A] [IsScalarTower R P A]

/-- The ordered affine cover of the relative space of a `P`-algebra `A`, pulled back from the
cover `K` of the relative space of `P`. -/
abbrev testCover : (relSpace f A).OrderedAffineCover :=
  pullCover f (IsScalarTower.toAlgHom R P A) K

lemma testCover_inter {p : ℕ} (σ : K.Idx p) :
    (testCover f K A).inter σ = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ K.inter σ :=
  pullCover_inter f _ K σ

variable {A} in
/-- The base-change map on the sections over a finite intersection. -/
def secMap {p : ℕ} (σ : K.Idx p) :
    Γ(relSpace f P, K.inter σ) ⟶ Γ(relSpace f A, (testCover f K A).inter σ) :=
  (relMap f (IsScalarTower.toAlgHom R P A)).appLE _ _ (testCover_inter f K A σ).le

lemma structureHom_comp_secMap {p : ℕ} (σ : K.Idx p) :
    structureHom f P (K.inter σ) ≫ secMap f K σ =
      CommRingCat.ofHom (algebraMap P A) ≫ structureHom f A ((testCover f K A).inter σ) :=
  structureHom_comp_appLE f _ _ _ _

variable {A₀ : Type u} [CommRing A₀] [Algebra P A₀]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]

variable {A} in
/-- The comparison map from the base-changed Čech cochains with coefficients in `M` to the
Čech cochains of the structure sheaf of the relative space of `A`, along `j : M → A`:
`(a ⊗ x) ⊗ m ↦ (j (a m) · x_σ)_σ`. -/
def compMap [IsSeparated f] (j : M →ₗ[P] A) (p : ℕ) :
    cplx f K A₀ p ⊗[A₀] M →+
      (OModulePresheaf.unit (relProj f A)).cochain (testCover f K A) p :=
  letI : ∀ σ : K.Idx p, Algebra P Γ(relSpace f P, K.inter σ) := fun σ =>
    Scheme.TwoAffineOpenCover.algebraOfHom (relProj f P) _
  letI : ∀ σ : K.Idx p, Algebra A Γ(relSpace f A, (testCover f K A).inter σ) := fun σ =>
    Scheme.TwoAffineOpenCover.algebraOfHom (relProj f A) _
  letI : ∀ σ : K.Idx p, Algebra P Γ(relSpace f A, (testCover f K A).inter σ) := fun σ =>
    ((algebraMap A _).comp (algebraMap P A)).toAlgebra
  letI : ∀ σ : K.Idx p,
      Algebra Γ(relSpace f P, K.inter σ) Γ(relSpace f A, (testCover f K A).inter σ) :=
    fun σ => (secMap (A := A) f K σ).hom.toAlgebra
  haveI : ∀ σ : K.Idx p, IsScalarTower P A Γ(relSpace f A, (testCover f K A).inter σ) :=
    fun σ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ σ : K.Idx p,
      IsScalarTower P Γ(relSpace f P, K.inter σ) Γ(relSpace f A, (testCover f K A).inter σ) :=
    fun σ => IsScalarTower.of_algebraMap_eq fun x =>
      (ConcreteCategory.congr_hom (structureHom_comp_secMap f K A σ) x).symm
  haveI : ∀ σ : K.Idx p, Algebra.IsPushout P A Γ(relSpace f P, K.inter σ)
      Γ(relSpace f A, (testCover f K A).inter σ) := fun σ => by
    have := isSeparated_relProj f P
    exact algebraIsPushout_sections_of_eq f _ _ (isAffineOpen_inter f K σ) _
      (testCover_inter f K A σ).symm rfl rfl rfl rfl
  (cechTensorMap (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j).toAddMonoidHom

variable {A} [IsSeparated f]

set_option hygiene false in
/-- Introduces the algebra structures used in `compMap` as local instances. -/
local macro "intro_insts" p:term:max A:term:max : tactic => `(tactic| (
  letI : ∀ σ : K.Idx $p, Algebra P Γ(relSpace f P, K.inter σ) := fun σ =>
    Scheme.TwoAffineOpenCover.algebraOfHom (relProj f P) _
  letI : ∀ σ : K.Idx $p, Algebra $A Γ(relSpace f $A, (testCover f K $A).inter σ) := fun σ =>
    Scheme.TwoAffineOpenCover.algebraOfHom (relProj f $A) _
  letI : ∀ σ : K.Idx $p, Algebra P Γ(relSpace f $A, (testCover f K $A).inter σ) := fun σ =>
    ((algebraMap $A _).comp (algebraMap P $A)).toAlgebra
  letI : ∀ σ : K.Idx $p,
      Algebra Γ(relSpace f P, K.inter σ) Γ(relSpace f $A, (testCover f K $A).inter σ) :=
    fun σ => (secMap (A := $A) f K σ).hom.toAlgebra
  haveI : ∀ σ : K.Idx $p, IsScalarTower P $A Γ(relSpace f $A, (testCover f K $A).inter σ) :=
    fun σ => IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : ∀ σ : K.Idx $p,
      IsScalarTower P Γ(relSpace f P, K.inter σ) Γ(relSpace f $A, (testCover f K $A).inter σ) :=
    fun σ => IsScalarTower.of_algebraMap_eq fun x =>
      (ConcreteCategory.congr_hom (structureHom_comp_secMap f K $A σ) x).symm
  haveI : ∀ σ : K.Idx $p, Algebra.IsPushout P $A Γ(relSpace f P, K.inter σ)
      Γ(relSpace f $A, (testCover f K $A).inter σ) := fun σ => by
    have := isSeparated_relProj f P
    exact algebraIsPushout_sections_of_eq f _ _ (isAffineOpen_inter f K σ) _
      (testCover_inter f K $A σ).symm rfl rfl rfl rfl))

lemma compMap_tmul (j : M →ₗ[P] A) {p : ℕ} (a : A₀)
    (x : (OModulePresheaf.unit (relProj f P)).cochain K p) (m : M) (σ : K.Idx p) :
    compMap f K j p ((a ⊗ₜ[P] x) ⊗ₜ[A₀] m) σ =
      (structureHom f A _).hom (j (a • m)) * (secMap (A := A) f K σ).hom (x σ) := by
  unfold compMap
  intro_insts p A
  exact cechTensorMap_tmul (C := P) (A := A) (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j a x m σ

lemma compMap_injective [Flat f] (j : M →ₗ[P] A) (hj : Function.Injective j) (p : ℕ) :
    Function.Injective (compMap (A₀ := A₀) f K j p) := by
  unfold compMap
  intro_insts p A
  have : ∀ σ : K.Idx p, Module.Flat P Γ(relSpace f P, K.inter σ) := fun σ => by
    have := isSeparated_relProj f P
    exact flat_structureHom f P _ (isAffineOpen_inter f K σ)
  exact cechTensorMap_injective (C := P) (A := A) (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j hj

lemma exists_compMap_eq_iff (j : M →ₗ[P] A) (𝔞 : Ideal A) (hj : ∀ a : A, a ∈ 𝔞 ↔ ∃ m, j m = a)
    {p : ℕ} (y : (OModulePresheaf.unit (relProj f A)).cochain (testCover f K A) p) :
    (∃ x, compMap (A₀ := A₀) f K j p x = y) ↔
      ∀ σ, y σ ∈ Ideal.map (structureHom f A ((testCover f K A).inter σ)).hom 𝔞 := by
  unfold compMap
  intro_insts p A
  exact LinearMap.mem_range.symm.trans (mem_range_cechTensorMap_iff (C := P) (A := A) (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j 𝔞 hj y)

omit [IsSeparated f] in
lemma secMap_res {p q : ℕ} (σ : K.Idx p) (τ : K.Idx q) (h : K.inter τ ≤ K.inter σ)
    (h' : (testCover f K A).inter τ ≤ (testCover f K A).inter σ) (x : Γ(relSpace f P, K.inter σ)) :
    ((relSpace f A).presheaf.map (homOfLE h').op).hom ((secMap (A := A) f K σ).hom x) =
      (secMap (A := A) f K τ).hom (((relSpace f P).presheaf.map (homOfLE h).op).hom x) := by
  change (secMap (A := A) f K σ ≫ (relSpace f A).presheaf.map (homOfLE h').op).hom x =
    ((relSpace f P).presheaf.map (homOfLE h).op ≫ secMap (A := A) f K τ).hom x
  rw [secMap, secMap, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

omit [IsSeparated f] in
lemma d_secMap {p : ℕ} (x : (OModulePresheaf.unit (relProj f P)).cochain K p) :
    (OModulePresheaf.unit (relProj f A)).d (testCover f K A) p
        (fun σ => (secMap (A := A) f K σ).hom (x σ)) =
      fun s => (secMap (A := A) f K s).hom ((OModulePresheaf.unit (relProj f P)).d K p x s) := by
  funext s
  refine (OModulePresheaf.d_apply _ _ _ _ s).trans (Eq.trans ?_
    (congrArg (secMap (A := A) f K s).hom (OModulePresheaf.d_apply _ K p x s)).symm)
  refine Eq.trans ?_ (map_sum (secMap (A := A) f K s).hom _ _).symm
  refine Finset.sum_congr rfl fun i _ => Eq.trans ?_ (map_zsmul _ _ _).symm
  exact congrArg _ (secMap_res f K _ _ _ _ _)

lemma compMap_dif (j : M →ₗ[P] A) (p : ℕ) (y : cplx f K A₀ p ⊗[A₀] M) :
    compMap f K j (p + 1) ((dif f K A₀ p).rTensor M y) =
      (OModulePresheaf.unit (relProj f A)).d (testCover f K A) p (compMap f K j p y) := by
  unfold compMap dif
  intro_insts p A
  intro_insts (p + 1) A
  exact cechTensorMap_differential (C := P) (A := A) (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j
    (fun σ : K.Idx (p + 1) => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx (p + 1) => Γ(relSpace f A, (testCover f K A).inter σ))
    ((OModulePresheaf.unit (relProj f P)).d K p)
    ((OModulePresheaf.unit (relProj f A)).d (testCover f K A) p) (d_secMap f K) y

lemma compMap_mul_eq_zero (j : M →ₗ[P] A) (hj : ∀ m m', j m * j m' = 0) {p : ℕ}
    (y y' : cplx f K A₀ p ⊗[A₀] M) (σ : K.Idx p) :
    (show Γ(relSpace f A, (testCover f K A).inter σ) from compMap f K j p y σ) *
      (show Γ(relSpace f A, (testCover f K A).inter σ) from compMap f K j p y' σ) = 0 := by
  unfold compMap
  intro_insts p A
  exact cechTensorMap_mul_eq_zero (C := P) (A := A) (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ)) j hj y y' σ

variable {A' : Type u} [CommRing A'] [Algebra R A'] [Algebra P A'] [IsScalarTower R P A']

omit [IsSeparated f] in
lemma testCover_inter_le (h : A →ₐ[P] A') {p : ℕ} (σ : K.Idx p) :
    (testCover f K A').inter σ ≤
      relMap f (h.restrictScalars R) ⁻¹ᵁ (testCover f K A).inter σ := by
  have e : (IsScalarTower.toAlgHom R P A') =
      (h.restrictScalars R).comp (IsScalarTower.toAlgHom R P A) := by
    ext x
    simp
  rw [testCover_inter, testCover_inter, e, relMap_comp, Scheme.Hom.comp_preimage]

omit [IsSeparated f] in
/-- The section maps of the relative spaces along a morphism of test algebras. -/
def testMap (h : A →ₐ[P] A') {p : ℕ} (σ : K.Idx p) :
    Γ(relSpace f A, (testCover f K A).inter σ) ⟶ Γ(relSpace f A', (testCover f K A').inter σ) :=
  (relMap f (h.restrictScalars R)).appLE _ _ (testCover_inter_le f K h σ)

omit [IsSeparated f] in
lemma secMap_comp_testMap (h : A →ₐ[P] A') {p : ℕ} (σ : K.Idx p) :
    secMap (A := A) f K σ ≫ testMap f K h σ = secMap (A := A') f K σ := by
  rw [secMap, testMap, Scheme.Hom.appLE_comp_appLE]
  refine appLE_congr ?_ _ _ _ _
  rw [← relMap_comp]
  congr 1
  ext x
  simp

omit [IsSeparated f] in
lemma structureHom_comp_testMap (h : A →ₐ[P] A') {p : ℕ} (σ : K.Idx p) :
    structureHom f A _ ≫ testMap f K h σ =
      CommRingCat.ofHom h.toRingHom ≫ structureHom f A' ((testCover f K A').inter σ) :=
  structureHom_comp_appLE f (h.restrictScalars R) _ _ _

variable {M' : Type u} [AddCommGroup M'] [Module A₀ M'] [Module P M'] [IsScalarTower P A₀ M']

lemma compMap_natural (j : M →ₗ[P] A) (j' : M' →ₗ[P] A') (h : A →ₐ[P] A')
    (φ : M →ₗ[A₀] M') (hφ : ∀ m, j' (φ m) = h (j m)) {p : ℕ} (y : cplx f K A₀ p ⊗[A₀] M)
    (σ : K.Idx p) :
    (testMap f K h σ).hom (compMap f K j p y σ) = compMap f K j' p (φ.lTensor _ y) σ := by
  unfold compMap
  intro_insts p A
  intro_insts p A'
  exact cechTensorMap_natural (C := P) (A := A) (A' := A') (A₀ := A₀)
    (fun σ : K.Idx p => Γ(relSpace f P, K.inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A, (testCover f K A).inter σ))
    (fun σ : K.Idx p => Γ(relSpace f A', (testCover f K A').inter σ)) j j' h.toRingHom
    (fun σ => (testMap f K h σ).hom)
    (fun σ a => ConcreteCategory.congr_hom (structureHom_comp_testMap f K h σ) a)
    (fun σ x => ConcreteCategory.congr_hom (secMap_comp_testMap f K h σ) x) φ hφ y σ

end Comparison

section Finiteness

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  (A₀ : Type u) [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]

section
variable [IsSeparated f]

lemma compMap_smul_tmul_one (a : A₀) {p : ℕ} (y : cplx f K A₀ p) (σ : K.Idx p) :
    compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p ((a • y) ⊗ₜ[A₀] (1 : A₀)) σ =
      (structureHom f A₀ ((testCover f K A₀).inter σ)).hom a *
        (show Γ(relSpace f A₀, (testCover f K A₀).inter σ) from
          compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p (y ⊗ₜ[A₀] (1 : A₀)) σ) := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ =>
    have e : ∀ z₁ z₂ : cplx f K A₀ p,
        compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p ((z₁ + z₂) ⊗ₜ[A₀] (1 : A₀)) σ =
          compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p (z₁ ⊗ₜ[A₀] (1 : A₀)) σ +
            compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p (z₂ ⊗ₜ[A₀] (1 : A₀)) σ := fun z₁ z₂ =>
      congrFun ((congrArg (compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p)
        (TensorProduct.add_tmul z₁ z₂ (1 : A₀))).trans
          (map_add (compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p) _ _)) σ
    rw [smul_add, e, e, h₁, h₂]
    exact (mul_add (R := Γ(relSpace f A₀, (testCover f K A₀).inter σ)) _ _ _).symm
  | tmul b x =>
    rw [TensorProduct.smul_tmul', compMap_tmul, compMap_tmul]
    simp only [LinearMap.id_apply, smul_eq_mul, mul_one, map_mul]
    exact mul_assoc (G := Γ(relSpace f A₀, (testCover f K A₀).inter σ)) _ _ _

/-- The base-changed Čech cochains of the relative space of `P` are the Čech cochains of the
relative space of `A₀` for the pulled-back cover (linear map). -/
def toCochain (p : ℕ) :
    cplx f K A₀ p →ₗ[A₀] (OModulePresheaf.unit (relProj f A₀)).cochain (testCover f K A₀) p where
  toFun y := compMap f K (LinearMap.id : A₀ →ₗ[P] A₀) p (y ⊗ₜ[A₀] (1 : A₀))
  map_add' y y' := by rw [TensorProduct.add_tmul, map_add]
  map_smul' a y := by
    funext σ
    exact compMap_smul_tmul_one f K A₀ a y σ

lemma toCochain_dif (p : ℕ) (y : cplx f K A₀ p) :
    toCochain f K A₀ (p + 1) (dif f K A₀ p y) =
      (OModulePresheaf.unit (relProj f A₀)).d (testCover f K A₀) p (toCochain f K A₀ p y) :=
  compMap_dif f K (LinearMap.id : A₀ →ₗ[P] A₀) p (y ⊗ₜ[A₀] (1 : A₀))

lemma toCochain_bijective [Flat f] (p : ℕ) : Function.Bijective (toCochain f K A₀ p) := by
  constructor
  · intro y y' h
    have := compMap_injective f K (LinearMap.id : A₀ →ₗ[P] A₀) Function.injective_id p h
    simpa using congrArg (TensorProduct.rid A₀ (cplx f K A₀ p)) this
  · intro c
    obtain ⟨x, hx⟩ := (exists_compMap_eq_iff f K (A₀ := A₀) (LinearMap.id : A₀ →ₗ[P] A₀) ⊤
      (fun a => ⟨fun _ => ⟨a, rfl⟩, fun _ => Submodule.mem_top⟩) c).mpr
      (fun σ => by rw [Ideal.map_top]; trivial)
    refine ⟨TensorProduct.rid A₀ (cplx f K A₀ p) x, ?_⟩
    change compMap f K _ p ((TensorProduct.rid A₀ _).symm (TensorProduct.rid A₀ _ x)) = c
    rw [LinearEquiv.symm_apply_apply, hx]

/-- The comparison isomorphism of `toCochain`. -/
def equivCochain [Flat f] (p : ℕ) :
    cplx f K A₀ p ≃ₗ[A₀] (OModulePresheaf.unit (relProj f A₀)).cochain (testCover f K A₀) p :=
  LinearEquiv.ofBijective (toCochain f K A₀ p) (toCochain_bijective f K A₀ p)

end

variable [IsNoetherianRing A₀] [IsProper f] [Flat f]

/-- The cohomology of the base-changed Čech complex is finitely generated over a noetherian
`A₀`, for `f` proper and flat. -/
lemma finiteCohomology_dif : FiniteCohomology (dif f K A₀) := by
  have := isProper_relProj f A₀
  obtain ⟨h₀, h₁⟩ := OModulePresheaf.cechFinite_unit_of_isProper (relProj f A₀) (testCover f K A₀)
  exact finiteCohomology_of_equiv (dif f K A₀)
    (fun i => (OModulePresheaf.unit (relProj f A₀)).d (testCover f K A₀) i)
    (equivCochain f K A₀) (toCochain_dif f K A₀) ⟨h₀, h₁⟩

end Finiteness

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
