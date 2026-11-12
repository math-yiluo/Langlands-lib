import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.CechData
import Langlands.Algebra.ThickSquareZero
import Mathlib.Tactic.LinearCombination

/-! # The obstruction cochains of a family of transition functions -/

set_option linter.style.haveILetI false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections Langlands.Algebra Langlands.Algebra.PushoutIdealTensor

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

section Surjective

/-- The relative-space map of a surjective algebra map with nil kernel is surjective. -/
lemma surjective_relMap {A A' : Type u} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    (t : A →ₐ[R] A') (ht : Function.Surjective t) (hnil : RingHom.ker t.toRingHom ≤ nilradical A) :
    Function.Surjective (relMap f t).base := by
  have hS : Surjective (Spec.map (CommRingCat.ofHom t.toRingHom)) := by
    constructor
    intro x
    have hx : x ∈ Set.range (PrimeSpectrum.comap t.toRingHom) := by
      rw [range_comap_of_surjective _ t.toRingHom ht,
        (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr hnil]
      trivial
    exact hx
  have : Surjective (relMap f t) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_relMap f t).flip hS
  exact this.surj

end Surjective

section Along

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A : Type u} [CommRing A] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
  {A' : Type u} [CommRing A'] [Algebra R A'] [Algebra P A'] [IsScalarTower R P A']

/-- The section maps of the relative spaces along an algebra map `s : P →ₐ[R] A` whose
relative-space map has the same preimages as that of the structure map. -/
def secMapAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    {p : ℕ} (σ : K.Idx p) :
    Γ(relSpace f P, K.inter σ) ⟶ Γ(relSpace f A, (testCover f K A).inter σ) :=
  (relMap f s).appLE _ _ ((testCover_inter f K A σ).trans (hs _).symm).le

lemma secMapAlong_congr {s s' : P →ₐ[R] A} (e : s = s')
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (hs' : ∀ V, relMap f s' ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    {p : ℕ} (σ : K.Idx p) : secMapAlong f K s hs σ = secMapAlong f K s' hs' σ := by
  subst e
  rfl

lemma secMapAlong_toAlgHom {p : ℕ} (σ : K.Idx p) :
    secMapAlong f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) σ = secMap f K σ := rfl

lemma structureHom_comp_secMapAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    {p : ℕ} (σ : K.Idx p) :
    structureHom f P (K.inter σ) ≫ secMapAlong f K s hs σ =
      CommRingCat.ofHom s.toRingHom ≫ structureHom f A ((testCover f K A).inter σ) :=
  structureHom_comp_appLE f s _ _ _

lemma secMapAlong_res (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    {p q : ℕ} (σ : K.Idx p) (τ : K.Idx q) (h : K.inter τ ≤ K.inter σ)
    (h' : (testCover f K A).inter τ ≤ (testCover f K A).inter σ) (x : Γ(relSpace f P, K.inter σ)) :
    ((relSpace f A).presheaf.map (homOfLE h').op).hom ((secMapAlong f K s hs σ).hom x) =
      (secMapAlong f K s hs τ).hom (((relSpace f P).presheaf.map (homOfLE h).op).hom x) := by
  change (secMapAlong f K s hs σ ≫ (relSpace f A).presheaf.map (homOfLE h').op).hom x =
    ((relSpace f P).presheaf.map (homOfLE h).op ≫ secMapAlong f K s hs τ).hom x
  rw [secMapAlong, secMapAlong, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

lemma testCover_inter_eq_of_comp (h : A →ₐ[R] A')
    (hpre : ∀ V, relMap f (h.comp (IsScalarTower.toAlgHom R P A)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V) {p : ℕ} (σ : K.Idx p) :
    (testCover f K A').inter σ = relMap f h ⁻¹ᵁ (testCover f K A).inter σ := by
  rw [testCover_inter, testCover_inter, ← hpre, relMap_comp, Scheme.Hom.comp_preimage]

/-- The section maps along an `R`-algebra map `h : A →ₐ[R] A'` of `P`-algebras that is compatible
with the structure maps up to the preimages of opens. -/
def testMapAlong (h : A →ₐ[R] A')
    (hpre : ∀ V, relMap f (h.comp (IsScalarTower.toAlgHom R P A)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V) {p : ℕ} (σ : K.Idx p) :
    Γ(relSpace f A, (testCover f K A).inter σ) ⟶ Γ(relSpace f A', (testCover f K A').inter σ) :=
  (relMap f h).appLE _ _ (testCover_inter_eq_of_comp f K h hpre σ).le

lemma secMapAlong_comp_testMapAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (h : A →ₐ[R] A')
    (hpre : ∀ V, relMap f (h.comp (IsScalarTower.toAlgHom R P A)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V)
    (hs' : ∀ V, relMap f (h.comp s) ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V)
    {p : ℕ} (σ : K.Idx p) :
    secMapAlong f K s hs σ ≫ testMapAlong f K h hpre σ = secMapAlong f K (h.comp s) hs' σ := by
  rw [secMapAlong, testMapAlong, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr (relMap_comp f s h).symm _ _ _ _

lemma structureHom_comp_testMapAlong (h : A →ₐ[R] A')
    (hpre : ∀ V, relMap f (h.comp (IsScalarTower.toAlgHom R P A)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V) {p : ℕ} (σ : K.Idx p) :
    structureHom f A _ ≫ testMapAlong f K h hpre σ =
      CommRingCat.ofHom h.toRingHom ≫ structureHom f A' ((testCover f K A').inter σ) :=
  structureHom_comp_appLE f h _ _ _

/-- Two section maps along algebra maps that agree after a surjection `t` differ by an element
of the extension of the kernel of `t`. -/
lemma secMapAlong_sub_mem [IsSeparated f] {A'' : Type u} [CommRing A''] [Algebra R A'']
    (s s' : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (hs' : ∀ V, relMap f s' ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (t : A →ₐ[R] A'') (ht : Function.Surjective t) (hts : t.comp s = t.comp s')
    {p : ℕ} (σ : K.Idx p) (x : Γ(relSpace f P, K.inter σ)) :
    (secMapAlong f K s hs σ).hom x - (secMapAlong f K s' hs' σ).hom x ∈
      Ideal.map (structureHom f A ((testCover f K A).inter σ)).hom (RingHom.ker t.toRingHom) := by
  have := isSeparated_relProj f A
  rw [← ker_appLE_eq_map f t ht _ (isAffineOpen_inter f (testCover f K A) σ), RingHom.mem_ker,
    map_sub,
    sub_eq_zero]
  change (secMapAlong f K s hs σ ≫ (relMap f t).appLE _ _ le_rfl).hom x =
    (secMapAlong f K s' hs' σ ≫ (relMap f t).appLE _ _ le_rfl).hom x
  rw [secMapAlong, secMapAlong, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  have h₀ : relMap f t ≫ relMap f s = relMap f t ≫ relMap f s' := by
    rw [← relMap_comp, ← relMap_comp, hts]
  exact congrArg (fun φ : Γ(relSpace f P, K.inter σ) ⟶
      Γ(relSpace f A'', relMap f t ⁻¹ᵁ (testCover f K A).inter σ) => φ.hom x)
    (appLE_congr h₀ _ _ _ _)

/-- An element killing the generators of an ideal kills its extension. -/
lemma mul_eq_zero_of_mem_map {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) (I : Ideal S)
    (c : S) (hc : ∀ k ∈ I, c * k = 0) (y : T) (hy : y ∈ Ideal.map g I) : g c * y = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [← map_mul, hc k hk, map_zero]
  | zero => exact mul_zero _
  | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

variable {A₀ : Type u} [CommRing A₀] [Algebra P A₀]
  {M : Type u} [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]
  {M' : Type u} [AddCommGroup M'] [Module A₀ M'] [Module P M'] [IsScalarTower P A₀ M']

/-- Naturality of the comparison maps along an `R`-algebra map that is compatible with the
structure maps modulo an ideal annihilated by the coefficients of the target. -/
lemma compMap_natural_of_mul_eq_zero [IsSeparated f] (j : M →ₗ[P] A) (j' : M' →ₗ[P] A')
    (h : A →ₐ[R] A')
    (hpre : ∀ V, relMap f (h.comp (IsScalarTower.toAlgHom R P A)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A') ⁻¹ᵁ V)
    {A'' : Type u} [CommRing A''] [Algebra R A''] (t : A' →ₐ[R] A'') (ht : Function.Surjective t)
    (hts : t.comp (h.comp (IsScalarTower.toAlgHom R P A)) =
      t.comp (IsScalarTower.toAlgHom R P A'))
    (hj' : ∀ m' a, t a = 0 → j' m' * a = 0)
    (φ : M →ₗ[A₀] M') (hφ : ∀ m, j' (φ m) = h (j m)) {p : ℕ} (y : cplx f K A₀ p ⊗[A₀] M)
    (σ : K.Idx p) :
    (testMapAlong f K h hpre σ).hom (compMap f K j p y σ) =
      compMap f K j' p (φ.lTensor _ y) σ := by
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ =>
    have e₁ := congrFun (map_add (compMap f K j p) y₁ y₂) σ
    have e₂ := congrFun (map_add (compMap f K j' p) (φ.lTensor _ y₁) (φ.lTensor _ y₂)) σ
    rw [map_add (φ.lTensor _), e₂, e₁]
    exact (map_add _ _ _).trans (by rw [h₁, h₂]; rfl)
  | tmul t' m =>
    induction t' using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul]
      have e₁ := congrFun (map_add (compMap f K j p) (t₁ ⊗ₜ[A₀] m) (t₂ ⊗ₜ[A₀] m)) σ
      have e₂ := congrFun (map_add (compMap f K j' p) (φ.lTensor _ (t₁ ⊗ₜ[A₀] m))
        (φ.lTensor _ (t₂ ⊗ₜ[A₀] m))) σ
      rw [map_add (φ.lTensor _), e₂, e₁]
      exact (map_add _ _ _).trans (by rw [h₁, h₂]; rfl)
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, compMap_tmul, compMap_tmul]
      have e₁ : (testMapAlong f K h hpre σ).hom
          ((structureHom f A ((testCover f K A).inter σ)).hom (j (a • m))) =
            (structureHom f A' ((testCover f K A').inter σ)).hom (h (j (a • m))) :=
        ConcreteCategory.congr_hom (structureHom_comp_testMapAlong f K h hpre σ) (j (a • m))
      have e₂ : (testMapAlong f K h hpre σ).hom ((secMap (A := A) f K σ).hom (x σ)) =
          (secMapAlong f K (h.comp (IsScalarTower.toAlgHom R P A)) hpre σ).hom (x σ) :=
        ConcreteCategory.congr_hom (secMapAlong_comp_testMapAlong f K
          (IsScalarTower.toAlgHom R P A) (fun _ => rfl) h hpre hpre σ) (x σ)
      refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) e₁ e₂).trans ?_)
      have hmem := secMapAlong_sub_mem f K (h.comp (IsScalarTower.toAlgHom R P A))
        (IsScalarTower.toAlgHom R P A') hpre (fun _ => rfl) t ht hts σ (x σ)
      have hzero := mul_eq_zero_of_mem_map (structureHom f A' ((testCover f K A').inter σ)).hom
        (RingHom.ker t.toRingHom) (h (j (a • m)))
        (fun k hk => by rw [← hφ]; exact hj' _ k (RingHom.mem_ker.mp hk)) _ hmem
      have hc : j' (a • φ m) = h (j (a • m)) := by rw [← φ.map_smul, hφ]
      exact (sub_eq_zero.mp ((mul_sub _ _ _).symm.trans hzero)).trans
        (congrArg (fun c => (structureHom f A' ((testCover f K A').inter σ)).hom c *
          (secMap (A := A') f K σ).hom (x σ)) hc.symm)

end Along

section Pairs

variable {Y : Scheme.{u}} (K' : Y.OrderedAffineCover)

lemma map_map_apply {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE h').op).hom x) =
      (Y.presheaf.map (homOfLE (h.trans h')).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of data on the pairwise intersections `K'.U i ⊓ K'.U j` to a finite
intersection `K'.inter σ`, at the vertices `a` and `b` of `σ`. -/
def pr (u : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j)) {p : ℕ} (σ : K'.Idx p) (a b : Fin (p + 1)) :
    Γ(Y, K'.inter σ) :=
  (Y.presheaf.map (homOfLE (le_inf (K'.inter_le σ a) (K'.inter_le σ b))).op).hom
    (u (σ.1 a) (σ.1 b))

lemma map_pair_congr (u : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j)) {i j i' j' : K'.ι}
    (hi : i = i') (hj : j = j') {V : Y.Opens} (h : V ≤ K'.U i ⊓ K'.U j)
    (h' : V ≤ K'.U i' ⊓ K'.U j') :
    (Y.presheaf.map (homOfLE h).op).hom (u i j) = (Y.presheaf.map (homOfLE h').op).hom (u i' j') := by
  subst hi hj
  rfl

lemma res_pr (u : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j)) {p q : ℕ} (σ : K'.Idx p) (τ : K'.Idx q)
    (h : K'.inter τ ≤ K'.inter σ) (a b : Fin (p + 1)) (a' b' : Fin (q + 1))
    (ha : σ.1 a = τ.1 a') (hb : σ.1 b = τ.1 b') :
    (Y.presheaf.map (homOfLE h).op).hom (pr K' u σ a b) = pr K' u τ a' b' := by
  rw [pr, map_map_apply]
  exact map_pair_congr K' u ha hb _ _

/-- The values of a family of units on the pairwise intersections. -/
abbrev uval (g : ∀ i j : K'.ι, (Γ(Y, K'.U i ⊓ K'.U j))ˣ) : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j) :=
  fun i j => g i j

/-- The inverses of a family of units on the pairwise intersections. -/
abbrev uinv (g : ∀ i j : K'.ι, (Γ(Y, K'.U i ⊓ K'.U j))ˣ) : ∀ i j : K'.ι, Γ(Y, K'.U i ⊓ K'.U j) :=
  fun i j => ((g i j)⁻¹ : (Γ(Y, K'.U i ⊓ K'.U j))ˣ)

lemma pr_val_mul_pr_inv (g : ∀ i j : K'.ι, (Γ(Y, K'.U i ⊓ K'.U j))ˣ) {p : ℕ} (σ : K'.Idx p)
    (a b : Fin (p + 1)) :
    pr K' (uval K' g) σ a b * pr K' (uinv K' g) σ a b = 1 := by
  rw [pr, pr, ← map_mul, Units.mul_inv, map_one]

variable {S : Type u} [CommRing S] (π : Y ⟶ Spec (CommRingCat.of S))

lemma d_one_apply (c : (OModulePresheaf.unit π).cochain K' 1) (s : K'.Idx 2) :
    (show Γ(Y, K'.inter s) from (OModulePresheaf.unit π).d K' 1 c s) =
      (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 0)).op).hom (c (K'.face s 0)) -
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 1)).op).hom (c (K'.face s 1)) +
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 2)).op).hom (c (K'.face s 2)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_sq,
    neg_zsmul, sub_eq_add_neg]
  rfl

lemma d_two_apply (c : (OModulePresheaf.unit π).cochain K' 2) (s : K'.Idx 3) :
    (show Γ(Y, K'.inter s) from (OModulePresheaf.unit π).d K' 2 c s) =
      (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 0)).op).hom (c (K'.face s 0)) -
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 1)).op).hom (c (K'.face s 1)) +
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 2)).op).hom (c (K'.face s 2)) -
        (Y.presheaf.map (homOfLE (K'.inter_le_inter_face s 3)).op).hom (c (K'.face s 3)) := by
  rw [OModulePresheaf.d_apply, Fin.sum_univ_four]
  have e3 : (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) = -1 := by decide
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, e3, pow_zero, pow_one, one_zsmul, neg_one_sq,
    neg_zsmul, sub_eq_add_neg]
  rfl

end Pairs

section Cores

/-- Products in the extension of a square-zero ideal vanish. -/
lemma mul_eq_zero_of_mem_map_sq {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T)
    (I : Ideal S) (hI : ∀ k ∈ I, ∀ k' ∈ I, k * k' = 0) {x y : T} (hx : x ∈ I.map g)
    (hy : y ∈ I.map g) : x * y = 0 := by
  have hxy : x * y ∈ (I * I).map g := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul hx hy
  have hII : I * I = ⊥ :=
    eq_bot_iff.mpr (Ideal.mul_le.mpr fun k hk k' hk' => by
      rw [hI k hk k' hk']
      exact zero_mem _)
  rwa [hII, Ideal.map_bot, Ideal.mem_bot] at hxy

/-- The ring identity behind `dz = 0`. -/
lemma dz_core {T : Type*} [CommRing T] (x01 x02 x12 x13 x23 y02 y03 y13 : T)
    (h02 : x02 * y02 = 1) (h13 : x13 * y13 = 1)
    (H1 : (x12 * x23 * y13 - 1) * (x01 * x13 * y03 - 1) = 0)
    (H2 : (x02 * x23 * y03 - 1) * (x01 * x12 * y02 - 1) = 0) :
    (x12 * x23 * y13 - 1) - (x02 * x23 * y03 - 1) + (x01 * x13 * y03 - 1) -
      (x01 * x12 * y02 - 1) = 0 := by
  linear_combination (x01 * x12 * x23 * y03) * h13 - (x01 * x12 * x23 * y03) * h02 - H1 + H2

/-- The ring identity behind `dθ = δ_* z`. -/
lemma dtheta_core {T : Type*} [CommRing T] (A01 A12 A02 I01 I12 I02 B01 B12 B02 J02 : T)
    (hA01 : A01 * I01 = 1) (hA12 : A12 * I12 = 1) (hA02 : A02 * I02 = 1) (hB02 : B02 * J02 = 1)
    (hcoc : A01 * A12 * I02 = 1)
    (h1 : (B01 - A01) * (B12 - A12) = 0) (h2 : (B01 - A01) * (B02 - A02) = 0)
    (h3 : (B12 - A12) * (B02 - A02) = 0) (h4 : (B02 - A02) * (B02 - A02) = 0) :
    (B12 * I12 - 1) - (B02 * I02 - 1) + (B01 * I01 - 1) = B01 * B12 * J02 - 1 := by
  have hA : A01 * A12 = A02 := by linear_combination A02 * hcoc - A01 * A12 * hA02
  have hI12 : A01 * I02 = I12 := by linear_combination (-A01 * I02) * hA12 + I12 * hcoc
  have hI01 : A12 * I02 = I01 := by linear_combination (-A12 * I02) * hA01 + I01 * hcoc
  have hJ : J02 = I02 - (B02 - A02) * I02 * I02 := by
    linear_combination (-J02 * (1 - (B02 - A02) * I02)) * hA02 + J02 * I02 ^ 2 * h4 +
      (I02 - (B02 - A02) * I02 * I02) * hB02
  rw [hJ]
  linear_combination hA12 + hA01 - 2 * hA02 - I02 * hA - (B12 - A12) * hI12 -
    (B01 - A01) * hI01 - I02 * h1 + (B02 - A02) * I02 * hA02 + (B02 - A02) * I02 ^ 2 * hA +
    A01 * I02 ^ 2 * h3 + A12 * I02 ^ 2 * h2 + (B02 - A02) * I02 ^ 2 * h1

end Cores

section Defs

variable [IsSeparated f]
variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra P A₀]

omit [IsSeparated f] in
lemma structureHom_map (S : Type u) [CommRing S] [Algebra R S] {V W : (relSpace f S).Opens}
    (h : W ≤ V) :
    structureHom f S V ≫ (relSpace f S).presheaf.map (homOfLE h).op = structureHom f S W := by
  rw [structureHom, structureHom, Category.assoc]
  exact congrArg _ (Scheme.Hom.appLE_map (relProj f S) _ _)

omit [IsSeparated f] in
lemma res_mem_map (S : Type u) [CommRing S] [Algebra R S] {V W : (relSpace f S).Opens}
    (h : W ≤ V) (I : Ideal S) {x : Γ(relSpace f S, V)} (hx : x ∈ I.map (structureHom f S V).hom) :
    ((relSpace f S).presheaf.map (homOfLE h).op).hom x ∈ I.map (structureHom f S W).hom := by
  have := Ideal.mem_map_of_mem ((relSpace f S).presheaf.map (homOfLE h).op).hom hx
  rwa [Ideal.map_map, ← CommRingCat.hom_comp, structureHom_map] at this

omit [IsSeparated f] in
lemma secMap_mem_map {A : Type u} [CommRing A] [Algebra R A] [Algebra P A]
    [IsScalarTower R P A] (I : Ideal P) {p : ℕ} (σ : K.Idx p) {x : Γ(relSpace f P, K.inter σ)}
    (hx : x ∈ I.map (structureHom f P (K.inter σ)).hom) :
    (secMap (A := A) f K σ).hom x ∈
      (I.map (algebraMap P A)).map (structureHom f A ((testCover f K A).inter σ)).hom := by
  have := Ideal.mem_map_of_mem (secMap (A := A) f K σ).hom hx
  rwa [Ideal.map_map, ← CommRingCat.hom_comp, structureHom_comp_secMap, CommRingCat.hom_comp,
    ← Ideal.map_map] at this

/-- The multiplicative Čech coboundary of a family of units, minus one, on a triple
intersection. -/
def defect (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (s : K.Idx 2) :
    Γ(relSpace f P, K.inter s) :=
  pr K (uval K g) s 0 1 * pr K (uval K g) s 1 2 * pr K (uinv K g) s 0 2 - 1

variable {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]

lemma exists_zObs (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) :
    ∃ z : cplx f K A₀ 2 ⊗[A₀] Q,
      compMap f K jQ 2 z = fun s => (secMap (A := P) f K s).hom (defect f K g s) := by
  refine (exists_compMap_eq_iff f K jQ (RingHom.ker (algebraMap P A₀)) hjQ _).mpr fun s => ?_
  have := secMap_mem_map (A := P) f K _ s (hg s)
  rwa [Algebra.algebraMap_self, Ideal.map_id] at this

/-- The obstruction cochain `z ∈ C² ⊗ Q` of a family of units whose coboundary is trivial
modulo the kernel of `P → A₀`. -/
def zObs (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) :
    cplx f K A₀ 2 ⊗[A₀] Q :=
  (exists_zObs f K jQ hjQ g hg).choose

lemma compMap_zObs (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) :
    compMap f K jQ 2 (zObs f K jQ hjQ g hg) =
      fun s => (secMap (A := P) f K s).hom (defect f K g s) :=
  (exists_zObs f K jQ hjQ g hg).choose_spec

variable {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F]
  [Module R F]

omit [IsSeparated f] in
lemma preimage_ofDerivation (D : Derivation R P F) (V : (relSpace f P).Opens) :
    relMap f (Thick.ofDerivation D) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P (Thick P F)) ⁻¹ᵁ V :=
  preimage_relMap_eq f (Thick.ofDerivation D) (IsScalarTower.toAlgHom R P (Thick P F))
    (Thick.fstAlgHom R) (AlgHom.ext fun _ => rfl)
    (surjective_relMap f _ Thick.fst_surjective fun x hx =>
      Thick.isNilpotent_of_fst_eq_zero x (RingHom.mem_ker.mp hx)) V

/-- The one-cochain `Θ_* g / g - 1` on the relative space of the thickening `Thick P F`. -/
def thetaCochain (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (σ : K.Idx 1) : Γ(relSpace f (Thick P F), (testCover f K (Thick P F)).inter σ) :=
  (secMapAlong f K (Thick.ofDerivation D) (preimage_ofDerivation f D) σ).hom
      (pr K (uval K g) σ 0 1) *
    (secMap (A := Thick P F) f K σ).hom (pr K (uinv K g) σ 0 1) - 1

lemma thetaCochain_mem (D : Derivation R P F)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (σ : K.Idx 1) :
    thetaCochain f K D g σ ∈ (RingHom.ker (Thick.fstAlgHom R : Thick P F →ₐ[R] P).toRingHom).map
      (structureHom f (Thick P F) ((testCover f K (Thick P F)).inter σ)).hom := by
  have hmem := secMapAlong_sub_mem f K (Thick.ofDerivation D)
    (IsScalarTower.toAlgHom R P (Thick P F)) (preimage_ofDerivation f D) (fun _ => rfl)
    (Thick.fstAlgHom R) Thick.fst_surjective (AlgHom.ext fun _ => rfl) σ (pr K (uval K g) σ 0 1)
  have hone : (secMap (A := Thick P F) f K σ).hom (pr K (uval K g) σ 0 1) *
      (secMap (A := Thick P F) f K σ).hom (pr K (uinv K g) σ 0 1) = 1 := by
    rw [← map_mul, pr_val_mul_pr_inv, map_one]
  have e : thetaCochain f K D g σ =
      ((secMapAlong f K (Thick.ofDerivation D) (preimage_ofDerivation f D) σ).hom
          (pr K (uval K g) σ 0 1) -
        (secMap (A := Thick P F) f K σ).hom (pr K (uval K g) σ 0 1)) *
        (secMap (A := Thick P F) f K σ).hom (pr K (uinv K g) σ 0 1) := by
    unfold thetaCochain
    rw [sub_mul, hone]
  rw [e]
  exact Ideal.mul_mem_right _ _ hmem

lemma exists_thetaObs (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) :
    ∃ θ : cplx f K A₀ 1 ⊗[A₀] F,
      compMap f K (Thick.inr : F →ₗ[P] Thick P F) 1 θ = thetaCochain f K D g :=
  (exists_compMap_eq_iff f K (Thick.inr : F →ₗ[P] Thick P F)
    (RingHom.ker (Thick.fstAlgHom R : Thick P F →ₐ[R] P).toRingHom)
    (fun a => Thick.mem_ker_fstHom_iff a) _).mpr fun σ => thetaCochain_mem f K D g σ

/-- The obstruction cochain `θ ∈ C¹ ⊗ F`: the class of `Θ_* g / g - 1` for the thickening
`Θ = (id, D) : P → Thick P F`. -/
def thetaObs (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) :
    cplx f K A₀ 1 ⊗[A₀] F :=
  (exists_thetaObs (A₀ := A₀) f K D g).choose

lemma compMap_thetaObs (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) :
    compMap f K (Thick.inr : F →ₗ[P] Thick P F) 1 (thetaObs (A₀ := A₀) f K D g) =
      thetaCochain f K D g :=
  (exists_thetaObs (A₀ := A₀) f K D g).choose_spec

/-- The map `δ = D ∘ j : Q → F`. -/
def deltaMap (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ0 : ∀ q, algebraMap P A₀ (jQ q) = 0) (D : Derivation R P F) : Q →ₗ[A₀] F where
  toFun q := D (jQ q)
  map_add' q q' := by simp
  map_smul' a q := by
    obtain ⟨p, rfl⟩ := hπ a
    rw [algebraMap_smul, LinearMap.map_smul, smul_eq_mul, Derivation.leibniz,
      ← algebraMap_smul A₀ (jQ q) (D p), hjQ0, zero_smul, add_zero, RingHom.id_apply,
      algebraMap_smul]

omit [IsSeparated f] in
lemma deltaMap_apply (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ0 : ∀ q, algebraMap P A₀ (jQ q) = 0) (D : Derivation R P F) (q : Q) :
    deltaMap hπ jQ hjQ0 D q = D (jQ q) := rfl

omit [IsSeparated f] [Module A₀ Q] [IsScalarTower P A₀ Q] in
lemma hjQ0_of (jQ : Q →ₗ[P] P) (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (q : Q) : algebraMap P A₀ (jQ q) = 0 :=
  RingHom.mem_ker.mp ((hjQ (jQ q)).mpr ⟨q, rfl⟩)

end Defs

section Cocycle

variable [IsSeparated f]
variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra P A₀]
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]

omit [IsSeparated f] in
lemma res_defect_face (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (t : K.Idx 3)
    (j : Fin 4) :
    ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t j)).op).hom
        (defect f K g (K.face t j)) =
      pr K (uval K g) t (j.succAbove 0) (j.succAbove 1) *
        pr K (uval K g) t (j.succAbove 1) (j.succAbove 2) *
        pr K (uinv K g) t (j.succAbove 0) (j.succAbove 2) - 1 := by
  rw [defect, map_sub, map_mul, map_mul, map_one,
    res_pr K _ (K.face t j) t _ 0 1 (j.succAbove 0) (j.succAbove 1) rfl rfl,
    res_pr K _ (K.face t j) t _ 1 2 (j.succAbove 1) (j.succAbove 2) rfl rfl,
    res_pr K _ (K.face t j) t _ 0 2 (j.succAbove 0) (j.succAbove 2) rfl rfl]

omit [IsSeparated f] [Module A₀ Q] [IsScalarTower P A₀ Q] in
lemma ker_mul_eq_zero (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (hsq : ∀ q q', jQ q * jQ q' = 0) :
    ∀ k ∈ RingHom.ker (algebraMap P A₀), ∀ k' ∈ RingHom.ker (algebraMap P A₀), k * k' = 0 := by
  intro k hk k' hk'
  obtain ⟨q, rfl⟩ := (hjQ k).mp hk
  obtain ⟨q', rfl⟩ := (hjQ k').mp hk'
  exact hsq q q'

omit [IsSeparated f] [Module A₀ Q] [IsScalarTower P A₀ Q] in
/-- The alternating sum of the restricted defects over a quadruple intersection vanishes. -/
lemma defect_alt_sum (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (hsq : ∀ q q', jQ q * jQ q' = 0)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) (t : K.Idx 3) :
    ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t 0)).op).hom
          (defect f K g (K.face t 0)) -
        ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t 1)).op).hom
          (defect f K g (K.face t 1)) +
        ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t 2)).op).hom
          (defect f K g (K.face t 2)) -
        ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t 3)).op).hom
          (defect f K g (K.face t 3)) = 0 := by
  have hI := ker_mul_eq_zero (A₀ := A₀) jQ hjQ hsq
  have hmem : ∀ j : Fin 4,
      ((relSpace f P).presheaf.map (homOfLE (K.inter_le_inter_face t j)).op).hom
          (defect f K g (K.face t j)) ∈
        (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter t)).hom :=
    fun j => res_mem_map f P _ _ (hg _)
  have H1 := mul_eq_zero_of_mem_map_sq _ _ hI (hmem 0) (hmem 2)
  have H2 := mul_eq_zero_of_mem_map_sq _ _ hI (hmem 1) (hmem 3)
  rw [res_defect_face, res_defect_face] at H1 H2
  rw [res_defect_face, res_defect_face, res_defect_face, res_defect_face]
  exact dz_core (pr K (uval K g) t 0 1) (pr K (uval K g) t 0 2) (pr K (uval K g) t 1 2)
    (pr K (uval K g) t 1 3) (pr K (uval K g) t 2 3) (pr K (uinv K g) t 0 2)
    (pr K (uinv K g) t 0 3) (pr K (uinv K g) t 1 3) (pr_val_mul_pr_inv K g t 0 2)
    (pr_val_mul_pr_inv K g t 1 3) H1 H2

/-- The obstruction cochain `z` is a cocycle: `d z = 0`. -/
theorem dif_zObs [Flat f] (jQ : Q →ₗ[P] P) (hjQinj : Function.Injective jQ)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (hsq : ∀ q q', jQ q * jQ q' = 0)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) :
    (dif f K A₀ 2).rTensor Q (zObs f K jQ hjQ g hg) = 0 := by
  apply compMap_injective f K jQ hjQinj 3
  rw [map_zero, compMap_dif, compMap_zObs]
  funext t
  refine (d_two_apply (testCover f K P) (relProj f P) _ t).trans ?_
  rw [secMap_res f K ((testCover f K P).face t 0) t (K.inter_le_inter_face t 0),
    secMap_res f K ((testCover f K P).face t 1) t (K.inter_le_inter_face t 1),
    secMap_res f K ((testCover f K P).face t 2) t (K.inter_le_inter_face t 2),
    secMap_res f K ((testCover f K P).face t 3) t (K.inter_le_inter_face t 3),
    ← map_sub, ← map_add, ← map_sub]
  exact (congrArg (secMap (A := P) f K t).hom
    (defect_alt_sum f K jQ hjQ hsq g hg t)).trans (map_zero _)

end Cocycle

section Faces

variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A : Type u} [CommRing A] [Algebra R A] [Algebra P A] [IsScalarTower R P A]

lemma res_secMapAlong_face (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (u : ∀ i j : K.ι, Γ(relSpace f P, K.U i ⊓ K.U j)) {p : ℕ} (t : K.Idx (p + 1))
    (j : Fin (p + 2)) (a b : Fin (p + 1)) (a' b' : Fin (p + 2))
    (ha : t.1 (j.succAbove a) = t.1 a') (hb : t.1 (j.succAbove b) = t.1 b') :
    ((relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face t j)).op).hom
        ((secMapAlong f K s hs ((testCover f K A).face t j)).hom
          (pr K u ((testCover f K A).face t j) a b)) =
      (secMapAlong f K s hs t).hom (pr K u t a' b') :=
  (secMapAlong_res f K s hs _ t (K.inter_le_inter_face t j) _ _).trans
    (congrArg _ (res_pr K u (K.face t j) t _ a b a' b' ha hb))

lemma res_secMap_face (u : ∀ i j : K.ι, Γ(relSpace f P, K.U i ⊓ K.U j)) {p : ℕ}
    (t : K.Idx (p + 1)) (j : Fin (p + 2)) (a b : Fin (p + 1)) (a' b' : Fin (p + 2))
    (ha : t.1 (j.succAbove a) = t.1 a') (hb : t.1 (j.succAbove b) = t.1 b') :
    ((relSpace f A).presheaf.map (homOfLE ((testCover f K A).inter_le_inter_face t j)).op).hom
        ((secMap (A := A) f K ((testCover f K A).face t j)).hom
          (pr K u ((testCover f K A).face t j) a b)) =
      (secMap (A := A) f K t).hom (pr K u t a' b') :=
  res_secMapAlong_face f K (IsScalarTower.toAlgHom R P A) (fun _ => rfl) u t j a b a' b' ha hb

end Faces

section Theta

variable [IsSeparated f]
variable {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]

variable (A₀ F) in
/-- The reduction `Thick P F → Thick A₀ F`, `(p, f) ↦ (p mod J, f)`. -/
def thickRed : Thick P F →ₐ[R] Thick A₀ F where
  toRingHom := Thick.map (algebraMap P A₀) (fun p x => (algebraMap_smul A₀ p x).symm)
  commutes' r := by
    ext
    · simp [IsScalarTower.algebraMap_apply R P A₀]
    · simp

omit [IsSeparated f] [Module R F] in
@[simp] lemma fst_thickRed (x : Thick P F) :
    Thick.fst (thickRed (R := R) A₀ F x) = algebraMap P A₀ (Thick.fst x) :=
  Thick.fst_map (algebraMap P A₀) (fun p x => (algebraMap_smul A₀ p x).symm) x

omit [IsSeparated f] [Module R F] in
@[simp] lemma snd_thickRed (x : Thick P F) :
    Thick.snd (thickRed (R := R) A₀ F x) = Thick.snd x :=
  Thick.snd_map (algebraMap P A₀) (fun p x => (algebraMap_smul A₀ p x).symm) x

variable (A₀) in
/-- The map `Θ' = (π, D) : P → Thick A₀ F`. -/
def thetaRed (D : Derivation R P F) : P →ₐ[R] Thick A₀ F :=
  (thickRed A₀ F).comp (Thick.ofDerivation D)

omit [IsSeparated f] [Module R F] in
lemma thickRed_comp :
    (thickRed A₀ F).comp (IsScalarTower.toAlgHom R P (Thick P F)) =
      IsScalarTower.toAlgHom R P (Thick A₀ F) :=
  AlgHom.ext fun p => by ext <;> simp [Thick.algebraMap_apply]

omit [IsSeparated f] in
lemma fst_comp_thetaRed (D : Derivation R P F) :
    (Thick.fstAlgHom R).comp (thetaRed A₀ D) =
      (Thick.fstAlgHom R).comp (IsScalarTower.toAlgHom R P (Thick A₀ F)) :=
  AlgHom.ext fun p => by simp [thetaRed, Thick.algebraMap_apply]

omit [IsSeparated f] [Module R F] in
lemma surjective_relMap_fst :
    Function.Surjective (relMap f (Thick.fstAlgHom R : Thick A₀ F →ₐ[R] A₀)).base :=
  surjective_relMap f _ Thick.fst_surjective fun x hx =>
    Thick.isNilpotent_of_fst_eq_zero x (RingHom.mem_ker.mp hx)

omit [IsSeparated f] [Module R F] in
lemma preimage_thickRed (V : (relSpace f P).Opens) :
    relMap f ((thickRed A₀ F).comp (IsScalarTower.toAlgHom R P (Thick P F))) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P (Thick A₀ F)) ⁻¹ᵁ V := by
  rw [thickRed_comp]

omit [IsSeparated f] in
lemma preimage_thetaRed (D : Derivation R P F) (V : (relSpace f P).Opens) :
    relMap f (thetaRed A₀ D) ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P (Thick A₀ F)) ⁻¹ᵁ V :=
  preimage_relMap_eq f _ _ (Thick.fstAlgHom R) (fst_comp_thetaRed D) (surjective_relMap_fst f) V

omit [IsSeparated f] in
lemma preimage_thetaRed_comp (D : Derivation R P F) (V : (relSpace f P).Opens) :
    relMap f ((thetaRed A₀ D).comp (IsScalarTower.toAlgHom R P P)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P (Thick A₀ F)) ⁻¹ᵁ V :=
  preimage_thetaRed f D V

omit [IsSeparated f] [Algebra R P] [IsScalarTower R P A₀] [Module R F] in
lemma inr_mul_eq_zero (x : F) (a : Thick A₀ F) (ha : Thick.fstAlgHom R a = 0) :
    ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) x * a = 0 := by
  have : a = Thick.inr (Thick.snd a) := by
    ext
    · simpa using ha
    · simp
  rw [this]
  exact Thick.inr_mul_inr _ _

lemma compMap_thetaObs_red_apply (D : Derivation R P F)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (σ : K.Idx 1) :
    (show Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter σ) from
      compMap f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) 1
        (thetaObs (A₀ := A₀) f K D g) σ) =
      (secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) σ).hom (pr K (uval K g) σ 0 1) *
        (secMap (A := Thick A₀ F) f K σ).hom (pr K (uinv K g) σ 0 1) - 1 := by
  have h := compMap_natural_of_mul_eq_zero f K (Thick.inr : F →ₗ[P] Thick P F)
    ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) (thickRed A₀ F)
    (preimage_thickRed f) (Thick.fstAlgHom R) Thick.fst_surjective
    (by rw [thickRed_comp]) (inr_mul_eq_zero (R := R))
    (LinearMap.id : F →ₗ[A₀] F) (fun x => by ext <;> simp) (thetaObs (A₀ := A₀) f K D g) σ
  have e : (LinearMap.id : F →ₗ[A₀] F).lTensor (cplx f K A₀ 1) (thetaObs (A₀ := A₀) f K D g) =
      thetaObs (A₀ := A₀) f K D g := by
    rw [LinearMap.lTensor_id, LinearMap.id_apply]
  have e₁ := ConcreteCategory.congr_hom (secMapAlong_comp_testMapAlong f K
    (Thick.ofDerivation D) (preimage_ofDerivation f D) (thickRed A₀ F) (preimage_thickRed f)
    (preimage_thetaRed f D) σ) (pr K (uval K g) σ 0 1)
  have e₂ := (ConcreteCategory.congr_hom (secMapAlong_comp_testMapAlong f K
    (IsScalarTower.toAlgHom R P (Thick P F)) (fun _ => rfl) (thickRed A₀ F) (preimage_thickRed f)
    (preimage_thickRed f) σ) (pr K (uinv K g) σ 0 1)).trans
    (congrArg (fun φ : Γ(relSpace f P, K.inter σ) ⟶
        Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter σ) =>
          φ.hom (pr K (uinv K g) σ 0 1))
      (secMapAlong_congr f K (thickRed_comp (R := R) (A₀ := A₀) (F := F)) _ (fun _ => rfl) σ))
  refine (congrArg (fun y => compMap f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) 1
    y σ) e.symm).trans (h.symm.trans ?_)
  refine (congrArg (testMapAlong f K (thickRed A₀ F) (preimage_thickRed f) σ).hom
    (congrFun (compMap_thetaObs (A₀ := A₀) f K D g) σ)).trans ?_
  unfold thetaCochain
  rw [map_sub, map_mul, map_one]
  exact congrArg₂ (fun a b => a * b - 1) e₁ e₂

/-- The first obstruction cochain on the relative space of `Thick A₀ F`. -/
lemma compMap_thetaObs_red (D : Derivation R P F)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) :
    compMap f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) 1
        (thetaObs (A₀ := A₀) f K D g) =
      fun σ : K.Idx 1 =>
        ((secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) σ).hom (pr K (uval K g) σ 0 1) *
          (secMap (A := Thick A₀ F) f K σ).hom (pr K (uinv K g) σ 0 1) - 1 :
            Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter σ)) :=
  funext fun σ => compMap_thetaObs_red_apply f K D g σ

lemma compMap_deltaZ (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) (s : K.Idx 2) :
    (show Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter s) from
      compMap f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) 2
        ((deltaMap hπ jQ (hjQ0_of jQ hjQ) D).lTensor (cplx f K A₀ 2) (zObs f K jQ hjQ g hg)) s) =
      (secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) s).hom (defect f K g s) := by
  have h := compMap_natural_of_mul_eq_zero f K (A := P) jQ
    ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) (thetaRed A₀ D)
    (preimage_thetaRed_comp f D) (Thick.fstAlgHom R) Thick.fst_surjective
    (AlgHom.ext fun p => by simp [thetaRed, Thick.algebraMap_apply]) (inr_mul_eq_zero (R := R))
    (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
    (fun q => by
      ext
      · simp [thetaRed, hjQ0_of jQ hjQ q]
      · simp [thetaRed, deltaMap_apply]) (zObs f K jQ hjQ g hg) s
  refine h.symm.trans ?_
  refine (congrArg (testMapAlong f K (thetaRed A₀ D) (preimage_thetaRed_comp f D) s).hom
    (congrFun (compMap_zObs f K jQ hjQ g hg) s)).trans ?_
  have e := ConcreteCategory.congr_hom (secMapAlong_comp_testMapAlong f K
    (IsScalarTower.toAlgHom R P P) (fun _ => rfl) (thetaRed A₀ D) (preimage_thetaRed_comp f D)
    (preimage_thetaRed_comp f D) s) (defect f K g s)
  exact e.trans (congrArg (fun φ : Γ(relSpace f P, K.inter s) ⟶
      Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter s) => φ.hom (defect f K g s))
    (secMapAlong_congr f K (AlgHom.ext fun _ => rfl) _ _ s))

omit [IsSeparated f] [Module P F] [IsScalarTower P A₀ F] [Module R F] in
lemma secMap_defect_red (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) (s : K.Idx 2) :
    (secMap (A := Thick A₀ F) f K s).hom (defect f K g s) = 0 := by
  have h := secMap_mem_map (A := Thick A₀ F) f K _ s (hg s)
  have hbot : (RingHom.ker (algebraMap P A₀)).map (algebraMap P (Thick A₀ F)) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [Thick.algebraMap_apply, hx, map_zero]
  rwa [hbot, Ideal.map_bot, Ideal.mem_bot] at h

lemma thetaRed_sub_mem (D : Derivation R P F) {p : ℕ} (σ : K.Idx p)
    (x : Γ(relSpace f P, K.inter σ)) :
    (secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) σ).hom x -
        (secMap (A := Thick A₀ F) f K σ).hom x ∈
      (RingHom.ker (Thick.fstAlgHom R : Thick A₀ F →ₐ[R] A₀).toRingHom).map
        (structureHom f (Thick A₀ F) ((testCover f K (Thick A₀ F)).inter σ)).hom :=
  secMapAlong_sub_mem f K (thetaRed A₀ D) (IsScalarTower.toAlgHom R P (Thick A₀ F))
    (preimage_thetaRed f D) (fun _ => rfl) (Thick.fstAlgHom R) Thick.fst_surjective
    (fst_comp_thetaRed D) σ x

omit [IsSeparated f] [Algebra R P] [IsScalarTower R P A₀] [Algebra P A₀] [Module P F]
  [IsScalarTower P A₀ F] [Module R F] in
lemma ker_fst_mul (k : Thick A₀ F)
    (hk : k ∈ RingHom.ker (Thick.fstAlgHom R : Thick A₀ F →ₐ[R] A₀).toRingHom) (k' : Thick A₀ F)
    (hk' : k' ∈ RingHom.ker (Thick.fstAlgHom R : Thick A₀ F →ₐ[R] A₀).toRingHom) :
    k * k' = 0 := by
  have h₀ : Thick.fst k = 0 := RingHom.mem_ker.mp hk
  have h₁ : Thick.fst k' = 0 := RingHom.mem_ker.mp hk'
  ext <;> simp [h₀, h₁]

lemma dif_thetaObs_apply (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) (s : K.Idx 2) :
    (show Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter s) from
      compMap f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P) 2
        ((dif f K A₀ 1).rTensor F (thetaObs (A₀ := A₀) f K D g)) s) =
      (secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) s).hom (defect f K g s) := by
  refine (congrFun (compMap_dif f K _ 1 _) s).trans ?_
  rw [compMap_thetaObs_red f K D g]
  refine (d_one_apply (testCover f K (Thick A₀ F)) (relProj f (Thick A₀ F)) _ s).trans ?_
  simp only [map_sub, map_mul, map_one]
  rw [res_secMapAlong_face f K (thetaRed A₀ D) (preimage_thetaRed f D) (uval K g) s 0 0 1 1 2 rfl rfl,
    res_secMapAlong_face f K (thetaRed A₀ D) (preimage_thetaRed f D) (uval K g) s 1 0 1 0 2 rfl rfl,
    res_secMapAlong_face f K (thetaRed A₀ D) (preimage_thetaRed f D) (uval K g) s 2 0 1 0 1 rfl rfl,
    res_secMap_face f K (uinv K g) s 0 0 1 1 2 rfl rfl,
    res_secMap_face f K (uinv K g) s 1 0 1 0 2 rfl rfl,
    res_secMap_face f K (uinv K g) s 2 0 1 0 1 rfl rfl]
  unfold defect
  simp only [map_sub, map_mul, map_one]
  set B := secMapAlong f K (thetaRed A₀ D) (preimage_thetaRed f D) s with hB
  set A := secMap (A := Thick A₀ F) f K s with hA
  have hunit : ∀ (φ : Γ(relSpace f P, K.inter s) ⟶
      Γ(relSpace f (Thick A₀ F), (testCover f K (Thick A₀ F)).inter s)) (a b : Fin 3),
      φ.hom (pr K (uval K g) s a b) * φ.hom (pr K (uinv K g) s a b) = 1 := fun φ a b => by
    rw [← map_mul, pr_val_mul_pr_inv, map_one]
  have hcoc := secMap_defect_red (F := F) f K g hg s
  unfold defect at hcoc
  simp only [map_sub, map_mul, map_one, sub_eq_zero] at hcoc
  have hsq : ∀ a b a' b' : Fin 3,
      (B.hom (pr K (uval K g) s a b) - A.hom (pr K (uval K g) s a b)) *
        (B.hom (pr K (uval K g) s a' b') - A.hom (pr K (uval K g) s a' b')) = 0 :=
    fun a b a' b' => mul_eq_zero_of_mem_map_sq _ _ (ker_fst_mul (R := R))
      (thetaRed_sub_mem f K D s _) (thetaRed_sub_mem f K D s _)
  exact dtheta_core _ _ _ _ _ _ _ _ _ _ (hunit A 0 1) (hunit A 1 2) (hunit A 0 2) (hunit B 0 2) hcoc
    (hsq 0 1 1 2) (hsq 0 1 0 2) (hsq 1 2 0 2) (hsq 0 2 0 2)

/-- The obstruction cochains satisfy `d θ = δ_* z`. -/
theorem dif_thetaObs [Flat f] (hπ : Function.Surjective (algebraMap P A₀)) (jQ : Q →ₗ[P] P)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ q, jQ q = a)
    (D : Derivation R P F) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom) :
    (dif f K A₀ 1).rTensor F (thetaObs (A₀ := A₀) f K D g) =
      (deltaMap hπ jQ (hjQ0_of jQ hjQ) D).lTensor (cplx f K A₀ 2) (zObs f K jQ hjQ g hg) := by
  apply compMap_injective f K ((Thick.inr : F →ₗ[A₀] Thick A₀ F).restrictScalars P)
    Thick.inr_injective 2
  funext s
  exact (dif_thetaObs_apply f K D g hg s).trans (compMap_deltaZ f K hπ jQ hjQ D g hg s).symm

end Theta

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
