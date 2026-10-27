import Langlands.Representation.Filtration.InvariantBilinear
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.Length

/-! Bilinear forms with covariance tested through two separate ambient monoids. -/

noncomputable section

namespace Langlands.MixedBilinear

universe uK uG uH uI uJ uV uW uX uY

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {H : Type uH} [Monoid H]
variable {I : Type uI} {J : Type uJ}
variable {V : Type uV} {W : Type uW} {X : Type uX} {Y : Type uY}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- The covariance law of `B` for every test `i`, acting through `a i` in the first
argument and through `b i` in the second argument. -/
def IsCovariant (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) (B : V →ₗ[k] W →ₗ[k] k) : Prop :=
  ∀ i v w, B (ρ (a i) v) (σ (b i) w) = χ i * B v w

theorem IsCovariant.zero (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) : IsCovariant a b χ ρ σ 0 := by
  intro i v w
  simp

theorem IsCovariant.add {a : I → G} {b : I → H} {χ : I → k} {ρ : Representation k G V}
    {σ : Representation k H W} {B C : V →ₗ[k] W →ₗ[k] k}
    (hB : IsCovariant a b χ ρ σ B) (hC : IsCovariant a b χ ρ σ C) :
    IsCovariant a b χ ρ σ (B + C) := by
  intro i v w
  change B (ρ (a i) v) (σ (b i) w) + C (ρ (a i) v) (σ (b i) w) =
    χ i * (B v w + C v w)
  rw [hB, hC, mul_add]

theorem IsCovariant.smul {a : I → G} {b : I → H} {χ : I → k} {ρ : Representation k G V}
    {σ : Representation k H W} (c : k) {B : V →ₗ[k] W →ₗ[k] k}
    (hB : IsCovariant a b χ ρ σ B) : IsCovariant a b χ ρ σ (c • B) := by
  intro i v w
  change c * B (ρ (a i) v) (σ (b i) w) = χ i * (c * B v w)
  rw [hB, mul_left_comm]

/-- The actual space of bilinear forms satisfying every tested mixed covariance law. -/
def forms (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) : Submodule k (V →ₗ[k] W →ₗ[k] k) where
  carrier := {B | IsCovariant a b χ ρ σ B}
  zero_mem' := IsCovariant.zero a b χ ρ σ
  add_mem' := IsCovariant.add
  smul_mem' := IsCovariant.smul

instance formsAddCommGroup (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) : AddCommGroup (forms a b χ ρ σ) := by
  exact @Submodule.addCommGroup k (V →ₗ[k] W →ₗ[k] k) _ _ _ (forms a b χ ρ σ)

theorem mem_forms_iff_isCovariant {a : I → G} {b : I → H} {χ : I → k}
    {ρ : Representation k G V} {σ : Representation k H W} {B : V →ₗ[k] W →ₗ[k] k} :
    B ∈ forms a b χ ρ σ ↔ IsCovariant a b χ ρ σ B :=
  Iff.rfl

theorem mem_forms {a : I → G} {b : I → H} {χ : I → k}
    {ρ : Representation k G V} {σ : Representation k H W} {B : V →ₗ[k] W →ₗ[k] k} :
    B ∈ forms a b χ ρ σ ↔ ∀ i v w, B (ρ (a i) v) (σ (b i) w) = χ i * B v w :=
  Iff.rfl

/-- With no tests, every bilinear form is covariant. -/
theorem forms_eq_top_of_isEmpty [IsEmpty I] (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W) :
    forms a b χ ρ σ = ⊤ := by
  ext B
  simp only [Submodule.mem_top, iff_true]
  intro i
  exact isEmptyElim i

/-- Restricting the test family along any map enlarges the form space. -/
theorem forms_le_comp (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) (t : J → I) :
    forms a b χ ρ σ ≤ forms (a ∘ t) (b ∘ t) (χ ∘ t) ρ σ :=
  fun _ hB j v w => hB (t j) v w

/-- Concatenating two test families intersects the two form spaces. -/
theorem forms_sumElim (a : I → G) (b : I → H) (χ : I → k) (a' : J → G) (b' : J → H)
    (χ' : J → k) (ρ : Representation k G V) (σ : Representation k H W) :
    forms (Sum.elim a a') (Sum.elim b b') (Sum.elim χ χ') ρ σ =
      forms a b χ ρ σ ⊓ forms a' b' χ' ρ σ := by
  ext B
  constructor
  · intro hB
    exact ⟨fun i => hB (Sum.inl i), fun j => hB (Sum.inr j)⟩
  · rintro ⟨hB, hB'⟩ (i | j)
    · exact hB i
    · exact hB' j

/-- Testing every element of one common monoid through the identity recovers the
single-group covariance space of `Langlands.InvariantBilinear`. -/
theorem forms_id (χ : G → k) (ρ : Representation k G V) (σ : Representation k G W) :
    forms (id : G → G) (id : G → G) χ ρ σ = InvariantBilinear.forms ρ σ χ :=
  rfl

/-- Extended-natural length of the full mixed covariance space. -/
def length (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) : ℕ∞ :=
  Module.length k (forms a b χ ρ σ)

theorem length_id (χ : G → k) (ρ : Representation k G V) (σ : Representation k G W) :
    length (id : G → G) (id : G → G) χ ρ σ = InvariantBilinear.length ρ σ χ :=
  rfl

/-- Pullback in the first argument along an actual `G`-intertwiner. -/
def comapLeft {a : I → G} (b : I → H) (χ : I → k) {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k H W) (f : ρ.IntertwiningMap τ) :
    forms a b χ τ σ →ₗ[k] forms a b χ ρ σ where
  toFun B := ⟨B.val.comp f.toLinearMap, by
    intro i v w
    change B.val (f (ρ (a i) v)) (σ (b i) w) = χ i * B.val (f v) w
    rw [f.isIntertwining]
    exact B.property i (f v) w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem comapLeft_apply {a : I → G} (b : I → H) (χ : I → k) {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k H W) (f : ρ.IntertwiningMap τ)
    (B : forms a b χ τ σ) (v : V) (w : W) :
    (comapLeft b χ σ f B).val v w = B.val (f v) w :=
  rfl

theorem comapLeft_injective {a : I → G} (b : I → H) (χ : I → k) {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k H W) (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Injective (comapLeft (a := a) b χ σ f) := by
  intro B C h
  apply Subtype.ext
  ext x w
  obtain ⟨v, rfl⟩ := hf x
  exact congrArg (fun D : forms a b χ ρ σ => D.val v w) h

/-- Pullback in the second argument along an actual `H`-intertwiner. -/
def comapRight (a : I → G) {b : I → H} (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} {υ : Representation k H Y} (f : σ.IntertwiningMap υ) :
    forms a b χ ρ υ →ₗ[k] forms a b χ ρ σ where
  toFun B := ⟨B.val.compl₂ f.toLinearMap, by
    intro i v w
    change B.val (ρ (a i) v) (f (σ (b i) w)) = χ i * B.val v (f w)
    rw [f.isIntertwining]
    exact B.property i v (f w)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem comapRight_apply (a : I → G) {b : I → H} (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} {υ : Representation k H Y} (f : σ.IntertwiningMap υ)
    (B : forms a b χ ρ υ) (v : V) (w : W) :
    (comapRight a χ ρ f B).val v w = B.val v (f w) :=
  rfl

theorem comapRight_injective (a : I → G) {b : I → H} (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} {υ : Representation k H Y} (f : σ.IntertwiningMap υ)
    (hf : Function.Surjective f) : Function.Injective (comapRight a (b := b) χ ρ f) := by
  intro B C h
  apply Subtype.ext
  ext v y
  obtain ⟨w, rfl⟩ := hf y
  exact congrArg (fun D : forms a b χ ρ σ => D.val v w) h

/-- An equivalence of `G`-representations in the first argument identifies the form spaces. -/
def equivLeft {a : I → G} (b : I → H) (χ : I → k) {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k H W) (e : ρ.Equiv τ) :
    forms a b χ ρ σ ≃ₗ[k] forms a b χ τ σ :=
  { comapLeft b χ σ e.symm.toIntertwiningMap with
    invFun := comapLeft b χ σ e.toIntertwiningMap
    left_inv := by
      intro B
      apply Subtype.ext
      ext v w
      exact congrArg (fun x => B.val x w) (e.symm_apply_apply v)
    right_inv := by
      intro B
      apply Subtype.ext
      ext x w
      exact congrArg (fun v => B.val v w) (e.apply_symm_apply x) }

theorem length_congr_left {a : I → G} (b : I → H) (χ : I → k) {ρ : Representation k G V}
    {τ : Representation k G X} (σ : Representation k H W) (e : ρ.Equiv τ) :
    length a b χ ρ σ = length a b χ τ σ :=
  (equivLeft b χ σ e).length_eq

/-- An equivalence of `H`-representations in the second argument identifies the form
spaces. -/
def equivRight (a : I → G) {b : I → H} (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} {υ : Representation k H Y} (e : σ.Equiv υ) :
    forms a b χ ρ σ ≃ₗ[k] forms a b χ ρ υ :=
  { comapRight a χ ρ e.symm.toIntertwiningMap with
    invFun := comapRight a χ ρ e.toIntertwiningMap
    left_inv := by
      intro B
      apply Subtype.ext
      ext v w
      exact congrArg (fun y => B.val v y) (e.symm_apply_apply w)
    right_inv := by
      intro B
      apply Subtype.ext
      ext v y
      exact congrArg (fun w => B.val v w) (e.apply_symm_apply y) }

theorem length_congr_right (a : I → G) {b : I → H} (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} {υ : Representation k H Y} (e : σ.Equiv υ) :
    length a b χ ρ σ = length a b χ ρ υ :=
  (equivRight a χ ρ e).length_eq

/-- Exchanging the two arguments, and with them the two test maps, preserves the
mixed covariance laws over the same tests. -/
def flipEquiv (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    forms a b χ ρ σ ≃ₗ[k] forms b a χ σ ρ where
  toFun B := ⟨B.val.flip, fun i w v => B.property i v w⟩
  invFun B := ⟨B.val.flip, fun i v w => B.property i w v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem flipEquiv_apply (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) (B : forms a b χ ρ σ) (w : W) (v : V) :
    (flipEquiv a b χ ρ σ B).val w v = B.val v w :=
  rfl

theorem length_flip (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    length a b χ ρ σ = length b a χ σ ρ :=
  (flipEquiv a b χ ρ σ).length_eq

section Subrepresentations

variable {M : Type*} [Monoid M] {U : Type*} [AddCommGroup U] [Module k U]

/-- The inclusion of an actual subrepresentation as an intertwiner. -/
def inclusion {π : Representation k M U} (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

@[simp]
theorem inclusion_apply {π : Representation k M U} (S : Subrepresentation π)
    (u : S.toSubmodule) : inclusion S u = u :=
  rfl

/-- The top subrepresentation is equivalent to the whole representation. -/
def topEquiv (π : Representation k M U) :
    (⊤ : Subrepresentation π).toRepresentation.Equiv π where
  toLinearMap := (⊤ : Subrepresentation π).toSubmodule.subtype
  isIntertwining' _ := rfl
  invFun u := ⟨u, trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Subrepresentations

/-- Forms on the top subrepresentation in the first argument are forms on `ρ`. -/
def topEquivLeft (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    forms a b χ (⊤ : Subrepresentation ρ).toRepresentation σ ≃ₗ[k] forms a b χ ρ σ :=
  equivLeft b χ σ (topEquiv ρ)

/-- Forms on the top subrepresentation in the second argument are forms on `σ`. -/
def topEquivRight (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    forms a b χ ρ (⊤ : Subrepresentation σ).toRepresentation ≃ₗ[k] forms a b χ ρ σ :=
  equivRight a χ ρ (topEquiv σ)

theorem length_top_left (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    length a b χ (⊤ : Subrepresentation ρ).toRepresentation σ = length a b χ ρ σ :=
  (topEquivLeft a b χ ρ σ).length_eq

theorem length_top_right (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    length a b χ ρ (⊤ : Subrepresentation σ).toRepresentation = length a b χ ρ σ :=
  (topEquivRight a b χ ρ σ).length_eq

instance subsingleton_bot_left (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W) :
    Subsingleton (forms a b χ (⊥ : Subrepresentation ρ).toRepresentation σ) := by
  constructor
  intro B C
  apply Subtype.ext
  ext ⟨v, hv⟩ w
  have hv' : v = 0 := hv
  subst hv'
  change B.val 0 w = C.val 0 w
  simp

instance subsingleton_bot_right (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W) :
    Subsingleton (forms a b χ ρ (⊥ : Subrepresentation σ).toRepresentation) := by
  constructor
  intro B C
  apply Subtype.ext
  ext v ⟨w, hw⟩
  have hw' : w = 0 := hw
  subst hw'
  change B.val v 0 = C.val v 0
  simp

theorem length_bot_left (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    length a b χ (⊥ : Subrepresentation ρ).toRepresentation σ = 0 :=
  Module.length_eq_zero_iff.mpr inferInstance

theorem length_bot_right (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    (σ : Representation k H W) :
    length a b χ ρ (⊥ : Subrepresentation σ).toRepresentation = 0 :=
  Module.length_eq_zero_iff.mpr inferInstance

/-- Restriction of the first argument to an actual subrepresentation. -/
def restrictLeft (a : I → G) (b : I → H) (χ : I → k) {ρ : Representation k G V}
    (σ : Representation k H W) (S : Subrepresentation ρ) :
    forms a b χ ρ σ →ₗ[k] forms a b χ S.toRepresentation σ :=
  comapLeft b χ σ (inclusion S)

/-- Restriction of the second argument to an actual subrepresentation. -/
def restrictRight (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} (S : Subrepresentation σ) :
    forms a b χ ρ σ →ₗ[k] forms a b χ ρ S.toRepresentation :=
  comapRight a χ ρ (inclusion S)

/-- A form whose restriction to `S` vanishes in the first argument descends to the
actual quotient representation, with the same tests. -/
def descendLeft (a : I → G) (b : I → H) (χ : I → k) {ρ : Representation k G V}
    (σ : Representation k H W) (S : Subrepresentation ρ) :
    LinearMap.ker (restrictLeft a b χ σ S) →ₗ[k]
      forms a b χ (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv))
        σ := by
  have hker (B : LinearMap.ker (restrictLeft a b χ σ S)) :
      S.toSubmodule ≤ LinearMap.ker B.val.val := by
    intro v hv
    exact congrArg (fun C : forms a b χ S.toRepresentation σ => C.val ⟨v, hv⟩) B.property
  refine
    { toFun := fun B => ⟨S.toSubmodule.liftQ B.val.val (hker B), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro i q w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    exact B.val.property i v w
  · intro B C
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl
  · intro c B
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl

@[simp]
theorem descendLeft_apply_mkQ (a : I → G) (b : I → H) (χ : I → k)
    {ρ : Representation k G V} (σ : Representation k H W) (S : Subrepresentation ρ)
    (B : LinearMap.ker (restrictLeft a b χ σ S)) (v : V) (w : W) :
    (descendLeft a b χ σ S B).val (S.toSubmodule.mkQ v) w = B.val.val v w :=
  rfl

theorem descendLeft_injective (a : I → G) (b : I → H) (χ : I → k)
    {ρ : Representation k G V} (σ : Representation k H W) (S : Subrepresentation ρ) :
    Function.Injective (descendLeft a b χ σ S) := by
  intro B C h
  apply Subtype.ext
  apply Subtype.ext
  ext v w
  exact congrArg (fun D => D.val (S.toSubmodule.mkQ v) w) h

/-- A form whose restriction to `S` vanishes in the second argument descends to the
actual quotient representation, with the same tests. -/
def descendRight (a : I → G) (b : I → H) (χ : I → k) (ρ : Representation k G V)
    {σ : Representation k H W} (S : Subrepresentation σ) :
    LinearMap.ker (restrictRight a b χ ρ S) →ₗ[k]
      forms a b χ ρ
        (σ.quotient S.toSubmodule (fun h _ hw => S.apply_mem_toSubmodule h hw)) := by
  have hker (B : LinearMap.ker (restrictRight a b χ ρ S)) :
      S.toSubmodule ≤ LinearMap.ker B.val.val.flip := by
    intro w hw
    apply LinearMap.ext
    intro v
    exact congrArg (fun C : forms a b χ ρ S.toRepresentation => C.val v ⟨w, hw⟩) B.property
  refine
    { toFun := fun B => ⟨(S.toSubmodule.liftQ B.val.val.flip (hker B)).flip, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro i v q
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    exact B.val.property i v w
  · intro B C
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro q
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl
  · intro c B
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro q
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl

@[simp]
theorem descendRight_apply_mkQ (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) {σ : Representation k H W} (S : Subrepresentation σ)
    (B : LinearMap.ker (restrictRight a b χ ρ S)) (v : V) (w : W) :
    (descendRight a b χ ρ S B).val v (S.toSubmodule.mkQ w) = B.val.val v w :=
  rfl

theorem descendRight_injective (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) {σ : Representation k H W} (S : Subrepresentation σ) :
    Function.Injective (descendRight a b χ ρ S) := by
  intro B C h
  apply Subtype.ext
  apply Subtype.ext
  ext v w
  exact congrArg (fun D => D.val v (S.toSubmodule.mkQ w)) h

/-- An actual subrepresentation in the first argument and its actual quotient bound the
mixed form-space length. -/
theorem length_le_restrict_add_quotient_left (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W) (S : Subrepresentation ρ) :
    length a b χ ρ σ ≤ length a b χ S.toRepresentation σ +
      length a b χ (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv))
        σ := by
  let r := restrictLeft a b χ σ S
  have hex : Function.Exact (LinearMap.ker r).subtype r.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have heq := Module.length_eq_add_of_exact (R := k) (N := LinearMap.ker r)
    (M := forms a b χ ρ σ) (P := LinearMap.range r) (LinearMap.ker r).subtype r.rangeRestrict
    (Submodule.injective_subtype _) r.surjective_rangeRestrict hex
  change Module.length k (forms a b χ ρ σ) ≤ _
  rw [heq, add_comm]
  exact add_le_add
    (Module.length_le_of_injective (LinearMap.range r).subtype (Submodule.injective_subtype _))
    (Module.length_le_of_injective (descendLeft a b χ σ S) (descendLeft_injective a b χ σ S))

/-- An actual subrepresentation in the second argument and its actual quotient bound the
mixed form-space length. -/
theorem length_le_restrict_add_quotient_right (a : I → G) (b : I → H) (χ : I → k)
    (ρ : Representation k G V) (σ : Representation k H W) (S : Subrepresentation σ) :
    length a b χ ρ σ ≤ length a b χ ρ S.toRepresentation +
      length a b χ ρ (σ.quotient S.toSubmodule (fun h _ hw => S.apply_mem_toSubmodule h hw)) := by
  let r := restrictRight a b χ ρ S
  have hex : Function.Exact (LinearMap.ker r).subtype r.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have heq := Module.length_eq_add_of_exact (R := k) (N := LinearMap.ker r)
    (M := forms a b χ ρ σ) (P := LinearMap.range r) (LinearMap.ker r).subtype r.rangeRestrict
    (Submodule.injective_subtype _) r.surjective_rangeRestrict hex
  change Module.length k (forms a b χ ρ σ) ≤ _
  rw [heq, add_comm]
  exact add_le_add
    (Module.length_le_of_injective (LinearMap.range r).subtype (Submodule.injective_subtype _))
    (Module.length_le_of_injective (descendRight a b χ ρ S) (descendRight_injective a b χ ρ S))

end Langlands.MixedBilinear
