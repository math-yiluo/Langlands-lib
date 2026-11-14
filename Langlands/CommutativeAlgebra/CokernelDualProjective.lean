import Langlands.CommutativeAlgebra.CokernelDualHom

/-! # Projectivity of `Q` from exactness on fibres

Let `K₀ → K₁ → K₂` be maps of finite projective modules over a noetherian ring `A` with zero
composite. If for every maximal ideal `P` the complex is exact at `K₁` after base change to some
field with kernel `P`, then `K₁ ⧸ δ₀(K₀)` is projective (local criterion: the induced map to
`K₂` is split injective at every maximal ideal), and then `Q = K₀^∨ ⧸ δ₀^∨(K₁^∨)` is a direct
summand of `K₀^∨`, hence projective. -/

universe u

open TensorProduct

set_option linter.deprecated false

namespace Langlands.CommutativeAlgebra.CokernelDualHom

section Split

variable {A : Type u} [CommRing A] {K₀ K₁ : Type u} [AddCommGroup K₀] [Module A K₀]
  [Module.Finite A K₀] [Module.Projective A K₀] [AddCommGroup K₁] [Module A K₁]
  [Module.Finite A K₁] [Module.Projective A K₁] (δ : K₀ →ₗ[A] K₁)

omit [Module.Finite A K₁] in
/-- **`Q` is projective once the cokernel of `δ` is.** -/
theorem projective_Q_of_projective_coker [Module.Projective A (K₁ ⧸ LinearMap.range δ)] :
    Module.Projective A (Q δ) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LinearMap.range δ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hσy : ∀ c, (LinearMap.range δ).mkQ (σ c) = c := fun c => LinearMap.congr_fun hσ c
  let r : K₁ →ₗ[A] LinearMap.range δ :=
    LinearMap.codRestrict (LinearMap.range δ) (LinearMap.id - σ ∘ₗ (LinearMap.range δ).mkQ)
      (fun y => by
        have h0 : (LinearMap.range δ).mkQ
            ((LinearMap.id - σ ∘ₗ (LinearMap.range δ).mkQ : K₁ →ₗ[A] K₁) y) = 0 := by
          simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hσy,
            sub_self]
        exact (Submodule.Quotient.mk_eq_zero _).1 h0)
  have hr : ∀ z : LinearMap.range δ, r z = z := by
    intro z
    apply Subtype.ext
    have hz : (LinearMap.range δ).mkQ (z : K₁) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 z.2
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hz, map_zero, sub_zero]
  have : Module.Projective A (LinearMap.range δ) :=
    Module.Projective.of_split (LinearMap.range δ).subtype r (LinearMap.ext hr)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property δ.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict δ)
  have hsy : ∀ z, δ.rangeRestrict (s z) = z := fun z => LinearMap.congr_fun hs z
  have hδs : ∀ x, δ (s (δ.rangeRestrict x)) = δ x := by
    intro x
    have := congrArg Subtype.val (hsy (δ.rangeRestrict x))
    simpa using this
  let prj : Module.Dual A K₀ →ₗ[A] Module.Dual A K₀ := (s ∘ₗ δ.rangeRestrict).dualMap
  have hprj_range : ∀ φ, prj φ ∈ LinearMap.range δ.dualMap := by
    intro φ
    refine ⟨φ ∘ₗ s ∘ₗ r, ?_⟩
    ext x
    have hrx : r (δ x) = δ.rangeRestrict x := hr (δ.rangeRestrict x)
    simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, prj]
    rw [hrx]
  have hprj_fix : ∀ ψ : Module.Dual A K₁, prj (δ.dualMap ψ) = δ.dualMap ψ := by
    intro ψ
    ext x
    simp only [LinearMap.dualMap_apply, LinearMap.comp_apply, prj]
    rw [hδs]
  let σQ : Q δ →ₗ[A] Module.Dual A K₀ :=
    (LinearMap.range δ.dualMap).liftQ (LinearMap.id - prj) (by
      rintro _ ⟨ψ, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hprj_fix, sub_self])
  refine Module.Projective.of_split σQ (LinearMap.range δ.dualMap).mkQ ?_
  apply Submodule.linearMap_qext
  ext φ
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, σQ, Submodule.liftQ_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.id_comp]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 (hprj_range φ), sub_zero]

end Split

section Local

variable {B : Type u} [CommRing B] [IsLocalRing B] {C N : Type u} [AddCommGroup C] [Module B C]
  [Module.Finite B C] [AddCommGroup N] [Module B N] [Module.Finite B N] [Module.Free B N]

/-- **Local criterion.** Over a local ring, a module `C` with a map `u` to a finite free module
which stays injective after base change to some field with kernel the maximal ideal is
projective. -/
theorem projective_of_lTensor_field_injective (u : C →ₗ[B] N) (k : Type u) [Field k]
    [Algebra B k] (hk : RingHom.ker (algebraMap B k) = IsLocalRing.maximalIdeal B)
    (hinj : Function.Injective (u.lTensor k)) : Module.Projective B C := by
  let kB := IsLocalRing.ResidueField B
  let ι : kB →ₐ[B] k := Ideal.Quotient.liftₐ (IsLocalRing.maximalIdeal B) (Algebra.ofId B k)
    (fun a ha => by
      rw [← hk] at ha
      exact ha)
  let _ : Algebra kB k := ι.toAlgebra
  have : IsScalarTower B kB k := IsScalarTower.of_algebraMap_eq (fun b => (ι.commutes b).symm)
  let cbC := TensorProduct.AlgebraTensorModule.cancelBaseChange B kB k k C
  let cbN := TensorProduct.AlgebraTensorModule.cancelBaseChange B kB k k N
  have hnat : ∀ x, cbN ((u.baseChange kB).lTensor k x) = u.lTensor k (cbC x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp [cbC, cbN, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz =>
        rw [tmul_add, map_add, map_add, hy, hz, map_add, map_add]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hinjk : Function.Injective ((u.baseChange kB).lTensor k) := by
    intro x y hxy
    have h := congrArg cbN hxy
    rw [hnat, hnat] at h
    exact cbC.injective (hinj h)
  have hinjB : Function.Injective (u.lTensor kB) := by
    have h := (Module.FaithfullyFlat.lTensor_injective_iff_injective kB k
      (u.baseChange kB)).1 hinjk
    exact h
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective u).2 hinjB
  exact Module.Projective.of_split u l' hl'

end Local

section Global

variable {A : Type u} [CommRing A] {K₀ K₁ K₂ : Type u} [AddCommGroup K₀] [Module A K₀]
  [Module.Finite A K₀] [Module.Projective A K₀] [AddCommGroup K₁] [Module A K₁]
  [Module.Finite A K₁] [Module.Projective A K₁] [AddCommGroup K₂] [Module A K₂]
  [Module.Finite A K₂] [Module.Projective A K₂] (δ₀ : K₀ →ₗ[A] K₁) (δ₁ : K₁ →ₗ[A] K₂)

omit [Module.Finite A K₀] [Module.Projective A K₀] [Module.Finite A K₁] [Module.Projective A K₁]
  [Module.Finite A K₂] [Module.Projective A K₂] in
/-- Exactness at `K₁` after base change to a field `k` makes the induced map
`k ⊗ (K₁ ⧸ δ₀ K₀) → k ⊗ K₂` injective. -/
lemma lTensor_liftQ_injective (hδ : δ₁ ∘ₗ δ₀ = 0) (k : Type u) [Field k] [Algebra A k]
    (hex : ∀ x : k ⊗[A] K₁, δ₁.lTensor k x = 0 → x ∈ LinearMap.range (δ₀.lTensor k)) :
    Function.Injective (((LinearMap.range δ₀).liftQ δ₁
      (by rw [LinearMap.range_le_ker_iff]; exact hδ)).lTensor k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective k
    (Submodule.mkQ_surjective (LinearMap.range δ₀)) y
  have hx : δ₁.lTensor k x = 0 := by
    rw [← hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ]
  obtain ⟨z, rfl⟩ := hex x hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.range_mkQ_comp,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

omit [Module.Finite A K₀] [Module.Projective A K₀] [Module.Projective A K₁] in
/-- **The cokernel of `δ₀` is projective** when the complex is exact at `K₁` over a field at every
maximal ideal. -/
theorem projective_coker_of_exact [IsNoetherianRing A] (hδ : δ₁ ∘ₗ δ₀ = 0)
    (hex : ∀ (P : Ideal A) [P.IsMaximal], ∃ (k : Type u) (_ : Field k) (_ : Algebra A k),
      RingHom.ker (algebraMap A k) = P ∧
        ∀ x : k ⊗[A] K₁, δ₁.lTensor k x = 0 → x ∈ LinearMap.range (δ₀.lTensor k)) :
    Module.Projective A (K₁ ⧸ LinearMap.range δ₀) := by
  have : Module.FinitePresentation A (K₁ ⧸ LinearMap.range δ₀) :=
    Module.finitePresentation_of_finite A _
  let ū := (LinearMap.range δ₀).liftQ δ₁ (by rw [LinearMap.range_le_ker_iff]; exact hδ)
  refine Module.projective_of_localization_maximal' (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P ⊗[A] (K₁ ⧸ LinearMap.range δ₀))
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) _ 1) (fun P hP => ?_)
  obtain ⟨k, _, _, hker, hexk⟩ := hex P
  let B := Localization.AtPrime P
  have hunit : ∀ s : P.primeCompl, IsUnit (algebraMap A k s) := fun s => by
    rw [isUnit_iff_ne_zero]
    intro h
    apply s.2
    have h' : (s : A) ∈ RingHom.ker (algebraMap A k) := h
    rw [hker] at h'
    exact h'
  let φ : B →+* k := IsLocalization.lift (M := P.primeCompl) hunit
  let _ : Algebra B k := φ.toAlgebra
  have : IsScalarTower A B k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunit a).symm)
  have hkerB : RingHom.ker (algebraMap B k) = IsLocalRing.maximalIdeal B := by
    refine ((IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (RingHom.ker_ne_top _) ?_).symm
    intro b hb
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl b
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff B P] at hb
    rw [RingHom.mem_ker]
    change φ (IsLocalization.mk' B a s) = 0
    rw [IsLocalization.lift_mk']
    have ha : algebraMap A k a = 0 := by rw [← RingHom.mem_ker, hker]; exact hb
    rw [ha, zero_mul]
  have : Module.Free B (B ⊗[A] K₂) := Module.free_of_flat_of_isLocalRing
  refine projective_of_lTensor_field_injective (ū.baseChange B) k hkerB ?_
  let cbC := TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k (K₁ ⧸ LinearMap.range δ₀)
  let cbN := TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k K₂
  have hnat : ∀ x, cbN ((ū.baseChange B).lTensor k x) = ū.lTensor k (cbC x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp [cbC, cbN, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      | add y z hy hz =>
        rw [tmul_add, map_add, map_add, hy, hz, map_add, map_add]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  intro x y hxy
  have h := congrArg cbN hxy
  rw [hnat, hnat] at h
  exact cbC.injective (lTensor_liftQ_injective δ₀ δ₁ hδ k hexk h)

/-- **`Q` is projective** when the complex `K₀ → K₁ → K₂` is exact at `K₁` over a field at
every maximal ideal. -/
theorem projective_Q_of_exact [IsNoetherianRing A] (hδ : δ₁ ∘ₗ δ₀ = 0)
    (hex : ∀ (P : Ideal A) [P.IsMaximal], ∃ (k : Type u) (_ : Field k) (_ : Algebra A k),
      RingHom.ker (algebraMap A k) = P ∧
        ∀ x : k ⊗[A] K₁, δ₁.lTensor k x = 0 → x ∈ LinearMap.range (δ₀.lTensor k)) :
    Module.Projective A (Q δ₀) := by
  have := projective_coker_of_exact δ₀ δ₁ hδ hex
  exact projective_Q_of_projective_coker δ₀

end Global

end Langlands.CommutativeAlgebra.CokernelDualHom
