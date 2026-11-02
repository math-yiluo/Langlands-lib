import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleUniversal
import Langlands.AlgebraicGeometry.GroupoidCoactionExact

/-! # Extensions associated to groupoid cocycles -/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type u} [AddCommGroup M] [Module B M]

/-- The canonical coaction on the base ring. -/
def regular (t : B →+* C) : GroupoidCoaction t B where
  coaction :=
    { toFun := fun b => t b ⊗ₜ[B] (1 : B)
      map_zero' := by simp
      map_add' := fun b b' => by simp [add_tmul] }
  map_smul b b' := by simp [smul_tmul', smul_eq_mul]
  counit T _ _ φ h b := by
    change φ (t b) ⊗ₜ[B] (1 : B) = (1 : T) ⊗ₜ[B] b
    rw [show φ (t b) = algebraMap B T b from DFunLike.congr_fun h b]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
    simp
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ b := by
    change φ₃ (t b) ⊗ₜ[B] (1 : B) =
      φ₁ (t b) • LinearMap.rTensor B φ₂.toLinearMap (t 1 ⊗ₜ[B] (1 : B))
    rw [show φ₃ (t b) = φ₁ (t b) from DFunLike.congr_fun h₃ b]
    simp [smul_tmul', smul_eq_mul]

@[simp] theorem regular_coaction (b : B) :
    (regular t).coaction b = t b ⊗ₜ[B] (1 : B) := rfl

variable (θ : GroupoidCoaction t M) (x : C ⊗[B] M)

/-- The coaction formula on the split underlying module of a cocycle extension. -/
def cocycleExtensionMap : M × B →+ C ⊗[B] (M × B) where
  toFun z := LinearMap.lTensor C (LinearMap.inl B M B) (θ.coaction z.1) +
    t z.2 • (LinearMap.lTensor C (LinearMap.inl B M B) x +
      (1 : C) ⊗ₜ[B] (0, 1))
  map_zero' := by simp
  map_add' z z' := by simp [add_smul]; abel

@[simp]
theorem cocycleExtensionMap_apply (m : M) (b : B) :
    cocycleExtensionMap θ x (m, b) =
      LinearMap.lTensor C (LinearMap.inl B M B) (θ.coaction m) +
        t b • (LinearMap.lTensor C (LinearMap.inl B M B) x +
          (1 : C) ⊗ₜ[B] (0, 1)) := rfl

theorem cocycleExtensionMap_smul (b : B) (z : M × B) :
    cocycleExtensionMap θ x (b • z) = t b • cocycleExtensionMap θ x z := by
  simp only [cocycleExtensionMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.smul_fst,
    Prod.smul_snd, θ.map_smul, lTensor_smul, smul_eq_mul, map_mul, smul_add, smul_smul]

@[simp]
theorem cocycleExtensionMap_inl (m : M) :
    cocycleExtensionMap θ x (LinearMap.inl B M B m) =
      LinearMap.lTensor C (LinearMap.inl B M B) (θ.coaction m) := by
  simp [cocycleExtensionMap, LinearMap.inl_apply]

@[simp]
theorem cocycleExtensionMap_generator :
    cocycleExtensionMap θ x (0, 1) =
      LinearMap.lTensor C (LinearMap.inl B M B) x +
        (1 : C) ⊗ₜ[B] (0, 1) := by
  simp

private theorem compose_smul {N : Type u} [AddCommGroup N] [Module B N]
    (θN : N →+ C ⊗[B] N)
    (hθ : ∀ (b : B) (n : N), θN (b • n) = t b • θN n)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (c : C) (y : C ⊗[B] N) :
    coactionCompose t N θN hθ φ₁ φ₂ h (c • y) =
      φ₁ c • coactionCompose t N θN hθ φ₁ φ₂ h y := by
  induction y with
  | tmul c' n =>
    simp [coactionCompose, smul_tmul', smul_eq_mul, smul_smul]
  | add y z hy hz => simp [smul_add, hy, hz]

private theorem cocycleExtensionMap_unit (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x) (z : M × B) :
    LinearMap.rTensor (M × B) hE.identity.toLinearMap (cocycleExtensionMap θ x z) =
      (1 : B) ⊗ₜ[B] z := by
  rcases z with ⟨m, b⟩
  rw [cocycleExtensionMap_apply, map_add, rTensor_algHom_smul, tensor_naturality,
    θ.counit B hE.identity hE.identity_comp_t, map_add, tensor_naturality,
    hx.identity_eq_zero hE]
  simp only [map_zero, zero_add, LinearMap.lTensor_tmul, LinearMap.inl_apply,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  rw [show hE.identity (t b) = b from DFunLike.congr_fun hE.identity_comp_t b,
    ← tmul_smul, ← tmul_add]
  congr 1
  simp

private theorem cocycleExtensionMap_comp_generator (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ φ₃ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (h₃ : (φ₃ : C →+* T).comp t = φ₁.comp t) :
    LinearMap.rTensor (M × B) φ₃.toLinearMap
        (LinearMap.lTensor C (LinearMap.inl B M B) x + (1 : C) ⊗ₜ[B] (0, 1)) =
      coactionCompose t (M × B) (cocycleExtensionMap θ x) (cocycleExtensionMap_smul θ x)
        φ₁ φ₂ h (LinearMap.lTensor C (LinearMap.inl B M B) x +
          (1 : C) ⊗ₜ[B] (0, 1)) := by
  have hi := coactionCompose_map θ.coaction (cocycleExtensionMap θ x)
    θ.map_smul (cocycleExtensionMap_smul θ x) (LinearMap.inl B M B)
    (cocycleExtensionMap_inl θ x) φ₁ φ₂ h x
  have he :
      coactionCompose t (M × B) (cocycleExtensionMap θ x) (cocycleExtensionMap_smul θ x)
        φ₁ φ₂ h ((1 : C) ⊗ₜ[B] (0, 1)) =
      LinearMap.rTensor (M × B) φ₂.toLinearMap
        (LinearMap.lTensor C (LinearMap.inl B M B) x +
          (1 : C) ⊗ₜ[B] (0, 1)) := by
    change φ₁ 1 • LinearMap.rTensor (M × B) φ₂.toLinearMap
      (cocycleExtensionMap θ x (0, 1)) = _
    rw [map_one, one_smul, cocycleExtensionMap_generator]
  simp only [map_add, tensor_naturality, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, ← hi, he]
  rw [hx.specialize hE φ₁ φ₂ φ₃ h h₃, map_add]
  abel

private theorem cocycleExtensionMap_comp (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ φ₃ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (h₃ : (φ₃ : C →+* T).comp t = φ₁.comp t) (z : M × B) :
    LinearMap.rTensor (M × B) φ₃.toLinearMap (cocycleExtensionMap θ x z) =
      coactionCompose t (M × B) (cocycleExtensionMap θ x) (cocycleExtensionMap_smul θ x)
        φ₁ φ₂ h (cocycleExtensionMap θ x z) := by
  rcases z with ⟨m, b⟩
  rw [cocycleExtensionMap_apply, map_add, rTensor_algHom_smul, tensor_naturality,
    θ.coassoc T φ₁ φ₂ φ₃ h h₃]
  rw [coactionCompose_map θ.coaction (cocycleExtensionMap θ x)
    θ.map_smul (cocycleExtensionMap_smul θ x) (LinearMap.inl B M B)
    (cocycleExtensionMap_inl θ x) φ₁ φ₂ h,
    show φ₃ (t b) = φ₁ (t b) from DFunLike.congr_fun h₃ b,
    cocycleExtensionMap_comp_generator θ x hE hx φ₁ φ₂ φ₃ h h₃]
  simp only [map_add, compose_smul]

/-- The extension of the regular coaction by `θ` attached to a one-cocycle. -/
noncomputable def cocycleExtension (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x) : GroupoidCoaction t (M × B) :=
  ofUniversal hE (cocycleExtensionMap θ x) (cocycleExtensionMap_smul θ x)
    (cocycleExtensionMap_unit θ x hE hx)
    (cocycleExtensionMap_comp θ x hE hx _ _ _ _ hE.composableComposite_comp_t)

@[simp]
theorem cocycleExtension_coaction (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x) (z : M × B) :
    (cocycleExtension θ x hE hx).coaction z = cocycleExtensionMap θ x z := rfl

/-- Inclusion of the kernel is equivariant for the cocycle extension. -/
theorem cocycleExtension_inl_isHom (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x) :
    θ.IsHom (cocycleExtension θ x hE hx) (LinearMap.inl B M B) := by
  intro m
  exact cocycleExtensionMap_inl θ x m

/-- The projection of the cocycle extension to the regular coaction is equivariant. -/
theorem cocycleExtension_snd_isHom (hE : RingEtaleEquivalenceRelation t)
    (hx : θ.IsOneCocycle x) :
    (cocycleExtension θ x hE hx).IsHom (regular t) (LinearMap.snd B M B) := by
  have hz (y : C ⊗[B] M) :
      LinearMap.lTensor C (LinearMap.snd B M B)
        (LinearMap.lTensor C (LinearMap.inl B M B) y) = 0 := by
    induction y <;> simp_all
  intro z
  rcases z with ⟨m, b⟩
  simp only [regular_coaction, LinearMap.snd_apply, cocycleExtension_coaction,
    cocycleExtensionMap_apply, map_add, lTensor_smul, hz, zero_add,
    LinearMap.lTensor_tmul]
  simp [smul_tmul', smul_eq_mul]

/-- Invariant lifting for the cocycle extension makes each cocycle a coboundary. -/
theorem oneCohomologyVanishes_of_isAcyclic (hE : RingEtaleEquivalenceRelation t)
    (hθ : θ.IsAcyclic) : θ.OneCohomologyVanishes := by
  intro x hx
  have hi := cocycleExtension_inl_isHom θ x hE hx
  have hp := cocycleExtension_snd_isHom θ x hE hx
  have hinj : Function.Injective (LinearMap.inl B M B) := by
    intro a b hab
    exact congrArg Prod.fst hab
  have hsurj : Function.Surjective (LinearMap.snd B M B) := fun b => ⟨(0, b), rfl⟩
  have hex : LinearMap.range (LinearMap.inl B M B) =
      LinearMap.ker (LinearMap.snd B M B) := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      simp
    · intro hz
      refine ⟨z.1, ?_⟩
      have hz' : z.2 = 0 := hz
      ext <;> simp [hz']
  have hq : (1 : B) ∈ (regular t).invariants := by
    change (regular t).coaction 1 = (1 : C) ⊗ₜ[B] (1 : B)
    simp
  obtain ⟨g, hg, hg₂⟩ := hθ (M × B) B (cocycleExtension θ x hE hx) (regular t)
    (LinearMap.inl B M B) (LinearMap.snd B M B) hi hp hinj hsurj hex 1 hq
  have hfst (y : C ⊗[B] M) :
      LinearMap.lTensor C (LinearMap.fst B M B)
        (LinearMap.lTensor C (LinearMap.inl B M B) y) = y := by
    induction y <;> simp_all
  have he := congrArg (LinearMap.lTensor C (LinearMap.fst B M B)) hg
  change g.2 = 1 at hg₂
  change LinearMap.lTensor C (LinearMap.fst B M B) (cocycleExtensionMap θ x g) =
    LinearMap.lTensor C (LinearMap.fst B M B) ((1 : C) ⊗ₜ[B] g) at he
  rcases g with ⟨m, b⟩
  change b = 1 at hg₂
  subst b
  simp only [cocycleExtensionMap_apply, map_one, one_smul, map_add, hfst,
    LinearMap.lTensor_tmul, LinearMap.fst_apply, tmul_zero, add_zero] at he
  refine ⟨-m, ?_⟩
  simp only [coboundary_apply, map_neg]
  rw [← he]
  abel

/-- On an affine étale relation, the two internal acyclicity criteria agree. -/
theorem oneCohomologyVanishes_iff_isAcyclic (hE : RingEtaleEquivalenceRelation t) :
    θ.OneCohomologyVanishes ↔ θ.IsAcyclic := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact ⟨isAcyclic_of_oneCohomologyVanishes θ,
    oneCohomologyVanishes_of_isAcyclic θ hE⟩

end Langlands.AlgebraicGeometry.GroupoidCoaction
