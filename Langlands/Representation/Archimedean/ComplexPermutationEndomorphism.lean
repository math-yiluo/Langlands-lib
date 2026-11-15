import Langlands.Representation.FiniteVectors
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Equivariant endomorphisms of representations with finite multiplicities

Let `ρ` be a representation of a group `G` on a complex vector space `W` in which every vector
is a finite vector (its orbit spans a finite-dimensional subspace), and let `ev` be a linear
functional that separates vectors along orbits: `ev (ρ g w) = 0` for all `g` forces `w = 0`.
For the `U(n)`-finite functions of a principal series, `ev` is evaluation at `1`.

For a finite-dimensional invariant subspace `F`, the equivariant linear maps `F → W` form a
finite-dimensional space (`finiteDimensional_eqvHom`): `φ ↦ ev ∘ φ` is injective. This gives:

* `surjective_of_injective`: an injective equivariant endomorphism of `W` is surjective;
* `injective_of_surjective`: a surjective equivariant endomorphism of `W` is injective,
  provided `W` carries a `G`-invariant positive definite sesquilinear form (which supplies
  invariant complements in finite-dimensional invariant subspaces).
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexPermutation

open Module

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G W)

/-- The `G`-equivariant linear maps from a subspace `F` of `W` into `W`. -/
def eqvHom (F : Submodule ℂ W) : Submodule ℂ (F →ₗ[ℂ] W) where
  carrier := {φ | ∀ (g : G) (x : F) (hx : ρ g x ∈ F), φ ⟨ρ g x, hx⟩ = ρ g (φ x)}
  zero_mem' := by
    intro g x hx
    simp
  add_mem' {φ ψ} hφ hψ := by
    intro g x hx
    simp only [LinearMap.add_apply, hφ g x hx, hψ g x hx, map_add]
  smul_mem' c φ hφ := by
    intro g x hx
    simp only [LinearMap.smul_apply, hφ g x hx, map_smul]

theorem mem_eqvHom {F : Submodule ℂ W} (φ : F →ₗ[ℂ] W) :
    φ ∈ eqvHom ρ F ↔ ∀ (g : G) (x : F) (hx : ρ g x ∈ F), φ ⟨ρ g x, hx⟩ = ρ g (φ x) :=
  Iff.rfl

/-- The inclusion of a subspace is equivariant. -/
theorem subtype_mem_eqvHom (F : Submodule ℂ W) : F.subtype ∈ eqvHom ρ F := by
  intro g x hx
  rfl

/-- Composition with an equivariant endomorphism preserves equivariance. -/
theorem comp_mem_eqvHom {F : Submodule ℂ W} (E : W →ₗ[ℂ] W)
    (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w)) {φ : F →ₗ[ℂ] W}
    (hφ : φ ∈ eqvHom ρ F) : E ∘ₗ φ ∈ eqvHom ρ F := by
  intro g x hx
  rw [LinearMap.comp_apply, hφ g x hx, hE, LinearMap.comp_apply]

/-- Composition with `E` as a linear endomorphism of the space of equivariant maps. -/
def compEqvHom (F : Submodule ℂ W) (E : W →ₗ[ℂ] W)
    (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w)) :
    eqvHom ρ F →ₗ[ℂ] eqvHom ρ F where
  toFun φ := ⟨E ∘ₗ (φ : F →ₗ[ℂ] W), comp_mem_eqvHom ρ E hE φ.2⟩
  map_add' φ ψ := by
    apply Subtype.ext
    simp [LinearMap.comp_add]
  map_smul' c φ := by
    apply Subtype.ext
    simp [LinearMap.comp_smul]

theorem compEqvHom_apply (F : Submodule ℂ W) (E : W →ₗ[ℂ] W)
    (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w)) (φ : eqvHom ρ F) (x : F) :
    ((compEqvHom ρ F E hE φ : eqvHom ρ F) : F →ₗ[ℂ] W) x = E ((φ : F →ₗ[ℂ] W) x) :=
  rfl

section Finite

variable {ρ} (ev : W →ₗ[ℂ] ℂ) (hsep : ∀ w : W, (∀ g : G, ev (ρ g w) = 0) → w = 0)
include hsep

/-- For a finite-dimensional invariant subspace `F`, the equivariant maps `F → W` form a
finite-dimensional space: `φ ↦ ev ∘ φ` is injective into the dual of `F`. -/
theorem finiteDimensional_eqvHom (F : Submodule ℂ W) [FiniteDimensional ℂ F]
    (hF : ∀ (g : G), ∀ x ∈ F, ρ g x ∈ F) : FiniteDimensional ℂ (eqvHom ρ F) := by
  let Θ : eqvHom ρ F →ₗ[ℂ] Module.Dual ℂ F :=
    { toFun := fun φ => ev ∘ₗ (φ : F →ₗ[ℂ] W)
      map_add' := fun φ ψ => by
        ext x
        simp
      map_smul' := fun c φ => by
        ext x
        simp }
  refine Module.Finite.of_injective Θ ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply hsep
  intro g
  have h := LinearMap.congr_fun hφ ⟨ρ g x, hF g x x.2⟩
  change ev ((φ : F →ₗ[ℂ] W) ⟨ρ g x, hF g x x.2⟩) = 0 at h
  rw [φ.2 g x (hF g x x.2)] at h
  simpa using h

variable (hfin : ∀ w : W, FiniteVectors.IsFiniteVector ρ w)
include hfin

omit hsep hfin in
/-- The orbit span of a vector is an invariant subspace. -/
theorem orbitSpan_invariant (w : W) :
    ∀ (g : G), ∀ x ∈ FiniteVectors.orbitSpan ρ w, ρ g x ∈ FiniteVectors.orbitSpan ρ w :=
  fun g _ hx => (FiniteVectors.orbitSubrepresentation ρ w).apply_mem_toSubmodule g hx

omit hsep in
theorem finiteDimensional_orbitSpan (w : W) :
    FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ w) :=
  hfin w

/-- **An injective equivariant endomorphism is surjective.** For `w ∈ W` let `F` be its orbit
span. Composition with `E` is an injective endomorphism of the finite-dimensional space of
equivariant maps `F → W`, hence surjective; the inclusion of `F` is `E ∘ ψ` for some `ψ`, and
`w = E (ψ w)`. -/
theorem surjective_of_injective (E : W →ₗ[ℂ] W)
    (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w)) (hinj : Function.Injective E) :
    Function.Surjective E := by
  intro w
  set F := FiniteVectors.orbitSpan ρ w with hFdef
  have hFfin : FiniteDimensional ℂ F := hfin w
  have hFinv := orbitSpan_invariant (ρ := ρ) w
  have hfd := finiteDimensional_eqvHom ev hsep F hFinv
  have hcinj : Function.Injective (compEqvHom ρ F E hE) := by
    intro φ ψ h
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply hinj
    exact LinearMap.congr_fun (congrArg Subtype.val h) x
  have hcsurj := LinearMap.surjective_of_injective hcinj
  obtain ⟨ψ, hψ⟩ := hcsurj ⟨F.subtype, subtype_mem_eqvHom ρ F⟩
  refine ⟨(ψ : F →ₗ[ℂ] W) ⟨w, FiniteVectors.self_mem_orbitSpan ρ w⟩, ?_⟩
  have h := LinearMap.congr_fun (congrArg Subtype.val hψ)
    ⟨w, FiniteVectors.self_mem_orbitSpan ρ w⟩
  exact h

end Finite

/-! ## Invariant complements -/

section Complement

variable {ρ} (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ)
  (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
  (hBpos : ∀ x : W, B x x = 0 → x = 0)

/-- The functionals `x ↦ B x (u i)` as one linear map. -/
def pairingMap {r : ℕ} (u : Fin r → W) : W →ₗ[ℂ] (Fin r → ℂ) where
  toFun x i := B x (u i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp

include hBinv hBpos in
/-- **Invariant complements.** In a finite-dimensional invariant subspace `F'`, every invariant
subspace `U ≤ F'` has an invariant complement `C ≤ F'`: the vectors of `F'` orthogonal to `U`. -/
theorem exists_invariant_complement (F' U : Submodule ℂ W) [FiniteDimensional ℂ F']
    (hUF : U ≤ F') (hU : ∀ (g : G), ∀ x ∈ U, ρ g x ∈ U)
    (hF : ∀ (g : G), ∀ x ∈ F', ρ g x ∈ F') :
    ∃ C : Submodule ℂ W, C ≤ F' ∧ (∀ (g : G), ∀ x ∈ C, ρ g x ∈ C) ∧ U ⊓ C = ⊥ ∧
      U ⊔ C = F' := by
  have hUfin : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUF
  set r := finrank ℂ U with hr
  let bU : Basis (Fin r) ℂ U := Module.finBasis ℂ U
  let u : Fin r → W := fun i => (bU i : W)
  let Λ := pairingMap B u
  set C : Submodule ℂ W := F' ⊓ LinearMap.ker Λ with hCdef
  -- orthogonality to all of `U`
  have horth : ∀ x ∈ C, ∀ y ∈ U, B x y = 0 := by
    intro x hx y hy
    have hx0 : ∀ i, B x (u i) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hx.2) i
    have hy' : (⟨y, hy⟩ : U) = ∑ i, bU.repr ⟨y, hy⟩ i • bU i := (bU.sum_repr _).symm
    have hyW : y = ∑ i, bU.repr ⟨y, hy⟩ i • u i := by
      calc y = ((⟨y, hy⟩ : U) : W) := rfl
        _ = ((∑ i, bU.repr ⟨y, hy⟩ i • bU i : U) : W) := by rw [← hy']
        _ = ∑ i, bU.repr ⟨y, hy⟩ i • u i := by
          simp only [Submodule.coe_sum, Submodule.coe_smul, u]
    rw [hyW, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smulₛₗ, hx0 i, smul_zero]
  refine ⟨C, inf_le_left, ?_, ?_, ?_⟩
  · intro g x hx
    refine ⟨hF g x hx.1, ?_⟩
    show ρ g x ∈ LinearMap.ker Λ
    rw [LinearMap.mem_ker]
    ext i
    change B (ρ g x) (u i) = 0
    have hui : ρ g⁻¹ (u i) ∈ U := hU g⁻¹ (u i) (bU i).2
    have h1 : ρ g (ρ g⁻¹ (u i)) = u i := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hBinv]
    exact horth x hx _ hui
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact hBpos x (horth x hx.2 x hx.1)
  · apply Submodule.eq_of_le_of_finrank_le (sup_le hUF inf_le_left)
    show finrank ℂ F' ≤ finrank ℂ ↥(U ⊔ C)
    -- dimension count
    let Λ' : F' →ₗ[ℂ] (Fin r → ℂ) := Λ ∘ₗ F'.subtype
    have hrn := LinearMap.finrank_range_add_finrank_ker Λ'
    have hrange : finrank ℂ (LinearMap.range Λ') ≤ r := by
      have := Submodule.finrank_le (LinearMap.range Λ')
      simpa using this
    have hCfin : FiniteDimensional ℂ C := Submodule.finiteDimensional_of_le inf_le_left
    have hkerC : finrank ℂ (LinearMap.ker Λ') ≤ finrank ℂ C := by
      let e : LinearMap.ker Λ' →ₗ[ℂ] C :=
        { toFun := fun x => ⟨((x : F') : W), (x : F').2, by
            have := LinearMap.mem_ker.mp x.2
            exact LinearMap.mem_ker.mpr this⟩
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }
      refine LinearMap.finrank_le_finrank_of_injective (f := e) ?_
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : C => (z : W)) h
    have hinf : U ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      exact hBpos x (horth x hx.2 x hx.1)
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq U C
    rw [hinf, finrank_bot, add_zero] at hsum
    omega

end Complement

/-! ## Surjective endomorphisms -/

section Surjective

variable {ρ} (ev : W →ₗ[ℂ] ℂ) (hsep : ∀ w : W, (∀ g : G, ev (ρ g w) = 0) → w = 0)
  (hfin : ∀ w : W, FiniteVectors.IsFiniteVector ρ w)
  (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ)
  (hBinv : ∀ (g : G) (x y : W), B (ρ g x) (ρ g y) = B x y)
  (hBpos : ∀ x : W, B x x = 0 → x = 0)

include hfin in
/-- A finite family of vectors lies in a finite-dimensional invariant subspace. -/
theorem exists_finite_invariant {ι : Type*} [Fintype ι] (y : ι → W) :
    ∃ F' : Submodule ℂ W, FiniteDimensional ℂ F' ∧ (∀ (g : G), ∀ x ∈ F', ρ g x ∈ F') ∧
      ∀ i, y i ∈ F' := by
  refine ⟨⨆ i, FiniteVectors.orbitSpan ρ (y i), ?_, ?_, ?_⟩
  · have : ∀ i, FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ (y i)) := fun i => hfin (y i)
    infer_instance
  · intro g x hx
    refine Submodule.iSup_induction (fun i => FiniteVectors.orbitSpan ρ (y i))
      (motive := fun x => ρ g x ∈ ⨆ i, FiniteVectors.orbitSpan ρ (y i)) hx ?_ ?_ ?_
    · intro i x hx
      exact Submodule.mem_iSup_of_mem i
        ((FiniteVectors.orbitSubrepresentation ρ (y i)).apply_mem_toSubmodule g hx)
    · simp
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · intro i
    exact Submodule.mem_iSup_of_mem i (FiniteVectors.self_mem_orbitSpan ρ (y i))

include hfin hBinv hBpos in
/-- **Lifting through a surjective equivariant endomorphism.** Every equivariant map from a
finite-dimensional subspace `F` into `W` is `E ∘ ψ` for an equivariant `ψ`: lift a basis of `F`
to preimages, take the invariant span `F'` of their orbits, an invariant complement `C` of
`ker E ∩ F'` in `F'`, and invert `E` on `C`. -/
theorem exists_lift (E : W →ₗ[ℂ] W) (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w))
    (hsurj : Function.Surjective E) (F : Submodule ℂ W) [FiniteDimensional ℂ F]
    (φ : eqvHom ρ F) : ∃ ψ : eqvHom ρ F, compEqvHom ρ F E hE ψ = φ := by
  classical
  let bF := Module.finBasis ℂ F
  let y : Fin (finrank ℂ F) → W := fun j => (hsurj ((φ : F →ₗ[ℂ] W) (bF j))).choose
  have hy : ∀ j, E (y j) = (φ : F →ₗ[ℂ] W) (bF j) :=
    fun j => (hsurj ((φ : F →ₗ[ℂ] W) (bF j))).choose_spec
  obtain ⟨F', hF'fin, hF'inv, hyF'⟩ := exists_finite_invariant hfin y
  set U : Submodule ℂ W := LinearMap.ker E ⊓ F' with hUdef
  have hUinv : ∀ (g : G), ∀ x ∈ U, ρ g x ∈ U := by
    intro g x hx
    refine ⟨?_, hF'inv g x hx.2⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hE, LinearMap.mem_ker.mp hx.1, map_zero]
  obtain ⟨C, hCF', hCinv, hUC, hUCF'⟩ :=
    exists_invariant_complement B hBinv hBpos F' U inf_le_right hUinv hF'inv
  -- `E` is injective on `C`
  let EC : C →ₗ[ℂ] W := E ∘ₗ C.subtype
  have hECinj : Function.Injective EC := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have hxU : (x : W) ∈ U ⊓ C := ⟨⟨hx, hCF' x.2⟩, x.2⟩
    rw [hUC, Submodule.mem_bot] at hxU
    exact Subtype.ext hxU
  -- the image of `φ` lies in `E(C)`
  have hφC : ∀ x : F, (φ : F →ₗ[ℂ] W) x ∈ LinearMap.range EC := by
    intro x
    have hx : x = ∑ j, bF.repr x j • bF j := (bF.sum_repr x).symm
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hyj : y j ∈ U ⊔ C := by rw [hUCF']; exact hyF' j
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hyj
    refine ⟨⟨c, hc⟩, ?_⟩
    change E c = _
    rw [← hy j, ← hac, map_add, LinearMap.mem_ker.mp ha.1, zero_add]
  let e := LinearEquiv.ofInjective EC hECinj
  let φ' : F →ₗ[ℂ] LinearMap.range EC :=
    LinearMap.codRestrict (LinearMap.range EC) (φ : F →ₗ[ℂ] W) hφC
  let ψ₀ : F →ₗ[ℂ] W := C.subtype ∘ₗ (e.symm : LinearMap.range EC →ₗ[ℂ] C) ∘ₗ φ'
  have hψ₀C : ∀ x, ψ₀ x ∈ C := fun x => (e.symm (φ' x)).2
  have hEψ₀ : ∀ x, E (ψ₀ x) = (φ : F →ₗ[ℂ] W) x := by
    intro x
    have h := e.apply_symm_apply (φ' x)
    have h' := congrArg Subtype.val h
    exact h'
  have hψ₀ : ψ₀ ∈ eqvHom ρ F := by
    intro g x hx
    have h1 : E (ψ₀ ⟨ρ g x, hx⟩) = E (ρ g (ψ₀ x)) := by
      rw [hEψ₀, φ.2 g x hx, hE, hEψ₀]
    have h2 := hECinj (a₁ := ⟨_, hψ₀C ⟨ρ g x, hx⟩⟩) (a₂ := ⟨_, hCinv g _ (hψ₀C x)⟩) h1
    exact congrArg Subtype.val h2
  refine ⟨⟨ψ₀, hψ₀⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact hEψ₀ x

include hsep hfin hBinv hBpos in
/-- **A surjective equivariant endomorphism is injective** when `W` carries a `G`-invariant
positive definite sesquilinear form. Composition with `E` is surjective on the
finite-dimensional space of equivariant maps from the orbit span `F` of a vector `v ∈ ker E`,
hence injective; the inclusion of `F ⊆ ker E` is killed by it, so it vanishes and `v = 0`. -/
theorem injective_of_surjective (E : W →ₗ[ℂ] W)
    (hE : ∀ (g : G) (w : W), E (ρ g w) = ρ g (E w)) (hsurj : Function.Surjective E) :
    Function.Injective E := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [Submodule.mem_bot]
  set F := FiniteVectors.orbitSpan ρ v with hFdef
  have hFfin : FiniteDimensional ℂ F := hfin v
  have hFinv := orbitSpan_invariant (ρ := ρ) v
  have hfd := finiteDimensional_eqvHom ev hsep F hFinv
  have hcsurj : Function.Surjective (compEqvHom ρ F E hE) :=
    fun φ => exists_lift hfin B hBinv hBpos E hE hsurj F φ
  have hcinj := LinearMap.injective_iff_surjective.mpr hcsurj
  -- `F ⊆ ker E`
  have hFker : ∀ x ∈ F, E x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [hE, hv, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have h0 : compEqvHom ρ F E hE ⟨F.subtype, subtype_mem_eqvHom ρ F⟩ =
      compEqvHom ρ F E hE 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change E (x : W) = E 0
    rw [hFker x x.2, map_zero]
  have h1 := hcinj h0
  have h2 := LinearMap.congr_fun (congrArg Subtype.val h1)
    ⟨v, FiniteVectors.self_mem_orbitSpan ρ v⟩
  simpa using h2

end Surjective

end Langlands.Archimedean.ComplexPermutation
