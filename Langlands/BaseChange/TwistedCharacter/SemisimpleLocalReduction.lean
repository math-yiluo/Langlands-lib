import Langlands.BaseChange.TwistedCharacter.ClozelRegularComparison
import Langlands.BaseChange.TwistedCharacter.LocalCharacterDensity
import Langlands.BaseChange.TwistedCharacter.TwistedOrbitClosure
import Langlands.Galois.Local.AbsoluteDefinitions

/-! # Reduction of cyclic twisted integrability to semisimple neighborhoods -/

noncomputable section

namespace Langlands.BaseChange

open Module Set Filter _root_.Topology
open scoped SemidirectProduct Topology

section Algebra

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {l : ℕ} [NeZero l] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1} {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) E
local notation "H" => CyclicGLSemidirect σ hσ n

private theorem cyclicGLAction_eq_entrywise (c : CyclicComponent l) :
    cyclicGLAction σ hσ n c = entrywiseAut (cyclicPowerHom σ hσ c) n := by
  change (entrywiseAutHom n σ) ^ c.toAdd.val = entrywiseAutHom n (σ ^ c.toAdd.val)
  rw [map_pow]

/-- The cyclic adjoint action as a representation by linear equivalences. -/
def cyclicGLAdjointHom : H →* (M ≃ₗ[F] M) where
  toFun x := twistedMatrixConj (cyclicPowerHom σ hσ x.right) x.left
  map_one' := by
    apply LinearEquiv.ext
    intro X
    rw [SemidirectProduct.one_left, SemidirectProduct.one_right, map_one, twistedMatrixConj_apply]
    ext i j
    simp
  map_mul' x y := by
    rw [twistedMatrixConj_mul, SemidirectProduct.mul_right, map_mul,
      SemidirectProduct.mul_left, cyclicGLAction_eq_entrywise]

/-- An adjoint semisimple point in the cyclic model. -/
def IsCyclicGLSemisimple (x : H) : Prop :=
  Module.End.IsSemisimple ((cyclicGLAdjointHom x).toLinearMap)

variable [Module.Finite F E]

private theorem cyclicGLAdjoint_charpoly_conj (a x : H) :
    (cyclicGLAdjoint (a * x * a⁻¹)).charpoly = (cyclicGLAdjoint x).charpoly := by
  change ((cyclicGLAdjointHom (a * x * a⁻¹)).toLinearMap).charpoly =
    ((cyclicGLAdjointHom x).toLinearMap).charpoly
  rw [map_mul, map_mul, map_inv]
  exact LinearEquiv.charpoly_conj _ _

omit [Module.Finite F E] in
private theorem cyclicGL_conj_right (a x : H) : (a * x * a⁻¹).right = x.right := by
  simp [mul_comm a.right, mul_assoc]

/-- Componentwise minimal adjoint multiplicity is preserved by conjugation. -/
theorem IsCyclicGLRegular.conjugate {x : H} (hx : IsCyclicGLRegular x) (a : H) :
    IsCyclicGLRegular (a * x * a⁻¹) := by
  intro y hy
  let z := a⁻¹ * y * (a⁻¹)⁻¹
  have hz : z.right = x.right := by
    rw [show z.right = y.right from cyclicGL_conj_right a⁻¹ y, hy, cyclicGL_conj_right]
  have h := hx z hz
  rw [cyclicGLAdjoint_charpoly_conj a⁻¹ y] at h
  rwa [cyclicGLAdjoint_charpoly_conj]

end Algebra

section Closure

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [CharZero F]
  {E : Type v} [CommRing E] [Algebra F E] [Module.Finite F E] [IsReduced E]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  {l : ℕ} [NeZero l] {σ : E ≃ₐ[F] E} {hσ : σ ^ l = 1} {n : ℕ}

local notation "G" => GeneralLinear n E
local notation "H" => CyclicGLSemidirect σ hσ n

/-- Every conjugacy-orbit closure in the cyclic model has an adjoint semisimple point. -/
theorem exists_isCyclicGLSemisimple_mem_conjugacyClosure (hl : 0 < l) (x : H) :
    ∃ y ∈ closure (range fun a : H => a * x * a⁻¹), IsCyclicGLSemisimple y := by
  let τ := cyclicPowerHom σ hσ x.right
  have hτ : τ ^ l = 1 := by
    change (σ ^ x.right.toAdd.val) ^ l = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, hσ, one_pow]
  obtain ⟨δ, hδ, hss⟩ := twistedSemisimpleOrbitClosure F E τ l n hl hτ x.left
  let e : G → H := fun g => ⟨g, x.right⟩
  have he : Continuous e := (SemidirectProduct.isOpenEmbedding_slice
    (cyclicGLAction σ hσ n) x.right).continuous
  refine ⟨e δ, ?_, hss⟩
  have hsub : e '' range (fun g : G => g * x.left * (entrywiseAut τ n g)⁻¹) ⊆
      range (fun a : H => a * x * a⁻¹) := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, SemidirectProduct.ext ?_ ?_⟩
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left,
        SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        inv_one, one_mul, map_one, MulAut.one_apply, cyclicGLAction_eq_entrywise, map_inv, e, τ]
    · simp [e]
  exact closure_mono hsub (image_closure_subset_closure_image he ⟨δ, hδ, rfl⟩)

end Closure

open Langlands.JacquetLanglands

/-- The local character theorem near adjoint semisimple points in cyclic extensions. -/
def CyclicGLSemisimpleLocalCharacterStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    haveI := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
    let H := CyclicGLSemidirect σ hE.pow_eq_one n
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ H W) (hπ : IsAdmissible π), π.IsIrreducible →
      ∀ s : H, IsCyclicGLSemisimple s →
        ∃ U : Set H, IsOpen U ∧ s ∈ U ∧ ∃ Θ : H → ℂ,
          IsCharacterDensityOn π hπ Θ U ∧
          ∀ x ∈ U, IsCyclicGLRegular x → ∀ᶠ y in 𝓝 x, Θ y = Θ x

/-- Globalize the semisimple-neighborhood character theorem in the cyclic models. -/
theorem cyclicGLCharacterRegularity_of_semisimpleLocal.{u, v, uW}
    (h : CyclicGLSemisimpleLocalCharacterStatement.{u, v, uW}) :
    CyclicGLCharacterRegularityStatement.{u, v, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : NeZero l := ⟨hE.pos.ne'⟩
  have : Module.Finite F E := hE.1
  have : IsReduced E := hE.2.2.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  have := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  have := LocalFieldTopology.secondCountableTopology F
  have := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  have := (SemidirectProduct.homeomorphProd (cyclicGLAction σ hE.pow_eq_one n)).secondCountableTopology
  intro W _ _ π hπ hirr
  let H := CyclicGLSemidirect σ hE.pow_eq_one n
  have hclosure (x : H) : ∃ y ∈ closure (range fun a : H => a * x * a⁻¹), IsCyclicGLSemisimple y := by
    let := LocalGalois.localNormedField F
    have := LocalGalois.localNormedField_complete F
    exact exists_isCyclicGLSemisimple_mem_conjugacyClosure hE.pos x
  obtain ⟨Θ, hΘ, hreg⟩ := exists_characterFunction_of_conjugacyClosure
    {s : H | IsCyclicGLSemisimple s} {x : H | IsCyclicGLRegular x}
    (fun a x hx => IsCyclicGLRegular.conjugate hx a) hclosure (by
      intro s hs
      obtain ⟨U, hU, hsU, θ, hθ, hreg⟩ := h F E σ l n hE π hπ hirr s hs
      exact ⟨U, hU, hsU, θ, hθ, fun x hx => hreg x hx.1 hx.2⟩)
  exact ⟨Θ, hΘ, hreg⟩

/-- Local ordinary character densities near the semisimple points of the cyclic extensions
imply the twisted character integrability theorem on cyclic algebras. -/
def TwistedCharacterFromSemisimpleLocalStatement.{u, v, uW} : Prop :=
  CyclicGLSemisimpleLocalCharacterStatement.{u, v, uW} →
    TwistedCharacterLocalIntegrabilityStatement.{u, v, uW}

theorem twistedCharacterFromSemisimpleLocal.{u, v, uW} :
    TwistedCharacterFromSemisimpleLocalStatement.{u, v, uW} :=
  fun h => twistedCharacterFromCyclicGL (cyclicGLCharacterRegularity_of_semisimpleLocal h)

end Langlands.BaseChange
