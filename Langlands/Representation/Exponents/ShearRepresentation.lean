import Langlands.Representation.Exponents.TemperedBruhatRemarksStatements
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Geometry.Building.SplitTorusValuation
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # The shear representation `g ↦ [[1, φ(g)], [0, 1]]`

For a group `Γ` and an additive character `φ : Γ → ℂ` (written as a homomorphism to
`Multiplicative ℂ`), `shearRep φ` is the representation of `Γ` on `ℂ²` (lifted to an arbitrary
universe) by the unipotent matrices `[[1, φ(g)], [0, 1]]`. It is

* smooth when `φ` is trivial on an open subgroup;
* admissible, being finite-dimensional;
* not unitarizable as soon as `φ` is not identically zero: an invariant positive definite
  Hermitian form `⟨,⟩` gives `⟨g e₂, g e₁⟩ = ⟨φ(g) e₁ + e₂, e₁⟩ = ⟨e₂, e₁⟩`, so
  `conj(φ(g)) ⟨e₁, e₁⟩ = 0` and `e₁ = 0`.

For `G = 𝔾_m` over a nonarchimedean local field, `gmValuation` is the additive character
`x ↦ ord(x)` of `G(F) = Fˣ` (through the identity rational character), which is trivial on the
open norm kernel and takes the value `1` at a uniformizer. This gives an example for
Renard VII.2.6, Remark, which asserts that such a representation exists but gives none.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ComplexConjugate

namespace Langlands.ShearRepresentation

/-- The shear `(x, y) ↦ (x + a y, y)` of `ℂ²`, on the lift of `ℂ × ℂ` to universe `v`. -/
def shear (a : ℂ) : ULift.{v} (ℂ × ℂ) →ₗ[ℂ] ULift.{v} (ℂ × ℂ) where
  toFun x := ⟨(x.down.1 + a * x.down.2, x.down.2)⟩
  map_add' x y := by
    apply ULift.ext
    simp only [ULift.add_down, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    exact Prod.ext (by ring) (by ring)
  map_smul' r x := by
    apply ULift.ext
    simp only [ULift.smul_down, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk]
    exact Prod.ext (by ring) (by ring)

@[simp] theorem shear_apply_down (a : ℂ) (x : ULift.{v} (ℂ × ℂ)) :
    (shear.{v} a x).down = (x.down.1 + a * x.down.2, x.down.2) := rfl

theorem shear_zero : shear.{v} 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply ULift.ext
  simp

theorem shear_add (a b : ℂ) : shear.{v} (a + b) = shear.{v} a ∘ₗ shear.{v} b := by
  apply LinearMap.ext
  intro x
  apply ULift.ext
  simp only [shear_apply_down, LinearMap.coe_comp, Function.comp_apply]
  exact Prod.ext (by ring) (by ring)

variable {Γ : Type*} [Group Γ]

/-- The representation `g ↦ [[1, φ(g)], [0, 1]]` of `Γ` on `ℂ²`. -/
def shearRep (φ : Γ →* Multiplicative ℂ) : Representation ℂ Γ (ULift.{v} (ℂ × ℂ)) where
  toFun g := shear.{v} (φ g).toAdd
  map_one' := by
    rw [map_one, toAdd_one, shear_zero]
    rfl
  map_mul' g h := by
    rw [map_mul, toAdd_mul, shear_add]
    rfl

@[simp] theorem shearRep_apply (φ : Γ →* Multiplicative ℂ) (g : Γ) :
    shearRep.{v} φ g = shear.{v} (φ g).toAdd := rfl

/-- Every operator of the shear representation is unipotent: `(π(g) - 1)² = 0`. -/
theorem sq_shearRep_sub_one (φ : Γ →* Multiplicative ℂ) (g : Γ) :
    (shearRep.{v} φ g - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply ULift.ext
  simp only [sq, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    shearRep_apply, shear_apply_down, ULift.sub_down, LinearMap.zero_apply, ULift.zero_down]
  exact Prod.ext (by simp) (by simp)

/-- An invariant positive definite Hermitian form forces `φ = 0`. -/
theorem not_isUnitarizable_shearRep (φ : Γ →* Multiplicative ℂ) (g : Γ)
    (hg : (φ g).toAdd ≠ 0) : ¬ IsUnitarizable (shearRep.{v} φ) := by
  rintro ⟨b⟩
  let e₁ : ULift.{v} (ℂ × ℂ) := ⟨(1, 0)⟩
  let e₂ : ULift.{v} (ℂ × ℂ) := ⟨(0, 1)⟩
  have h₁ : shearRep.{v} φ g e₁ = e₁ := by
    apply ULift.ext
    simp [e₁]
  have h₂ : shearRep.{v} φ g e₂ = (φ g).toAdd • e₁ + e₂ := by
    apply ULift.ext
    simp [e₁, e₂]
  have hinv := b.invariant g e₂ e₁
  rw [h₁, h₂, b.add_left, b.smul_left] at hinv
  have hzero : conj (φ g).toAdd * b.inner e₁ e₁ = 0 := by
    linear_combination hinv
  have hne : conj (φ g).toAdd ≠ 0 := by
    rwa [map_ne_zero]
  have he : e₁ = 0 := b.definite e₁ ((mul_eq_zero.mp hzero).resolve_left hne)
  have := congrArg (fun x : ULift.{v} (ℂ × ℂ) => x.down.1) he
  simp [e₁] at this

section Topology

variable [TopologicalSpace Γ]

/-- The shear representation is smooth when `φ` is trivial on an open subgroup. -/
theorem isSmooth_shearRep (φ : Γ →* Multiplicative ℂ) (K : OpenSubgroup Γ)
    (hK : ∀ g ∈ K, φ g = 1) : IsSmooth (shearRep.{v} φ) := by
  intro x
  refine ⟨K, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro g
  change shearRep.{v} φ (g : Γ) x = x
  rw [shearRep_apply, hK g g.2, toAdd_one, shear_zero]
  rfl

/-- A finite-dimensional smooth representation is admissible. -/
theorem isAdmissible_shearRep (φ : Γ →* Multiplicative ℂ) (K : OpenSubgroup Γ)
    (hK : ∀ g ∈ K, φ g = 1) : IsAdmissible (shearRep.{v} φ) :=
  ⟨isSmooth_shearRep φ K hK, fun _ => inferInstance⟩

end Topology

end Langlands.ShearRepresentation

namespace Langlands.ShearRepresentation.Gm

open GroupScheme

variable (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The multiplicative group `𝔾_m` over `k`, as a group scheme. -/
abbrev group : GroupScheme (Spec (CommRingCat.of k)) := (Gm (Spec (CommRingCat.of k))).toGrp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- `𝔾_m` is a connected reductive group (a split torus). -/
theorem isConnectedReductive : IsConnectedReductive (group k) :=
  isSplitTorus_gm.isConnectedReductive

/-- The identity rational character of `𝔾_m`. -/
def identityCharacter : rationalCharacters (group k) := Additive.ofMul (𝟙 _)

/-- The additive character `x ↦ ord(x)` of `𝔾_m(k)`, read through the identity rational
character and the published integer valuation `Plancherel.rationalCharacterValuation`. -/
def gmValuation : rationalPoints (group k) →* Multiplicative ℂ where
  toFun g := Multiplicative.ofAdd
    (((Plancherel.rationalCharacterValuation (group k) g).toAdd (identityCharacter k) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, toAdd_mul, AddMonoidHom.add_apply, Int.cast_add, ofAdd_add]

/-- `gmValuation` is trivial on the published common norm kernel. -/
theorem gmValuation_eq_one_of_mem (g : rationalPoints (group k))
    (hg : g ∈ Plancherel.rationalCommonNormKernel (group k)) : gmValuation k g = 1 := by
  rw [Plancherel.mem_rationalCommonNormKernel_iff_valuation] at hg
  change Multiplicative.ofAdd _ = 1
  rw [hg (identityCharacter k), Int.cast_zero, ofAdd_zero]

/-- The point of `𝔾_m(k)` given by the uniformizer. -/
def uniformizerPoint : rationalPoints (group k) :=
  (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm
    (GroupScheme.SplitTorusValuation.uniformizerUnit k)

/-- The uniformizer has valuation one. -/
theorem gmValuation_uniformizerPoint :
    (gmValuation k (uniformizerPoint k)).toAdd = 1 := by
  change (((Plancherel.rationalCharacterValuation (group k) (uniformizerPoint k)).toAdd
    (identityCharacter k) : ℤ) : ℂ) = 1
  rw [Plancherel.rationalCharacterValuation_apply, rationalCharacterEval_apply]
  have h : uniformizerPoint k ≫ (identityCharacter k).toMul.hom.hom = uniformizerPoint k := by
    exact Category.comp_id _
  rw [h, uniformizerPoint, MulEquiv.apply_symm_apply,
    GroupScheme.SplitTorusValuation.fieldOrderUnits_uniformizerUnit]
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The group `𝔾_m(k)` is commutative. -/
theorem mul_comm_rationalPoints (g h : rationalPoints (group k)) : g * h = h * g := by
  apply (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).injective
  rw [map_mul, map_mul, mul_comm]

/-- The shear representation of `𝔾_m(k)` attached to the valuation is smooth for the canonical
evaluation topology: it is trivial on the open common norm kernel. -/
theorem isSmooth_shearRep_gmValuation :
    haveI := (isConnectedReductive k).isAffineHom
    letI : TopologicalSpace (rationalPoints (group k)) :=
      Aubert.General.RationalPointFamily.pointTopology
    IsSmooth (shearRep.{v} (gmValuation k)) := by
  have := (isConnectedReductive k).isAffineHom
  let : TopologicalSpace (rationalPoints (group k)) :=
    Aubert.General.RationalPointFamily.pointTopology
  have : IsAffine (group k).X.left := isAffine_of_isAffineHom (group k).X.hom
  have := (isConnectedReductive k).smooth
  exact isSmooth_shearRep (gmValuation k)
    (Plancherel.rationalCommonNormOpenSubgroup (group k))
    (gmValuation_eq_one_of_mem k)

/-- The shear representation of `𝔾_m(k)` is admissible for the canonical evaluation topology. -/
theorem isAdmissible_shearRep_gmValuation :
    haveI := (isConnectedReductive k).isAffineHom
    letI : TopologicalSpace (rationalPoints (group k)) :=
      Aubert.General.RationalPointFamily.pointTopology
    IsAdmissible (shearRep.{v} (gmValuation k)) := by
  have := (isConnectedReductive k).isAffineHom
  let : TopologicalSpace (rationalPoints (group k)) :=
    Aubert.General.RationalPointFamily.pointTopology
  have : IsAffine (group k).X.left := isAffine_of_isAffineHom (group k).X.hom
  have := (isConnectedReductive k).smooth
  exact isAdmissible_shearRep (gmValuation k)
    (Plancherel.rationalCommonNormOpenSubgroup (group k))
    (gmValuation_eq_one_of_mem k)

/-- The shear representation of `𝔾_m(k)` is not unitarizable. -/
theorem not_isUnitarizable_shearRep_gmValuation :
    ¬ IsUnitarizable (shearRep.{v} (gmValuation k)) :=
  not_isUnitarizable_shearRep (gmValuation k) (uniformizerPoint k)
    (by rw [gmValuation_uniformizerPoint k]; exact one_ne_zero)

end Langlands.ShearRepresentation.Gm
