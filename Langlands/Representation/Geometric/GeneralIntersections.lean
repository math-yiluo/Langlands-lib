import Langlands.Representation.Geometric.WeylDefinitions
import Mathlib.Topology.LocallyConstant.Basic

/-! Actual subgroup and character data for BZ77 section 5.1. -/

namespace Langlands.Geometric.General

open scoped Pointwise

universe uG uA

variable {G : Type uG} [Group G]

/-- The conjugate `w H w⁻¹`, expressed as an inverse image. -/
def conjugate (H : Subgroup G) (w : G) : Subgroup G :=
  H.comap (MulAut.conj w⁻¹).toMonoidHom

@[simp]
theorem mem_conjugate (H : Subgroup G) (w g : G) :
    g ∈ conjugate H w ↔ w⁻¹ * g * w ∈ H := by
  simp [conjugate]

/-- The inverse-image definition has exactly the expected conjugate elements. -/
theorem mem_conjugate_iff (H : Subgroup G) (w g : G) :
    g ∈ conjugate H w ↔ ∃ h : H, w * (h : G) * w⁻¹ = g := by
  constructor
  · intro hg
    refine ⟨⟨w⁻¹ * g * w, (mem_conjugate H w g).mp hg⟩, ?_⟩
    simp [mul_assoc]
  · rintro ⟨h, rfl⟩
    simp [mul_assoc]

/-- `M ∩ w⁻¹(K)` as an actual subgroup of `M`. Taking `K=Q,N,V`
gives the three source groups in BZ77 section 5.1. -/
def intersectionIn (M K : Subgroup G) (w : G) : Subgroup M :=
  K.comap ((MulAut.conj w).toMonoidHom.comp M.subtype)

@[simp]
theorem mem_intersectionIn (M K : Subgroup G) (w : G) (m : M) :
    m ∈ intersectionIn M K w ↔ w * (m : G) * w⁻¹ ∈ K := Iff.rfl

/-- Reassociate the subtype to the published ambient intersection.
This does not choose any group isomorphism. -/
def intersectionInAmbient (M K : Subgroup G) (w : G) :
    intersectionIn M K w ≃* intersectionSource M K w where
  toFun m := ⟨m.val.val, m.val.property, m.property⟩
  invFun g := ⟨⟨g.val, g.property.1⟩, g.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Conjugation from the intersection in `M` into `K`. -/
def intersectionToSecond (M K : Subgroup G) (w : G) :
    intersectionIn M K w →* K where
  toFun m := ⟨MulAut.conj w m.val.val, m.property⟩
  map_one' := Subtype.ext (map_one (MulAut.conj w))
  map_mul' m n := Subtype.ext ((MulAut.conj w).map_mul m.val.val n.val.val)

@[simp]
theorem intersectionToSecond_apply (M K : Subgroup G) (w : G)
    (m : intersectionIn M K w) :
    (intersectionToSecond M K w m : G) = w * m.val.val * w⁻¹ := rfl

/-- The BZ77 isomorphism `M' ≃ N'`, obtained from the published ambient
conjugation and the two canonical subtype re-associations. -/
def intersectionEquiv (M N : Subgroup G) (w : G) :
    intersectionIn M N w ≃* intersectionIn N M w⁻¹ :=
  (intersectionInAmbient M N w).trans
    ((intersectionConjugation M N w).trans (intersectionInAmbient N M w⁻¹).symm)

@[simp]
theorem intersectionEquiv_apply (M N : Subgroup G) (w : G)
    (m : intersectionIn M N w) :
    (intersectionEquiv M N w m).val.val = w * m.val.val * w⁻¹ := rfl

@[simp]
theorem intersectionEquiv_symm_apply (M N : Subgroup G) (w : G)
    (n : intersectionIn N M w⁻¹) :
    ((intersectionEquiv M N w).symm n).val.val = w⁻¹ * n.val.val * w := by
  change w⁻¹ * n.val.val * (w⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Literal decomposability from BZ77 5.1:
`H ∩ (M U) = (H ∩ M)(H ∩ U)`, where multiplication is set multiplication. -/
def IsDecomposable (H M U : Subgroup G) : Prop :=
  (H : Set G) ∩ ((M : Set G) * (U : Set G)) =
    ((H ⊓ M : Subgroup G) : Set G) * ((H ⊓ U : Subgroup G) : Set G)

/-- All six decomposability conditions in BZ77 5.1(4), in their source order. -/
def SixDecomposable (P M U Q N V : Subgroup G) (w : G) : Prop :=
  IsDecomposable (conjugate P w) N V ∧
  IsDecomposable (conjugate M w) N V ∧
  IsDecomposable (conjugate U w) N V ∧
  IsDecomposable (conjugate Q w⁻¹) M U ∧
  IsDecomposable (conjugate N w⁻¹) M U ∧
  IsDecomposable (conjugate V w⁻¹) M U

/-- An elementwise version of the literal set equality. -/
theorem isDecomposable_iff (H M U : Subgroup G) :
    IsDecomposable H M U ↔
      ∀ g : G, g ∈ H → g ∈ (M : Set G) * (U : Set G) →
        ∃ m ∈ H ⊓ M, ∃ u ∈ H ⊓ U, m * u = g := by
  constructor
  · intro h g hg hmu
    have hg' : g ∈ ((H ⊓ M : Subgroup G) : Set G) *
        ((H ⊓ U : Subgroup G) : Set G) := by
      rw [← h]
      exact ⟨hg, hmu⟩
    exact hg'
  · intro h
    apply Set.ext
    intro g
    constructor
    · rintro ⟨hg, hmu⟩
      exact h g hg hmu
    · rintro ⟨m, hm, u, hu, rfl⟩
      exact ⟨H.mul_mem hm.1 hu.1, ⟨m, hm.2, u, hu.2, rfl⟩⟩

section Characters

variable {A : Type uA} [Monoid A]

/-- Conjugate and restrict a character. For `M,V,w,psi` this is `psi'`;
for `N,U,w⁻¹,theta` this is `theta'`. -/
def intersectionCharacter (M K : Subgroup G) (w : G) (χ : K →* A) :
    intersectionIn M K w →* A :=
  χ.comp (intersectionToSecond M K w)

@[simp]
theorem intersectionCharacter_apply (M K : Subgroup G) (w : G) (χ : K →* A)
    (m : intersectionIn M K w) :
    intersectionCharacter M K w χ m = χ (intersectionToSecond M K w m) := rfl

/-- The characters `w(theta)` and `psi` agree on `w(U) ∩ V`.
Failure of this concrete predicate is the zero-orbit-piece branch of BZ77 5.1. -/
def CharactersCompatible (U V : Subgroup G) (w : G)
    (θ : U →* A) (ψ : V →* A) : Prop :=
  intersectionCharacter V U w⁻¹ θ = ψ.comp (intersectionIn V U w⁻¹).subtype

theorem charactersCompatible_iff (U V : Subgroup G) (w : G)
    (θ : U →* A) (ψ : V →* A) :
    CharactersCompatible U V w θ ψ ↔
      ∀ v : intersectionIn V U w⁻¹, θ (intersectionToSecond V U w⁻¹ v) = ψ v.val := by
  constructor
  · intro h v
    exact DFunLike.congr_fun h v
  · intro h
    exact MonoidHom.ext h

end Characters

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClosed_conjugate (H : Subgroup G) (w : G) (hH : IsClosed (H : Set G)) :
    IsClosed (conjugate H w : Set G) := by
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

/-- Closedness in the induced topology on `M` requires only closedness of `K`. -/
theorem isClosed_intersectionIn (M K : Subgroup G) (w : G)
    (hK : IsClosed (K : Set G)) : IsClosed (intersectionIn M K w : Set M) := by
  exact hK.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

omit [IsTopologicalGroup G] in
theorem continuous_intersectionInAmbient (M K : Subgroup G) (w : G) :
    Continuous (intersectionInAmbient M K w) := by
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

omit [IsTopologicalGroup G] in
theorem continuous_intersectionInAmbient_symm (M K : Subgroup G) (w : G) :
    Continuous (intersectionInAmbient M K w).symm := by
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem continuous_intersectionToSecond (M K : Subgroup G) (w : G) :
    Continuous (intersectionToSecond M K w) := by
  exact ((continuous_const.mul
    (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const).subtype_mk _

/-- The same actual conjugation is a topological group isomorphism. -/
def intersectionEquivContinuous (M N : Subgroup G) (w : G) :
    intersectionIn M N w ≃ₜ* intersectionIn N M w⁻¹ where
  toMulEquiv := intersectionEquiv M N w
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_intersectionToSecond M N w
  continuous_invFun := by
    have hc : Continuous (fun n : intersectionIn N M w⁻¹ =>
        ((intersectionEquiv M N w).symm n).val.val) := by
      simp only [intersectionEquiv_symm_apply]
      exact (continuous_const.mul
        (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const
    exact (hc.subtype_mk _).subtype_mk _

/-- Local constancy survives the actual conjugation and subgroup restriction. -/
theorem isLocallyConstant_intersectionCharacter
    {A : Type uA} [Monoid A] (M K : Subgroup G) (w : G)
    (χ : K →* A) (hχ : IsLocallyConstant χ) :
    IsLocallyConstant (intersectionCharacter M K w χ) :=
  hχ.comp_continuous (continuous_intersectionToSecond M K w)

end Topology

end Langlands.Geometric.General
