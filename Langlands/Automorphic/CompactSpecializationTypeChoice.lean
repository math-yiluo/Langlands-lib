import Langlands.Automorphic.JointCompactProjection
import Langlands.Representation.CuspidalSupport.NormalRestrictionCovariance
import Langlands.Representation.Filtration.LengthTwoMatching

/-! # Choosing a nonzero compact type in a specialization quotient -/

noncomputable section

open scoped MonoidAlgebra

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.KFiniteDual

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type*} [Group K]

section Choice

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
  (ρ : Representation ℂ G W) (κ : Representation ℂ K W)
  [IsSemisimpleModule ℂ[K] κ.asModule]

/-- A nonzero smooth, compact-finite quotient has a vector of one irreducible
compact type fixed by a compact open subgroup of the supplied level. -/
theorem exists_nonzero_jointCompactType
    (hρ : Langlands.IsSmooth ρ) (hκ : ∀ v, FiniteVectors.IsFiniteVector κ v)
    (L₀ : OpenSubgroup G) (hL₀ : IsCompact (L₀ : Set G)) :
    ∃ (L : OpenSubgroup G), L ≤ L₀ ∧ IsCompact (L : Set G) ∧
      ∃ (d : ℕ) (τ : Representation ℂ K (Fin d → ℂ)), τ.IsIrreducible ∧
        ∃ y : W, y ≠ 0 ∧ y ∈ fixedVectors ρ L.toSubgroup ∧
          y ∈ CompactSplitting.isotypicPart τ κ := by
  let : Nontrivial κ.asModule := inferInstanceAs (Nontrivial W)
  obtain ⟨A, _, hA⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le
    (⊤ : Submodule ℂ[K] κ.asModule)).resolve_left top_ne_bot
  let := hA
  let : Nontrivial A := IsSimpleModule.nontrivial ℂ[K] A
  obtain ⟨s, hs⟩ := exists_ne (0 : A)
  let S : Subrepresentation κ := Subrepresentation.ofSubmodule' A
  let y : W := s.val
  have hy : y ≠ 0 := fun hy => hs (Subtype.ext hy)
  have hspan : S.toSubmodule ≤ FiniteVectors.orbitSpan κ y := by
    intro u hu
    exact mem_orbitSpan_of_isSimpleModule A s.property hy hu
  let : FiniteDimensional ℂ (FiniteVectors.orbitSpan κ y) := hκ y
  let : FiniteDimensional ℂ S.toSubmodule := Submodule.finiteDimensional_of_le hspan
  have hS : S.toRepresentation.IsIrreducible :=
    (NormalRestrictionOrbit.isIrreducible_iff_isSimpleModule S).mpr hA
  let τ := coordRep S
  let e := (Module.finBasis ℂ S.toSubmodule).equivFun
  let equiv : τ.Equiv S.toRepresentation :=
    Representation.Equiv.mk e.symm (fun k => LinearMap.ext (equivFun_symm_coordRep S k))
  have hτ : τ.IsIrreducible := LengthTwo.isIrreducible_of_equiv equiv.symm hS
  let f : τ.IntertwiningMap κ :=
    { toLinearMap := S.toSubmodule.subtype.comp e.symm.toLinearMap
      isIntertwining' := fun k => LinearMap.ext fun x =>
        congrArg Subtype.val (equivFun_symm_coordRep S k x) }
  have hTy : y ∈ CompactSplitting.isotypicPart τ κ :=
    CompactSplitting.range_le_isotypicPart τ κ f
      ⟨e ⟨y, s.property⟩, congrArg Subtype.val (e.symm_apply_apply ⟨y, s.property⟩)⟩
  obtain ⟨L, hL⟩ := hρ y
  let L₁ := L ⊓ L₀
  have hL₁ : IsCompact (L₁ : Set G) := hL₀.of_isClosed_subset L₁.isClosed
    (fun _ h => (OpenSubgroup.mem_inf.mp h).2)
  refine ⟨L₁, inf_le_right, hL₁, _, τ, hτ, y, hy, ?_, hTy⟩
  intro k
  exact hL ⟨k.val, (OpenSubgroup.mem_inf.mp k.property).1⟩

end Choice

section Lifts

variable {U V W : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {d : ℕ} (τ : Representation ℂ K (Fin d → ℂ)) [τ.IsIrreducible]
  (ρU : Representation ℂ G U) (κU : Representation ℂ K U)
  [IsSemisimpleModule ℂ[K] κU.asModule]
  (hU : Langlands.IsSmooth ρU) (L : OpenSubgroup G) (hL : IsCompact (L : Set G))

/-- The joint projection on the numerator gives the projected representative
of a vector in a compact type of the quotient. -/
def jointCompactQuotientLift (x : U) : U :=
  jointCompactProjection τ ρU κU hU L hL x

variable (ρV : Representation ℂ G V) (κV : Representation ℂ K V)
  [IsSemisimpleModule ℂ[K] κV.asModule] (hV : Langlands.IsSmooth ρV)
  (ρW : Representation ℂ G W) (κW : Representation ℂ K W)
  [IsSemisimpleModule ℂ[K] κW.asModule] (hW : Langlands.IsSmooth ρW)

include hW in
/-- The numerator lift maps to the projected inducing vector and preserves a
quotient value fixed by the finite level and the infinite compact projection. -/
theorem jointCompactQuotientLift_spec
    (i : U →ₗ[ℂ] V) (q : U →ₗ[ℂ] W)
    (hiF : ∀ g x, i (ρU g x) = ρV g (i x)) (hiK : ∀ k x, i (κU k x) = κV k (i x))
    (hqF : ∀ g x, q (ρU g x) = ρW g (q x)) (hqK : ∀ k x, q (κU k x) = κW k (q x))
    (x : U) {y : W} (hx : q x = y) (hyF : y ∈ fixedVectors ρW L.toSubgroup)
    (hyK : y ∈ CompactSplitting.isotypicPart τ κW) :
    i (jointCompactQuotientLift τ ρU κU hU L hL x) = jointCompactProjection τ ρV κV hV L hL (i x) ∧
      q (jointCompactQuotientLift τ ρU κU hU L hL x) = y := by
  refine ⟨jointCompactProjection_natural τ ρU κU hU L hL ρV κV hV i hiF hiK x, ?_⟩
  change q (jointCompactProjection τ ρU κU hU L hL x) = y
  rw [jointCompactProjection_natural τ ρU κU hU L hL ρW κW hW q hqF hqK x, hx]
  exact jointCompactProjection_fixed τ ρW κW hW L hL hyF hyK

end Lifts

end Langlands.Automorphic
