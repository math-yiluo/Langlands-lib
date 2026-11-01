import Langlands.Shimura.PEL.LieDeterminantBaseChange
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Spaces

/-! # A locally directed affine cover with actual finite free Lie charts -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} (B : AbelianScheme S)

/-- Affine opens contained in a member of the proved finite Lie-basis cover. -/
def affineLieBasisOpens : Set S.Opens :=
  {V | IsAffineOpen V ∧ ∃ k : (lieFiniteLocalBasisData B).I,
    V ≤ (lieFiniteLocalBasisData B).X k}

/-- Refining the Lie cover by affine neighborhoods gives a basis of the base. -/
lemma isBasis_affineLieBasisOpens :
    TopologicalSpace.Opens.IsBasis (affineLieBasisOpens B) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  have hcov := (lieFiniteLocalBasisData B).coversTop
  rw [_root_.Opens.coversTop_iff] at hcov
  obtain ⟨k, hk⟩ := hcov.exists_mem x
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ (lieFiniteLocalBasisData B).X k
      from ⟨hx, hk⟩)
  exact ⟨V, ⟨hV, k, fun y hy => (hVU hy).2⟩, hxV, fun y hy => (hVU hy).1⟩

/-- The cover by all affine opens subordinate to the actual finite Lie-basis cover. -/
def affineLieBasisCover : S.OpenCover.{u} :=
  S.openCoverOfIsOpenCover (fun V : affineLieBasisOpens B => V.1)
    (isBasis_affineLieBasisOpens B).isOpenCover

instance : Preorder (affineLieBasisCover B).I₀ :=
  inferInstanceAs (Preorder (affineLieBasisOpens B))

instance : (affineLieBasisCover B).LocallyDirected :=
  .ofIsBasisOpensRange (fun {V V'} => by
      change V.1 ≤ V'.1 ↔ _
      simp [affineLieBasisCover]) (by
    have h :
        Set.range (fun V : (affineLieBasisCover B).I₀ =>
          ((affineLieBasisCover B).f V).opensRange) = affineLieBasisOpens B := by
      ext U
      simp only [affineLieBasisCover, Scheme.openCoverOfIsOpenCover_f,
        Scheme.Opens.opensRange_ι, Set.mem_range]
      exact ⟨fun ⟨V, hV⟩ => hV ▸ V.2, fun hU => ⟨⟨U, hU⟩, rfl⟩⟩
    rw [h]
    exact isBasis_affineLieBasisOpens B)

instance (V : (affineLieBasisCover B).I₀) : IsAffine ((affineLieBasisCover B).X V) :=
  V.2.1

/-- A member of the original Lie cover containing the chosen affine open. -/
def affineLieBasisIndex (V : (affineLieBasisCover B).I₀) :
    (lieFiniteLocalBasisData B).I :=
  V.2.2.choose

lemma affineLieBasis_le (V : (affineLieBasisCover B).I₀) :
    V.1 ≤ (lieFiniteLocalBasisData B).X (affineLieBasisIndex B V) :=
  V.2.2.choose_spec

/-- The finite basis indexing type inherited from the proved Lie trivialization. -/
abbrev affineLieBasisType (V : (affineLieBasisCover B).I₀) : Type u :=
  ((lieFiniteLocalBasisData B).generators (affineLieBasisIndex B V)).I

instance (V : (affineLieBasisCover B).I₀) : Fintype (affineLieBasisType B V) :=
  inferInstanceAs
    (Fintype ((lieFiniteLocalBasisData B).generators (affineLieBasisIndex B V)).I)

lemma affineLieBasis_preimage (V : (affineLieBasisCover B).I₀) :
    (affineLieBasisCover B).f V ⁻¹ᵁ
      (lieFiniteLocalBasisData B).X (affineLieBasisIndex B V) = ⊤ := by
  apply top_unique
  intro x hx
  exact affineLieBasis_le B V x.property

set_option maxHeartbeats 800000 in
/-- A global finite free chart on the actual pulled-back abelian scheme on each affine member. -/
def affineLieBasisTrivialization (V : (affineLieBasisCover B).I₀) :
    SheafOfModules.free
        (R := ((affineLieBasisCover B).X V).ringCatSheaf.over ⊤)
        (affineLieBasisType B V) ≅
      ((baseChange ((affineLieBasisCover B).f V)).obj B).Lie.over ⊤ := by
  have e := lieBaseChangeChart ((affineLieBasisCover B).f V) B
    (I := affineLieBasisType B V)
    (lieFiniteLocalBasisTrivialization B (affineLieBasisIndex B V))
  rw [affineLieBasis_preimage B V] at e
  exact e

end Langlands.AbelianScheme
