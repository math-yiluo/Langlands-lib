import Langlands.Global.AdelicL2FiniteVectorDensity
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Finite vectors of a finite orthogonal sum in adelic `L²` -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

universe u

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RestrictionSplitCentre

section FiniteSubmodule

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "H" => Lp ℂ 2 (canonicalMeasure F G)
local notation "R" => canonicalL2RightAction F G centralSplitTorusCharacter

/-- The compact-finite, finite-level submodule of the canonical quotient Hilbert space. -/
def canonicalL2FiniteSubmodule (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) : Submodule ℂ H :=
  (FiniteVectors.subrepresentation
    (((R hG).comp (ofInfinite F G).toMonoidHom).comp
      (K.comap (ofInfinite F G).toMonoidHom).subtype)).toSubmodule ⊓
  Langlands.smoothVectors ((R hG).comp (ofFinite F G).toMonoidHom)

theorem mem_canonicalL2FiniteSubmodule (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) (v : H) :
    v ∈ canonicalL2FiniteSubmodule hG K ↔ IsCanonicalL2FiniteVector hG K v := by
  constructor
  · rintro ⟨hK, L, hL⟩
    exact ⟨hK, L.toSubgroup, L.isOpen, fun l hl => hL ⟨l, hl⟩⟩
  · rintro ⟨hK, L, hLo, hL⟩
    exact ⟨hK, ⟨⟨L, hLo⟩, fun l => hL l l.property⟩⟩

end FiniteSubmodule

/-- Orthogonal projection and finite summation identify the finite vectors of a finite
invariant orthogonal sum with the product of the finite-vector spaces of its summands. -/
def AdelicL2FiniteSumStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (K : Subgroup (AdelicGroupPoints F G))
    (Index : Type u) [Fintype Index],
    let H := Lp ℂ 2 (canonicalMeasure F G)
    let R := canonicalL2RightAction F G centralSplitTorusCharacter hG
    ∀ (V : Index → Submodule ℂ H)
    (hClosed : ∀ i, IsClosed (V i : Set H)),
    (∀ g i, ∀ x ∈ V i, R g x ∈ V i) →
    OrthogonalFamily ℂ (fun i => ↥(V i)) (fun i => (V i).subtypeₗᵢ) →
    letI (i : Index) : CompleteSpace (V i) := (hClosed i).completeSpace_coe
    let C := canonicalL2FiniteSubmodule hG K
    ∃ e : ↥((⨆ i, V i) ⊓ C) ≃ₗ[ℂ] ((i : Index) → ↥(V i ⊓ C)),
      (∀ x i, (e x i : H) = (V i).starProjection x.val) ∧
      (∀ y, (e.symm y : H) = ∑ i, (y i : H))

end Langlands.Global
