import Langlands.Sheaf.Equivariant.LocallyConstant
import Langlands.Sheaf.Equivariant.SmoothPart
import Langlands.Representation.Category.Basic

/-! # The full locally constant sheaf of a smooth coefficient representation -/

noncomputable section

universe u v

namespace Langlands.Sheaf.Equivariant.LocallyConstantSheaf

open CategoryTheory TopologicalSpace Opposite

variable {R : Type u} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X]
  {M : Type u} [AddCommGroup M] [Module R M]

/-- Local constancy and smooth coefficients make every original section locally fixed. -/
theorem isSmoothSheaf (ρ : Representation R G M) (hρ : Langlands.IsSmooth ρ) :
    IsSmoothSheaf R G X (sheaf (X := X) ρ) := by
  intro U s x hx
  change LocallyConstant U.openSet M at s
  let c : M := s ⟨x, hx⟩
  let O : Set X := Subtype.val '' {y : U.openSet | s y = c}
  have hO : IsOpen O :=
    U.openSet.isOpen.isOpenMap_subtype_val _ (s.isLocallyConstant.isOpen_fiber c)
  have hxO : x ∈ O := ⟨⟨x, hx⟩, rfl, rfl⟩
  obtain ⟨H₁, V₁, hV₁, hxV₁, hVO, hH₁⟩ :=
    HasStableNeighbourhoods.exists_stable (G := G) x O hO hxO
  obtain ⟨H₂, hc⟩ := hρ c
  have hH₂ : ∀ h : (H₂ : Subgroup G), ρ (h : G) c = c :=
    (Representation.mem_invariants _ _).mp hc
  let V : ActionOpens G X := ⟨⟨V₁, hV₁⟩⟩
  have hVU : V.openSet ≤ U.openSet := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := hVO hy
    exact z.property
  have hconst (y : V.openSet) : s ⟨y.val, hVU y.property⟩ = c := by
    obtain ⟨z, hz, heq⟩ := hVO y.property
    exact (congrArg s (Subtype.ext heq.symm)).trans hz
  let H : OpenSubgroup G := H₁ ⊓ H₂
  have hV : ∀ h : (H : Subgroup G), ∀ y ∈ V.openSet, (h : G) • y ∈ V.openSet :=
    fun h y hy => hH₁ h (OpenSubgroup.mem_inf.mp h.property).1 y hy
  refine ⟨V, hVU, H, hV, hxV₁, fun h => ?_⟩
  apply LocallyConstant.ext
  intro y
  change ρ ((h : G)⁻¹)⁻¹
    (ρ (1 : G)⁻¹ (s ⟨(1 : G) • ((h : G)⁻¹ • y.val), _⟩)) =
      ρ (1 : G)⁻¹ (s ⟨(1 : G) • y.val, _⟩)
  simp only [inv_inv, inv_one, one_smul, map_one, Module.End.one_apply]
  have hleft := hconst ⟨(h : G)⁻¹ • y.val, hV h⁻¹ y.val y.property⟩
  rw [hleft, hconst y]
  exact hH₂ ⟨h, (OpenSubgroup.mem_inf.mp h.property).2⟩

/-- Bundle the unchanged full locally constant sheaf with its proved smoothness. -/
def smoothSheaf (A : Langlands.SmoothRep.{u, v, u} R G) :
    SmoothTopologicalSheaf R G X :=
  ⟨sheaf A.representation, isSmoothSheaf A.representation A.isSmooth⟩

variable (R G X)

/-- All original pointwise coefficient maps act on the constructed smooth sheaves. -/
def smoothFunctor :
    Langlands.SmoothRep.{u, v, u} R G ⥤ SmoothTopologicalSheaf R G X :=
  (smoothSheafProperty R G X).lift
    (Langlands.SmoothRep.toRep ⋙ functor R G X)
    (fun A => isSmoothSheaf A.representation A.isSmooth)

/-- Forgetting smoothness recovers exactly the original full sheaf coefficient functor. -/
def smoothFunctorForgetIso :
    smoothFunctor R G X ⋙ smoothInclusion R G X ≅
      Langlands.SmoothRep.toRep ⋙ functor R G X :=
  ObjectProperty.liftCompιIso _ _ _

end Langlands.Sheaf.Equivariant.LocallyConstantSheaf
