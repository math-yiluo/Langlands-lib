import Langlands.Sheaf.Equivariant.TwistedInductionSmoothCoordinates
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open-subgroup invariant coordinate maps on twisted induction -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite
open LocalActionSystem

universe v u uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)
variable {R : Type w} [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]
variable {F F' : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R}

/-- Apply a possibly different natural coefficient map at each group coordinate. -/
def indexedMapApp (η : G → (F ⟶ F')) (U : TwistedOver P ρ)
    (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    ((ι P ρ).op.ran.obj F').obj (op U) :=
  (moduleCoordinates ρ F' U).symm fun g =>
    (η g).app (op ((translate P ρ g).obj U.obj)) (moduleCoordinates ρ F U s g)

@[simp]
theorem indexedMapApp_coordinates (η : G → (F ⟶ F')) (U : TwistedOver P ρ)
    (s : ((ι P ρ).op.ran.obj F).obj (op U)) (g : G) :
    moduleCoordinates ρ F' U (indexedMapApp ρ η U s) g =
      (η g).app (op ((translate P ρ g).obj U.obj)) (moduleCoordinates ρ F U s g) :=
  congrFun ((moduleCoordinates ρ F' U).apply_symm_apply _) g

/-- A twisted restriction shifts the family of coefficient maps by its inverse twist. -/
theorem map_indexedMapApp (η : G → (F ⟶ F')) {U V : TwistedOver P ρ}
    (f : U ⟶ V) (s : ((ι P ρ).op.ran.obj F).obj (op V)) :
    ((ι P ρ).op.ran.obj F').map f.op (indexedMapApp ρ η V s) =
      indexedMapApp ρ (fun g => η (g * (Hom.twist f)⁻¹)) U
        (((ι P ρ).op.ran.obj F).map f.op s) := by
  apply (moduleCoordinates ρ F' U).injective
  funext g
  have hF := congrFun (moduleCoordinates_map ρ F f s) g
  have hF' := congrFun (moduleCoordinates_map ρ F' f (indexedMapApp ρ η V s)) g
  change moduleCoordinates ρ F U (((ι P ρ).op.ran.obj F).map f.op s) g =
    F.map (transport ρ f g).op
      (moduleCoordinates ρ F V s (g * (Hom.twist f)⁻¹)) at hF
  change moduleCoordinates ρ F' U
      (((ι P ρ).op.ran.obj F').map f.op (indexedMapApp ρ η V s)) g =
    F'.map (transport ρ f g).op
      (moduleCoordinates ρ F' V (indexedMapApp ρ η V s)
        (g * (Hom.twist f)⁻¹)) at hF'
  rw [hF', indexedMapApp_coordinates, indexedMapApp_coordinates, hF]
  exact ((η (g * (Hom.twist f)⁻¹)).naturality_apply (transport ρ f g).op _).symm

variable [TopologicalSpace G]

/-- An open-subgroup invariant coordinate map preserves discreteness for every
local action whose twist is the inverse of its acting element. -/
theorem isDiscreteSection_indexedMapApp
    (η : G → (F ⟶ F')) (K : OpenSubgroup G)
    (hη : ∀ (g k : G), k ∈ K → η (g * k) = η g)
    {U : TwistedOver P ρ} {H : OpenSubgroup G}
    (a : (H : Subgroup G) →* (End U)ᵐᵒᵖ) (ha : IsLift a)
    (s : ((ι P ρ).op.ran.obj F).obj (op U))
    (hs : IsDiscreteSection ((ι P ρ).op.ran.obj F) a s) :
    IsDiscreteSection ((ι P ρ).op.ran.obj F') a (indexedMapApp ρ η U s) := by
  obtain ⟨J, hJH, hJ⟩ := hs
  refine ⟨J ⊓ K, inf_le_left.trans hJH, fun h hh => ?_⟩
  have he : (fun g => η (g * (Hom.twist (a h).unop.asHom)⁻¹)) = η := by
    funext g
    rw [ha h, inv_inv]
    exact hη g h (OpenSubgroup.mem_inf.1 hh).2
  rw [map_indexedMapApp, he, hJ h (OpenSubgroup.mem_inf.1 hh).1]

variable [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G) (hL : L.IsLiftSystem)

include hL

/-- Right invariance under an open subgroup is sufficient to preserve the entire
discrete sieve, even though the coordinate map need not be natural for all twists. -/
theorem discreteSieve_le_indexedMapApp
    (η : G → (F ⟶ F')) (K : OpenSubgroup G)
    (hη : ∀ (g k : G), k ∈ K → η (g * k) = η g)
    (U : TwistedOver P ρ) (s : ((ι P ρ).op.ran.obj F).obj (op U)) :
    L.discreteSieve ((ι P ρ).op.ran.obj F) s ≤
      L.discreteSieve ((ι P ρ).op.ran.obj F') (indexedMapApp ρ η U s) := by
  rintro W p ⟨V, k, f, H, a, ha, hs, hp⟩
  let t := Hom.twist f
  let K' : OpenSubgroup G :=
    ⟨(K : Subgroup G).comap (MulAut.conj t).toMonoidHom,
      K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hη' : ∀ (g j : G), j ∈ K' →
      η ((g * j) * t⁻¹) = η (g * t⁻¹) := by
    intro g j hj
    have hj' : t * j * t⁻¹ ∈ K := by
      change (MulAut.conj t) j ∈ K at hj
      simpa only [MulAut.conj_apply] using hj
    have he : (g * j) * t⁻¹ = (g * t⁻¹) * (t * j * t⁻¹) := by group
    rw [he, hη _ _ hj']
  refine ⟨V, k, f, H, a, ha, ?_, hp⟩
  rw [map_indexedMapApp]
  exact isDiscreteSection_indexedMapApp ρ (fun g => η (g * t⁻¹)) K' hη' a
    (hL V H a ha) _ hs

/-- Stable coordinate cutoffs preserve the existing locally discrete submodule. -/
theorem indexedMapApp_mem_smoothSubmodule
    (J : GrothendieckTopology (TwistedOver P ρ)) [L.HasAdmissibleRefinements J]
    (η : G → (F ⟶ F')) (K : OpenSubgroup G)
    (hη : ∀ (g k : G), k ∈ K → η (g * k) = η g)
    (U : TwistedOver P ρ) (s : ((ι P ρ).op.ran.obj F).obj (op U))
    (hs : s ∈ smoothSubmodule L J ((ι P ρ).op.ran.obj F) U) :
    indexedMapApp ρ η U s ∈ smoothSubmodule L J ((ι P ρ).op.ran.obj F') U :=
  J.superset_covering (discreteSieve_le_indexedMapApp ρ L hL η K hη U s) hs

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
