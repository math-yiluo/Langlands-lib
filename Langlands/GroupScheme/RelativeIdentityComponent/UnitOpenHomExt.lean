import Langlands.GroupScheme.RelativeIdentityComponent.SmoothReduction

/-! # Equality of group homomorphisms on an open neighbourhood of the unit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Multiplication of two copies of an open containing the whole unit section
is a one-member smooth cover when the residue fibres are connected. -/
def unitOpenMultiplicationCover {S : Scheme.{u}} {G : GroupScheme S} [Smooth G.X.hom]
    (hconn : ∀ s : S, ConnectedSpace (residueFiber G s).X.left)
    {P : Over S} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : ∀ s : S, unitSection G s ∈ Set.range i.left) :
    Scheme.Cover.{0} (Scheme.precoverage @Smooth) G.X.left := by
  let m := (i ⊗ₘ i) ≫ μ[G.X]
  have hsurj : Function.Surjective m.left := by
    intro x
    apply underlyingSet_subset_range_product G i he
    let s := G.X.hom x
    let y : (residueFiber G s).X.left := G.X.hom.asFiber x
    let : ConnectedSpace (residueFiber G s).X.left := hconn s
    have hy : y ∈ IdentityComponent.identitySet (residueFiber G s) := by
      change y ∈ connectedComponent (IdentityComponent.identityPoint (residueFiber G s))
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.mem_univ _
    exact ⟨s, y, hy, G.X.hom.fiberι_asFiber x⟩
  have : IsOpenImmersion (i ⊗ₘ i).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (Over.w i).symm (Over.w i).symm
  have : Smooth μ[G.X].left := smooth_multiplication G
  refine Scheme.Cover.mkOfCovers PUnit (fun _ => (P ⊗ P).left) (fun _ => m.left)
    (fun x => ⟨PUnit.unit, hsurj x⟩) (fun _ => ?_)
  change Smooth ((i ⊗ₘ i).left ≫ μ[G.X].left)
  infer_instance

/-- Two homomorphisms from a smooth group with connected residue fibres agree
if they agree on an open neighbourhood of the entire unit section. -/
theorem hom_ext_of_comp_unitOpen_eq {S : Scheme.{u}} {G H : GroupScheme S}
    [Smooth G.X.hom] (hconn : ∀ s : S, ConnectedSpace (residueFiber G s).X.left)
    {P : Over S} (i : P ⟶ G.X) [IsOpenImmersion i.left]
    (he : ∀ s : S, unitSection G s ∈ Set.range i.left)
    {f g : G ⟶ H} (hi : i ≫ f.hom.hom = i ≫ g.hom.hom) :
    f = g := by
  let m := (i ⊗ₘ i) ≫ μ[G.X]
  let cover := unitOpenMultiplicationCover hconn i he
  have : Surjective m.left := by
    constructor
    intro x
    obtain ⟨_, hx⟩ :=
      ((Scheme.presieve₀_mem_precoverage_iff cover.toPreZeroHypercover).mp cover.mem₀).1 x
    change x ∈ Set.range m.left at hx
    exact hx
  have : Smooth m.left := cover.map_prop PUnit.unit
  have : Epi m.left := Flat.epi_of_flat_of_surjective _
  have : Epi m := Over.epi_of_epi_left _
  apply Grp.hom_ext
  apply (cancel_epi m).mp
  change ((i ⊗ₘ i) ≫ μ[G.X]) ≫ f.hom.hom =
    ((i ⊗ₘ i) ≫ μ[G.X]) ≫ g.hom.hom
  simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hi]

end Langlands.GroupScheme.RelativeIdentityComponent
