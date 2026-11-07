import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.Reductive.Basic

/-! # Surjective morphisms onto reduced schemes are epimorphisms

A morphism of schemes whose underlying map is surjective and whose target is reduced is an
epimorphism in the category of all schemes, and hence in every category `Over S`. No
separatedness, finiteness or group structure is assumed on the test target. For a smooth
group scheme over a field, this reduces epimorphy of the subgroup multiplication map to
surjectivity of its underlying map.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace Langlands.AlgebraicGeometry.SurjectiveReducedEpi

variable {X Y T : Scheme.{u}}

/-- Two morphisms out of a reduced scheme agree once they agree after composition with every
residue-field point `Spec κ(y) ⟶ Y`. The target `T` is arbitrary. -/
theorem ext_of_fromSpecResidueField_eq [IsReduced Y] (g h : Y ⟶ T)
    (H : ∀ y : Y, Y.fromSpecResidueField y ≫ g = Y.fromSpecResidueField y ≫ h) : g = h := by
  apply Scheme.hom_ext_of_forall
  intro y
  have hgy : g y = h y := by
    obtain ⟨s⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
    have := congrArg (fun φ : Spec (Y.residueField y) ⟶ T => φ s) (H y)
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  let U : Y.Opens := g ⁻¹ᵁ V ⊓ h ⁻¹ᵁ V
  refine ⟨U, ⟨hyV, show h y ∈ V from hgy ▸ hyV⟩, ?_⟩
  have : IsAffine V := hV
  rw [← g.resLE_comp_ι (U := V) (V := U) inf_le_left,
    ← h.resLE_comp_ι (U := V) (V := U) inf_le_right]
  congr 1
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq _ _ (terminal.from _) Set.univ
    dense_univ (fun u _ => ?_) (terminal.hom_ext _ _)
  rw [← cancel_mono (Scheme.Opens.ι V), Category.assoc, Category.assoc, g.resLE_comp_ι, h.resLE_comp_ι,
    ← U.ι.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
    ← U.ι.SpecMap_residueFieldMap_fromSpecResidueField_assoc, H]

/-- The morphism of spectra induced by a homomorphism of fields is an epimorphism of schemes. -/
theorem epi_SpecMap_of_fields {K L : Type u} [Field K] [Field L]
    (φ : CommRingCat.of K ⟶ CommRingCat.of L) : Epi (Spec.map φ) := by
  have : Surjective (Spec.map φ) :=
    ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [φ.hom]
    exact (RingHom.flat_algebraMap_iff).mpr inferInstance
  exact Flat.epi_of_flat_of_surjective _

/-- A morphism of schemes that is surjective onto a reduced scheme is an epimorphism in the
category of schemes, cancelling against arbitrary target schemes. -/
theorem epi_of_surjective [IsReduced Y] (f : X ⟶ Y) [Surjective f] : Epi f := by
  constructor
  intro T g h hgh
  apply ext_of_fromSpecResidueField_eq g h
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  have := epi_SpecMap_of_fields (f.residueFieldMap x)
  rw [← cancel_epi (Spec.map (f.residueFieldMap x)),
    f.SpecMap_residueFieldMap_fromSpecResidueField_assoc,
    f.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hgh]

/-- A morphism over `S` whose underlying morphism is surjective onto a reduced scheme is an
epimorphism in `Over S`. -/
theorem over_epi_of_surjective {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) [IsReduced B.left]
    [Surjective f.left] : Epi f := by
  have : Epi ((Over.forget S).map f) := epi_of_surjective f.left
  exact (Over.forget S).epi_of_epi_map this

end Langlands.AlgebraicGeometry.SurjectiveReducedEpi

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry

variable {k : Type u} [Field k] {G Z D : GroupScheme (Spec (CommRingCat.of k))}

/-- For a smooth group scheme over a field, the subgroup multiplication map is an epimorphism in
`Over (Spec k)` as soon as its underlying morphism of schemes is surjective. -/
theorem epi_subgroupProductMap_of_surjective_of_smooth (hG : Smooth G.X.hom) (i : Z ⟶ G)
    (d : D ⟶ G) (hsurj : Function.Surjective (subgroupProductMap i d).left) :
    Epi (subgroupProductMap i d) := by
  have := hG
  have : IsReduced G.X.left :=
    SmoothReducedProof.isReduced_of_smooth_over_field k G.X.left G.X.hom
  have : Surjective (subgroupProductMap i d).left := ⟨hsurj⟩
  exact SurjectiveReducedEpi.over_epi_of_surjective _

/-- For a connected reductive group over a field, the subgroup multiplication map is an
epimorphism in `Over (Spec k)` as soon as its underlying morphism of schemes is surjective. -/
theorem IsConnectedReductive.epi_subgroupProductMap_of_surjective (hG : IsConnectedReductive G)
    (i : Z ⟶ G) (d : D ⟶ G) (hsurj : Function.Surjective (subgroupProductMap i d).left) :
    Epi (subgroupProductMap i d) :=
  epi_subgroupProductMap_of_surjective_of_smooth hG.smooth i d hsurj

end Langlands.GroupScheme
