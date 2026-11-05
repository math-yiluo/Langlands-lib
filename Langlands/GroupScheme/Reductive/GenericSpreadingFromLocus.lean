import Langlands.GroupScheme.Reductive.GenericSpreadingAssembly
import Langlands.GroupScheme.Reductive.IdentityComponentLocus

/-! # Generic spreading from openness of the identity-component locus -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The coefficient map representing the actual geometric point of an affine base. -/
def geometricPointScalarMap (R : Type u) [CommRing R]
    (s : Spec (CommRingCat.of R)) :
    R →+* AlgebraicClosure ((Spec (CommRingCat.of R)).residueField s) :=
  (Spec.map_surjective (geometricPoint _ s)).choose.hom

/-- The chosen scalar map represents the specified geometric point itself. -/
theorem geometricPointScalarMap_spec (R : Type u) [CommRing R]
    (s : Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (geometricPointScalarMap R s)) = geometricPoint _ s :=
  (Spec.map_surjective (geometricPoint _ s)).choose_spec

/-- Connectedness for all field-valued points of a principal open applies to the
actual geometric fibre at each point of that open. -/
theorem connected_geometricFiber_of_fieldConnected {R : Type u} [CommRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (r : R)
    (h : ∀ (k : Type u) [Field k] [Algebra R k], algebraMap R k r ≠ 0 →
      ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left)
    (s : Spec (CommRingCat.of R)) (hs : s ∈ PrimeSpectrum.basicOpen r) :
    ConnectedSpace (geometricFiber G s).X.left := by
  let A := AlgebraicClosure ((Spec (CommRingCat.of R)).residueField s)
  let : Algebra R A := (geometricPointScalarMap R s).toAlgebra
  have he : Spec.algebraMap R A = geometricPoint _ s :=
    geometricPointScalarMap_spec R s
  have hp : (Spec.algebraMap R A) (IsLocalRing.closedPoint A) = s := by
    rw [he]
    change (Spec (CommRingCat.of R)).fromSpecResidueField s
      ((toAlgebraicClosure _ ) (IsLocalRing.closedPoint A)) = s
    exact Scheme.fromSpecResidueField_apply _ _
  have hr : algebraMap R A r ≠ 0 :=
    (fieldPoint_mem_basicOpen_iff r).mp (by rwa [hp])
  have hc := h A hr
  change ConnectedSpace ((baseChange (geometricPoint _ s)).obj G).X.left
  rwa [he] at hc

/-- The published identity-component locus interface supplies the exact generic
spreading conclusion once its structural openness proposition is proved. -/
theorem genericReductivitySpreading_of_identityComponentLocusOpen
    (hopen : IdentityComponentReductiveLocusOpenStatement.{u}) :
    GenericReductivitySpreadingStatement.{u} := by
  intro R K _ _ _ _ _ _ G hsm haff hK
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let S := Spec (CommRingCat.of R)
  let η := genericPoint S
  have hres : IsConnectedReductive ((baseChange (S.fromSpecResidueField η)).obj G) :=
    genericResidueReductive_of_fractionFieldReductive R K G hK
  have hgeom : IsConnectedReductive (geometricFiber G η) := by
    have hext := connectedReductiveFieldExtensionStatement (S.residueField η)
      (AlgebraicClosure (S.residueField η)) _ hres
    exact hext.of_iso (baseChangeCompIso (S.fromSpecResidueField η)
      (toAlgebraicClosure (S.residueField η)) G)
  have hη : η ∈ identityComponentReductiveLocus G := hgeom.identityComponent
  obtain ⟨r₁, hr₁, hc⟩ := exists_principalOpen_connected_fibers R K G hsm haff
    hK.connectedSpace
  obtain ⟨_, ⟨r₂, rfl⟩, hηr₂, hr₂V⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp
      ((hopen S G).mem_nhds hη)
  have hr₂ : r₂ ≠ 0 := by
    intro hz
    subst r₂
    simp at hηr₂
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, ?_⟩
  intro k _ _ hr
  have hr' : algebraMap R k r₁ * algebraMap R k r₂ ≠ 0 := by
    simpa only [map_mul] using hr
  obtain ⟨hk₁, hk₂⟩ := mul_ne_zero_iff.mp hr'
  let s := (Spec.algebraMap R k) (IsLocalRing.closedPoint k)
  have hs₁ : s ∈ PrimeSpectrum.basicOpen r₁ :=
    (fieldPoint_mem_basicOpen_iff r₁).mpr hk₁
  have hs₂ : s ∈ identityComponentReductiveLocus G :=
    hr₂V ((fieldPoint_mem_basicOpen_iff r₂).mpr hk₂)
  let : ConnectedSpace (geometricFiber G s).X.left :=
    connected_geometricFiber_of_fieldConnected G r₁ hc s hs₁
  have hg : IsConnectedReductive (geometricFiber G s) :=
    isConnectedReductive_geometricFiber_of_mem_identityComponentReductiveLocus G s hs₂
  have hi : IsConnectedReductive
      ((baseChange (toAlgebraicClosure (S.residueField s))).obj
        ((baseChange (S.fromSpecResidueField s)).obj G)) :=
    hg.of_iso (baseChangeCompIso (S.fromSpecResidueField s)
      (toAlgebraicClosure (S.residueField s)) G).symm
  have hsred : IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G) :=
    IsConnectedReductive.of_fieldExtension
      (k := S.residueField s) (K := AlgebraicClosure (S.residueField s)) hi
  exact (fieldReductive_iff_residueReductive G (Spec.algebraMap R k)).mpr hsred

end Langlands.GroupScheme
