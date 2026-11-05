import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.GeometricIrreducibilityProof
import Langlands.AlgebraicGeometry.Picard.GenericFractionField
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Actual field fibres and generic connectedness -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.GroupScheme

/-- The residue-field embedding determined by an actual field-valued point. -/
def fieldPointResidueMap {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    S.residueField (b (IsLocalRing.closedPoint k)) ⟶ CommRingCat.of k :=
  S.descResidueField (Scheme.stalkClosedPointTo b)

@[reassoc]
theorem fieldPointResidueMap_factorization {S : Scheme.{u}} {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    Spec.map (fieldPointResidueMap b) ≫
      S.fromSpecResidueField (b (IsLocalRing.closedPoint k)) = b :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S b

/-- The actual field-valued pullback is the residue-field fibre followed by
extension along its canonical residue-field embedding. -/
def fieldPointFiberIso {S : Scheme.{u}} (G : GroupScheme S)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    (baseChange b).obj G ≅
      (baseChange (Spec.map (fieldPointResidueMap b))).obj
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) :=
  eqToIso (congrArg (fun f => (baseChange f).obj G)
      (fieldPointResidueMap_factorization b).symm) ≪≫
    baseChangeCompIso _ _ G

/-- Residue-fibre reductivity implies reductivity of every specified
field-valued pullback lying in the same set of base points. -/
theorem fieldReductive_of_residueReductive {S : Scheme.{u}} (G : GroupScheme S)
    (V : Set S)
    (hV : ∀ s ∈ V, IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : b (IsLocalRing.closedPoint k) ∈ V) :
    IsConnectedReductive ((baseChange b).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  have h := connectedReductiveFieldExtensionStatement
    (S.residueField (b (IsLocalRing.closedPoint k))) k _
    (hV _ hb)
  exact h.of_iso (fieldPointFiberIso G b)

/-- A field-valued point lies in the principal open precisely when its
specified coefficient map does not kill the defining scalar. -/
theorem fieldPoint_mem_basicOpen_iff {R k : Type u} [CommRing R] [Field k]
    [Algebra R k] (r : R) :
    (Spec.algebraMap R k) (IsLocalRing.closedPoint k) ∈ PrimeSpectrum.basicOpen r ↔
      algebraMap R k r ≠ 0 := by
  change algebraMap R k r ∉ (IsLocalRing.closedPoint k).asIdeal ↔ _
  change algebraMap R k r ∉ IsLocalRing.maximalIdeal k ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- Geometric irreducibility over an open gives geometric irreducibility
of each specified field-valued pullback whose image lies in that open. -/
theorem geometricallyIrreducible_fieldPullback_of_mem_open
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (hV : GeometricallyIrreducible (f ∣_ V))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (hb : b (IsLocalRing.closedPoint k) ∈ V) :
    GeometricallyIrreducible (pullback.snd f b) := by
  have hr : Set.range b ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    exact ⟨⟨b z, hz ▸ hb⟩, rfl⟩
  let bV := IsOpenImmersion.lift V.ι b hr
  have he : bV ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  have hp : IsPullback (pullback.fst f b) (pullback.snd f b) f (bV ≫ V.ι) := by
    rw [he]
    exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback
    (hp.of_right' (isPullback_morphismRestrict f V).flip) hV

/-- The actual supplied fraction-field pullback and the scheme-theoretic
fibre at the generic point are isomorphic as arrows. -/
def fractionFieldFiberArrowIso (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Arrow.mk (pullback.snd f (Spec.algebraMap R K)) ≅
      Arrow.mk (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))) := by
  let e := Langlands.AlgebraicGeometry.fractionFieldGenericPointIso (CommRingCat.of R) K
  have he : e.hom ≫ (Spec (CommRingCat.of R)).fromSpecResidueField
      (genericPoint (Spec (CommRingCat.of R))) = Spec.algebraMap R K :=
    Langlands.AlgebraicGeometry.fractionFieldGenericPointIso_hom_fromSpecResidueField
      (CommRingCat.of R) K
  let a := pullback.map f (Spec.algebraMap R K) f
    ((Spec (CommRingCat.of R)).fromSpecResidueField
      (genericPoint (Spec (CommRingCat.of R))))
    (𝟙 X) e.hom (𝟙 _) (by simp) (by simpa using he.symm)
  letI : IsIso a := by dsimp [a]; infer_instance
  exact Arrow.isoMk (asIso a) e (by
    simp [a, Scheme.Hom.fiberToSpecResidueField])

/-- Connectedness of a smooth affine supplied generic fibre spreads to all
field-valued points of a single nonempty principal open. -/
theorem exists_principalOpen_connected_fibers (R K : Type u)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (hsm : Smooth G.X.hom) (haff : IsAffineHom G.X.hom)
    (hconn : ConnectedSpace ((baseChange (Spec.algebraMap R K)).obj G).X.left) :
    ∃ r : R, r ≠ 0 ∧ ∀ (k : Type u) [Field k] [Algebra R k],
      algebraMap R k r ≠ 0 → ConnectedSpace ((baseChange (Spec.algebraMap R k)).obj G).X.left := by
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  let GK := (baseChange (Spec.algebraMap R K)).obj G
  have hsmK : Smooth GK.X.hom := by
    change Smooth (pullback.snd G.X.hom (Spec.algebraMap R K))
    infer_instance
  have haffK : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (Spec.algebraMap R K))
    infer_instance
  have hgK : GeometricallyIntegral GK.X.hom :=
    smoothConnectedAffineGeometry.1 K GK hsmK haffK hconn
  let : GeometricallyIntegral GK.X.hom := hgK
  have hgeneric : GeometricallyIrreducible
      (G.X.hom.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R)))) :=
    (geometricallyIrreducible_arrowIso_iff (fractionFieldFiberArrowIso R K G.X.hom)).mp
      (inferInstance : GeometricallyIrreducible GK.X.hom)
  obtain ⟨V, hηV, hV⟩ := finiteTypeGeometricallyIrreducibleGenericSpreading
    G.X.hom _ (genericPoint_spec _) hgeneric
  obtain ⟨_, ⟨r, rfl⟩, hηr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp (V.isOpen.mem_nhds hηV)
  refine ⟨r, ?_, ?_⟩
  · intro hr
    subst r
    simp at hηr
  · intro k _ _ hr
    have hb : (Spec.algebraMap R k) (IsLocalRing.closedPoint k) ∈ V :=
      hrV ((fieldPoint_mem_basicOpen_iff r).mpr hr)
    have : GeometricallyIrreducible (pullback.snd G.X.hom (Spec.algebraMap R k)) :=
      geometricallyIrreducible_fieldPullback_of_mem_open G.X.hom V hV _ hb
    have : IrreducibleSpace ↥(pullback G.X.hom (Spec.algebraMap R k)) :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton
        (pullback.snd G.X.hom (Spec.algebraMap R k))
    change ConnectedSpace ↥(pullback G.X.hom (Spec.algebraMap R k))
    infer_instance

end Langlands.GroupScheme
