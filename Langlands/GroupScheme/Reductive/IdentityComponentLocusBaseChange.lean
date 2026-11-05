import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Base change of the reductive identity-component locus -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

local instance smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) :
    Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom b))

local instance affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace IdentityComponent

/-- Reductivity of the actual identity component is preserved and reflected by
every extension of the ground field. -/
theorem isConnectedReductive_baseChange_iff {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    IsConnectedReductive (identityComponent ((baseChange (specMap φ)).obj H)) ↔
      IsConnectedReductive (identityComponent H) := by
  let : Algebra k K := φ.toAlgebra
  constructor
  · intro h
    exact IsConnectedReductive.of_fieldExtension (k := k) (K := K)
      (h.of_iso (baseChangeIso H φ))
  · intro h
    exact (connectedReductiveFieldExtensionStatement k K _ h).of_iso
      (baseChangeIso H φ).symm

end IdentityComponent

variable {S : Scheme.{u}} (G : GroupScheme S)
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The actual identity component at a field-valued point is the scalar
extension of the actual identity component of its residue-field fibre. -/
def fieldPointIdentityComponentIso
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    identityComponent ((baseChange b).obj G) ≅
      (baseChange (Spec.map (fieldPointResidueMap b))).obj
        (identityComponent
          ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G)) :=
  IdentityComponent.mapIso (fieldPointFiberIso G b) ≪≫
    (IdentityComponent.baseChangeIso _
      (fieldPointResidueMap b).hom).symm

/-- For any actual field-valued point, reductivity of the identity component
is equivalent to the same condition on its residue-field fibre. -/
theorem fieldIdentityComponentReductive_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsConnectedReductive (identityComponent ((baseChange b).obj G)) ↔
      IsConnectedReductive (identityComponent
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G)) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let H := (baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G
  constructor
  · intro h
    exact IsConnectedReductive.of_fieldExtension
      (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
      (h.of_iso (fieldPointIdentityComponentIso G b).symm)
  · intro h
    exact (connectedReductiveFieldExtensionStatement
      (S.residueField (b (IsLocalRing.closedPoint k))) k (identityComponent H) h).of_iso
      (fieldPointIdentityComponentIso G b)

/-- The chosen algebraic closure in the locus definition can be replaced
by the actual residue field without changing membership. -/
theorem mem_identityComponentReductiveLocus_iff_residueFiber (s : S) :
    s ∈ identityComponentReductiveLocus G ↔
      IsConnectedReductive (identityComponent
        ((baseChange (S.fromSpecResidueField s)).obj G)) := by
  have h := fieldIdentityComponentReductive_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rw [himage] at h
  exact h

/-- Every actual field-valued point detects exactly membership of its image
in the reductive geometric identity-component locus. -/
theorem fieldIdentityComponentReductive_iff_mem_locus
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsConnectedReductive (identityComponent ((baseChange b).obj G)) ↔
      b (IsLocalRing.closedPoint k) ∈ identityComponentReductiveLocus G :=
  (fieldIdentityComponentReductive_iff_residueFiber G b).trans
    (mem_identityComponentReductiveLocus_iff_residueFiber G _).symm

/-- The actual reductive geometric identity-component locus commutes with
arbitrary base change, with no hypothesis on the base-change morphism. -/
theorem identityComponentReductiveLocus_baseChange {T : Scheme.{u}} (b : T ⟶ S) :
    identityComponentReductiveLocus ((baseChange b).obj G) =
      b ⁻¹' identityComponentReductiveLocus G := by
  ext t
  have he := IdentityComponent.mapIso (baseChangeCompIso b (geometricPoint T t) G)
  have hfield := fieldIdentityComponentReductive_iff_mem_locus G (geometricPoint T t ≫ b)
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  rw [himage] at hfield
  change IsConnectedReductive
      (identityComponent ((baseChange (geometricPoint T t)).obj ((baseChange b).obj G))) ↔
    b t ∈ identityComponentReductiveLocus G
  constructor
  · intro ht
    exact hfield.mp (ht.of_iso he)
  · intro ht
    exact (hfield.mpr ht).of_iso he.symm

end Langlands.GroupScheme
