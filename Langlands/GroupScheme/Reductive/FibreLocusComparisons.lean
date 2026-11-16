import Langlands.GroupScheme.Reductive.IdentityComponentLocusBaseChange
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci

/-! # Fibrewise reductive and semisimple locus comparisons -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

local instance fibreLocus_smooth_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (b : T ⟶ S) : Smooth ((baseChange b).obj G).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom b))

local instance fibreLocus_affine_pullback {S T : Scheme.{u}} (G : GroupScheme S)
    [IsAffineHom G.X.hom] (b : T ⟶ S) : IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace IdentityComponent

/-- Semisimplicity of the actual identity component is preserved and reflected
by every extension of the ground field. -/
theorem isSemisimple_baseChange_iff {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    IsSemisimple (identityComponent ((baseChange (specMap φ)).obj H)) ↔
      IsSemisimple (identityComponent H) := by
  let : Algebra k K := φ.toAlgebra
  constructor
  · intro h
    exact IsSemisimple.of_fieldExtension (k := k) (K := K)
      (h.of_iso (baseChangeIso H φ))
  · intro h
    exact (isSemisimpleFieldExtension k K _ h).of_iso
      (baseChangeIso H φ).symm

end IdentityComponent

variable {S : Scheme.{u}} (G : GroupScheme S)
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Points where the actual identity component of the geometric fibre is semisimple. -/
def identityComponentSemisimpleLocus : Set S :=
  {s | IsSemisimple (identityComponent (geometricFiber G s))}

/-- Fullness of the semisimple identity-component locus is the exact fibrewise condition. -/
theorem identityComponentSemisimpleLocus_eq_univ_iff :
    identityComponentSemisimpleLocus G = Set.univ ↔
      ∀ s : S, IsSemisimple (identityComponent (geometricFiber G s)) :=
  Set.eq_univ_iff_forall

/-- For an actual field-valued point, semisimplicity of the identity component
is equivalent to the same condition on its residue-field fibre. -/
theorem fieldIdentityComponentSemisimple_iff_residueFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsSemisimple (identityComponent ((baseChange b).obj G)) ↔
      IsSemisimple (identityComponent
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G)) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  let H := (baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G
  constructor
  · intro h
    exact IsSemisimple.of_fieldExtension
      (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k)
      (h.of_iso (fieldPointIdentityComponentIso G b).symm)
  · intro h
    exact (isSemisimpleFieldExtension
      (S.residueField (b (IsLocalRing.closedPoint k))) k (identityComponent H) h).of_iso
      (fieldPointIdentityComponentIso G b)

/-- The chosen algebraic closure can be replaced by the residue field in the
semisimple identity-component locus. -/
theorem mem_identityComponentSemisimpleLocus_iff_residueFiber (s : S) :
    s ∈ identityComponentSemisimpleLocus G ↔
      IsSemisimple (identityComponent
        ((baseChange (S.fromSpecResidueField s)).obj G)) := by
  have h := fieldIdentityComponentSemisimple_iff_residueFiber G (geometricPoint S s)
  have himage : (geometricPoint S s)
      (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) = s := by
    change S.fromSpecResidueField s _ = s
    exact Scheme.fromSpecResidueField_apply _ _
  rw [himage] at h
  exact h

/-- Every actual field-valued point detects membership of its image in the
semisimple geometric identity-component locus. -/
theorem fieldIdentityComponentSemisimple_iff_mem_locus
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsSemisimple (identityComponent ((baseChange b).obj G)) ↔
      b (IsLocalRing.closedPoint k) ∈ identityComponentSemisimpleLocus G :=
  (fieldIdentityComponentSemisimple_iff_residueFiber G b).trans
    (mem_identityComponentSemisimpleLocus_iff_residueFiber G _).symm

/-- The actual semisimple geometric identity-component locus commutes with
arbitrary base change. -/
theorem identityComponentSemisimpleLocus_baseChange {T : Scheme.{u}} (b : T ⟶ S) :
    identityComponentSemisimpleLocus ((baseChange b).obj G) =
      b ⁻¹' identityComponentSemisimpleLocus G := by
  ext t
  have he := IdentityComponent.mapIso (baseChangeCompIso b (geometricPoint T t) G)
  have hfield := fieldIdentityComponentSemisimple_iff_mem_locus G (geometricPoint T t ≫ b)
  have himage : (geometricPoint T t ≫ b)
      (IsLocalRing.closedPoint (AlgebraicClosure (T.residueField t))) = b t := by
    change b (T.fromSpecResidueField t _) = b t
    rw [Scheme.fromSpecResidueField_apply]
  rw [himage] at hfield
  change IsSemisimple
      (identityComponent ((baseChange (geometricPoint T t)).obj ((baseChange b).obj G))) ↔
    b t ∈ identityComponentSemisimpleLocus G
  constructor
  · intro ht
    exact hfield.mp (ht.of_iso he)
  · intro ht
    exact (hfield.mpr ht).of_iso he.symm

/-- Reductivity is geometric connectedness together with reductivity of the
identity components of all actual geometric fibres. -/
theorem isReductive_iff_geometricallyConnected_and_locus_eq_univ :
    IsReductive G ↔ GeometricallyConnected G.X.hom ∧
      identityComponentReductiveLocus G = Set.univ := by
  constructor
  · intro hG
    refine ⟨?_, Set.eq_univ_iff_forall.mpr fun s => ?_⟩
    · refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun k _ f => ?_⟩
      exact (hG.isConnectedReductive_baseChange f).connectedSpace
    · exact (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed.identityComponent
  · rintro ⟨hc, hloc⟩
    let : GeometricallyConnected G.X.hom := hc
    refine ⟨inferInstance, inferInstance, fun s => ?_⟩
    have : ConnectedSpace (geometricFiber G s).X.left := by
      change ConnectedSpace ↥(pullback G.X.hom (geometricPoint S s))
      infer_instance
    exact (isConnectedReductive_geometricFiber_of_mem_identityComponentReductiveLocus
      G s (Set.eq_univ_iff_forall.mp hloc s)).isPseudoReductive

/-- For geometrically connected groups, semisimplicity of every geometric fibre
is equivalent to fullness of the semisimple identity-component locus. -/
theorem semisimple_geometricFibres_iff_locus_eq_univ
    (hc : GeometricallyConnected G.X.hom) :
    (∀ s : S, IsSemisimple (geometricFiber G s)) ↔
      identityComponentSemisimpleLocus G = Set.univ := by
  let : GeometricallyConnected G.X.hom := hc
  have hconn (s : S) : ConnectedSpace (geometricFiber G s).X.left := by
    change ConnectedSpace ↥(pullback G.X.hom (geometricPoint S s))
    infer_instance
  rw [identityComponentSemisimpleLocus_eq_univ_iff]
  constructor
  · intro hs s
    let := hconn s
    exact (hs s).of_iso (IdentityComponent.connectedIso (geometricFiber G s))
  · intro hs s
    let := hconn s
    exact (hs s).of_iso (IdentityComponent.connectedIso (geometricFiber G s)).symm

/-- The relative semisimple condition is geometric connectedness together with
semisimplicity of the identity components of all actual geometric fibres. -/
theorem isReductive_and_semisimple_geometricFibres_iff_locus :
    (IsReductive G ∧ ∀ s : S, IsSemisimple (geometricFiber G s)) ↔
      GeometricallyConnected G.X.hom ∧ identityComponentSemisimpleLocus G = Set.univ := by
  constructor
  · rintro ⟨hG, hs⟩
    have hc := (isReductive_iff_geometricallyConnected_and_locus_eq_univ G).mp hG |>.1
    exact ⟨hc, (semisimple_geometricFibres_iff_locus_eq_univ G hc).mp hs⟩
  · rintro ⟨hc, hs⟩
    have hss := (semisimple_geometricFibres_iff_locus_eq_univ G hc).mpr hs
    exact ⟨⟨inferInstance, inferInstance,
      fun s => (hss s).isConnectedReductive.isPseudoReductive⟩, hss⟩

end Langlands.GroupScheme
