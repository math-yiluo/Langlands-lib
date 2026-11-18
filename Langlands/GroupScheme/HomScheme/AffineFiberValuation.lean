import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.SmoothDvrGenericAffinenessProof
import Langlands.GroupScheme.HomScheme.AdicDiagonalizable
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof

/-! # Actual base changes of groups with affine residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

private theorem isAffineHom_of_overIso {S : Scheme.{u}} {X Y : Over S}
    (e : X ≅ Y) (hY : IsAffineHom Y.hom) : IsAffineHom X.hom := by
  let : IsIso e.hom.left := (inferInstance : IsIso ((Over.forget S).mapIso e).hom)
  let : IsAffineHom Y.hom := hY
  have hcomp : IsAffineHom (e.hom.left ≫ Y.hom) := inferInstance
  exact Over.w e.hom ▸ hcomp

variable {S T : Scheme.{u}} (G : GroupScheme S)

/-- Each actual residue-field fibre of `G` is affine over its residue field. -/
def HasAffineResidueFibers : Prop :=
  ∀ s : S, IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom

/-- Affineness of the actual residue fibres gives affineness over any field-valued point. -/
theorem isAffineHom_fieldPullback_of_residueFibers
    (h : HasAffineResidueFibers G)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom := by
  let s := b (IsLocalRing.closedPoint k)
  let kMap := S.descResidueField (Scheme.stalkClosedPointTo b)
  let f := Spec.map kMap
  have w : f ≫ S.fromSpecResidueField s = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S b
  let F := RelativeIdentityComponent.residueFiber G s
  let e := (Grp.forget _).mapIso
    (Descent.pullbackComparison (S.fromSpecResidueField s) f b w G).symm
  let : IsAffineHom F.X.hom := h s
  have ha : IsAffineHom ((baseChange f).obj F).X.hom := by
    change IsAffineHom (pullback.snd F.X.hom f)
    infer_instance
  exact isAffineHom_of_overIso e ha

/-- Affine residue fibres are preserved by every base change. -/
theorem HasAffineResidueFibers.baseChange {G : GroupScheme S}
    (h : HasAffineResidueFibers G) (b : T ⟶ S) :
    HasAffineResidueFibers ((GroupScheme.baseChange b).obj G) := by
  intro t
  let p := T.fromSpecResidueField t
  let e := (Grp.forget _).mapIso (baseChangeCompIso b p G).symm
  exact isAffineHom_of_overIso e (G.isAffineHom_fieldPullback_of_residueFibers h (p ≫ b))

/-- Over a discrete valuation ring, the field-pullback hypothesis on a smooth,
separated quasi-compact group gives affineness of the actual pullback. -/
theorem isAffineHom_dvrPullback_of_residueFibers
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (h : HasAffineResidueFibers G)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom := by
  let η := Spec.algebraMap R (FractionRing R)
  let e := (Grp.forget _).mapIso (baseChangeCompIso b η G).symm
  let B := (baseChange b).obj G
  have hSmooth : Smooth B.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hQuasiCompact : QuasiCompact B.X.hom := by
    change QuasiCompact (pullback.snd G.X.hom b)
    infer_instance
  have hSeparated : IsSeparated B.X.hom := by
    change IsSeparated (pullback.snd G.X.hom b)
    infer_instance
  exact smoothDvrGenericAffineness R (FractionRing R) B hSmooth hQuasiCompact hSeparated
    (isAffineHom_of_overIso e (G.isAffineHom_fieldPullback_of_residueFibers h (η ≫ b)))

namespace HomScheme.Adic

/-- Compatible adic homomorphisms out of a diagonalizable group over a complete
DVR algebraize uniquely after pullback of a group with affine residue fibres. -/
theorem restrict_bijective_dvrPullback_of_affineResidueFibers
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (h : HasAffineResidueFibers G)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (I : Ideal R) [IsAdicComplete I R] (b : Spec (CommRingCat.of R) ⟶ S)
    (H : GroupScheme (Spec (CommRingCat.of R)))
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) :
    Function.Bijective (System.restrict I H ((baseChange b).obj G)) := by
  let : IsAffineHom ((baseChange b).obj G).X.hom := G.isAffineHom_dvrPullback_of_residueFibers h b
  exact AdicDiagonalizable.restrict_bijective_of_isDiagonalizable I H _ hH

end HomScheme.Adic

namespace TorusSubgroupModuli

/-- The actual base change to a DVR of a smooth separated quasi-compact group
with affine residue fibres has a smooth universal closed torus family. -/
theorem smoothTorusSubgroupRepresentability_dvrPullback
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (h : HasAffineResidueFibers G)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ S) :
    ∃ (M : Over (Spec (CommRingCat.of R))) (K : GroupScheme M.left)
      (j : K ⟶ (baseChange M.hom).obj ((baseChange b).obj G)),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧ IsUniversal j ∧ Smooth M.hom := by
  let : Smooth ((baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom ((baseChange b).obj G).X.hom := G.isAffineHom_dvrPullback_of_residueFibers h b
  exact smoothTorusSubgroupRepresentability _ _

end TorusSubgroupModuli

end Langlands.GroupScheme
