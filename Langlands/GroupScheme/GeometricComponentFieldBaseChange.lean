import Langlands.GroupScheme.GeometricComponentEmbeddings

/-! # Geometric components under an extension of the base field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local irreducible] Langlands.GroupScheme.GaloisPointComparison.towerBaseChangeIso

namespace Langlands.GroupScheme.GaloisPointComparison

section Tower

variable (k K M : Type u) [Field k] [Field K] [Field M]
  [Algebra k K] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The actual tower comparison intertwines coefficient conjugation over K
with conjugation over k by the same automorphism. -/
theorem towerBaseChangeIso_conjugate (τ : M ≃ₐ[K] M)
    (x : rationalPoints (baseChanged K M (baseChanged k K H))) :
    rationalPoints.map (towerBaseChangeIso k K M H).hom
        (rationalConjugate K M (baseChanged k K H) τ x) =
      rationalConjugate k M H (τ.restrictScalars k)
        (rationalPoints.map (towerBaseChangeIso k K M H).hom x) := by
  apply (baseChangeCoeffEquiv k M H).injective
  rw [baseChangeCoeffEquiv_towerBaseChangeIso,
    baseChangeCoeffEquiv_rationalConjugate,
    baseChangeCoeffEquiv_rationalConjugate,
    baseChangeCoeffEquiv_towerBaseChangeIso]
  exact coefficientBaseChangeEquiv_conjugate k K M H τ _

end Tower

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

section Tower

variable (k K M : Type u) [Field k] [Field K] [Field M]
  [Algebra k K] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
  [IsAlgClosed M]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- On all actual components the tower comparison intertwines the two
coefficient actions of an automorphism fixing K. -/
theorem allComponentIso_tower_conjugate (τ : M ≃ₐ[K] M)
    (c : AlgebraicallyClosedComponents (baseChanged K M (baseChanged k K H))) :
    allComponentIso (towerBaseChangeIso k K M H)
        (allComponentConjugate K M (baseChanged k K H) τ c) =
      allComponentConjugate k M H (τ.restrictScalars k)
        (allComponentIso (towerBaseChangeIso k K M H) c) := by
  obtain ⟨x, rfl⟩ :=
    allComponentOfPoint_surjective (baseChanged K M (baseChanged k K H)) c
  simp only [allComponentConjugate_ofPoint, allComponentIso_apply,
    allComponentMap_ofPoint]
  rw [towerBaseChangeIso_conjugate]

end Tower

section IsomorphismPoint

variable {F : Type u} [Field F] [IsAlgClosed F]
  {G G' : GroupScheme (Spec (CommRingCat.of F))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [Smooth G'.X.hom] [IsAffineHom G'.X.hom]

private theorem componentIso_symm_ofPoint (i : G ≅ G') (x : rationalPoints G') :
    (allComponentIso i).symm (allComponentOfPoint G' x) =
      allComponentOfPoint G (rationalPoints.map i.inv x) := by
  change allComponentMap i.inv (allComponentOfPoint G' x) = _
  exact allComponentMap_ofPoint i.inv x

end IsomorphismPoint

section TowerComparisonData

variable (k K M : Type u) [Field k] [Field K] [Field M]
  [Algebra k K] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
  [IsAlgClosed M]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

omit [IsAlgClosed M] [Smooth H.X.hom] [IsAffineHom H.X.hom] in
private theorem inverse_coefficient_of_iso
    (i : baseChanged K M (baseChanged k K H) ≅ baseChanged k M H)
    (hi : ∀ y : rationalPoints (baseChanged K M (baseChanged k K H)),
      baseChangeCoeffEquiv k M H (rationalPoints.map i.hom y) =
        coefficientBaseChangeEquiv k K M H
          (baseChangeCoeffEquiv K M (baseChanged k K H) y))
    (x : rationalPoints (baseChanged k M H)) :
    coefficientBaseChangeEquiv k K M H
        (baseChangeCoeffEquiv K M (baseChanged k K H) (rationalPoints.map i.inv x)) =
      baseChangeCoeffEquiv k M H x := by
  rw [← hi]
  apply congrArg (baseChangeCoeffEquiv k M H)
  change (x ≫ i.inv.hom.hom) ≫ i.hom.hom.hom = x
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

private structure TowerComponentData where
  inverse_section : rationalPoints (baseChanged k M H) →*
    rationalPoints (baseChanged K M (baseChanged k K H))
  equiv : AlgebraicallyClosedComponents (baseChanged K M (baseChanged k K H)) ≃*
    AlgebraicallyClosedComponents (baseChanged k M H)
  inverse_point (x : rationalPoints (baseChanged k M H)) :
    equiv.symm (allComponentOfPoint _ x) =
      allComponentOfPoint _ (inverse_section x)
  inverse_coefficient (x : rationalPoints (baseChanged k M H)) :
    coefficientBaseChangeEquiv k K M H
        (baseChangeCoeffEquiv K M (baseChanged k K H) (inverse_section x)) =
      baseChangeCoeffEquiv k M H x
  conjugate (τ : M ≃ₐ[K] M)
    (c : AlgebraicallyClosedComponents (baseChanged K M (baseChanged k K H))) :
    equiv (allComponentConjugate K M (baseChanged k K H) τ c) =
      allComponentConjugate k M H (τ.restrictScalars k) (equiv c)

-- Name the component equivalence and its laws while all three fields are
-- abstract. Specialization at an algebraic closure uses only these projections.
private opaque towerComponentData : TowerComponentData k K M H := by
  refine ⟨rationalPoints.map (towerBaseChangeIso k K M H).inv,
    allComponentIso (towerBaseChangeIso k K M H),
    componentIso_symm_ofPoint (towerBaseChangeIso k K M H),
    inverse_coefficient_of_iso k K M H (towerBaseChangeIso k K M H)
      (baseChangeCoeffEquiv_towerBaseChangeIso k K M H),
    allComponentIso_tower_conjugate k K M H⟩

end TowerComparisonData

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

private structure BaseChangeComponentData where
  section_hom : rationalPoints (baseChanged k (AlgebraicClosure k) H) →*
    rationalPoints (baseChanged K (AlgebraicClosure K) (baseChanged k K H))
  equiv : GeometricComponents k H ≃* GeometricComponents K (baseChanged k K H)
  point_formula (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    equiv (geometricComponentOfPoint k H x) =
      geometricComponentOfPoint K (baseChanged k K H) (section_hom x)
  coefficient_formula (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    coefficientBaseChangeEquiv k K (AlgebraicClosure K) H
        (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H) (section_hom x)) =
      GaloisPoint.relativeExtend k (AlgebraicClosure k) (AlgebraicClosure K) H
        (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)
  smul_formula
    (σ : Field.absoluteGaloisGroup k) (τ : Field.absoluteGaloisGroup K)
    (h : ∀ a : AlgebraicClosure k,
      AlgEquiv.toAlgHom τ (algebraMap (AlgebraicClosure k) (AlgebraicClosure K) a) =
        algebraMap (AlgebraicClosure k) (AlgebraicClosure K) (AlgEquiv.toAlgHom σ a))
    (c : GeometricComponents k H) :
    equiv (σ • c) = τ • equiv c

private opaque fieldBaseChangeComponentData : BaseChangeComponentData k K H := by
  let t := towerComponentData k K (AlgebraicClosure K) H
  refine ⟨t.inverse_section.comp
    (fieldEmbeddingSectionHom k (AlgebraicClosure k) (AlgebraicClosure K) H),
    (geometricComponentEmbeddingEquiv k (AlgebraicClosure K) H).trans
      t.equiv.symm, ?_, ?_, ?_⟩
  · intro x
    exact (congrArg t.equiv.symm
      (geometricComponentEmbeddingEquiv_ofPoint k (AlgebraicClosure K) H x)).trans
        (t.inverse_point _)
  · intro x
    exact (t.inverse_coefficient _).trans
      (baseChangeCoeffEquiv_fieldEmbeddingSectionHom k (AlgebraicClosure k)
        (AlgebraicClosure K) H x)
  · intro σ τ h c
    change t.equiv.symm
        (geometricComponentEmbeddingEquiv k (AlgebraicClosure K) H (σ • c)) =
      allComponentConjugate K (AlgebraicClosure K) (baseChanged k K H) τ
        (t.equiv.symm (geometricComponentEmbeddingEquiv k (AlgebraicClosure K) H c))
    apply t.equiv.injective
    rw [MulEquiv.apply_symm_apply]
    have ht := t.conjugate τ
      (t.equiv.symm (geometricComponentEmbeddingEquiv k (AlgebraicClosure K) H c))
    rw [MulEquiv.apply_symm_apply] at ht
    exact (geometricComponentEmbeddingEquiv_smul k (AlgebraicClosure K) H σ
      (AlgEquiv.restrictScalars k τ) h c).trans ht.symm

/-- Extend an actual closure-valued section through the specified closure
embedding and the inverse pullback-tower comparison. -/
def geometricComponentBaseChangeSectionHom :
    rationalPoints (baseChanged k (AlgebraicClosure k) H) →*
      rationalPoints (baseChanged K (AlgebraicClosure K) (baseChanged k K H)) :=
  (fieldBaseChangeComponentData k K H).section_hom

/-- On original coefficient points, the actual section comparison is extension
along the specified embedding of chosen algebraic closures. -/
theorem geometricComponentBaseChangeSectionHom_coefficient
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    coefficientBaseChangeEquiv k K (AlgebraicClosure K) H
        (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H)
          (geometricComponentBaseChangeSectionHom k K H x)) =
      GaloisPoint.relativeExtend k (AlgebraicClosure k) (AlgebraicClosure K) H
        (baseChangeCoeffEquiv k (AlgebraicClosure k) H x) :=
  (fieldBaseChangeComponentData k K H).coefficient_formula x

/-- Compare the chosen geometric components before and after base-field
extension, along the specified compatible embedding of chosen closures. -/
def geometricComponentBaseChangeEquiv :
    GeometricComponents k H ≃* GeometricComponents K (baseChanged k K H) :=
  (fieldBaseChangeComponentData k K H).equiv

/-- The comparison respects the actual connected-component quotient topologies. -/
def geometricComponentBaseChangeHomeomorph :
    GeometricComponents k H ≃ₜ GeometricComponents K (baseChanged k K H) where
  toEquiv := (geometricComponentBaseChangeEquiv k K H).toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp]
theorem geometricComponentBaseChangeHomeomorph_apply (c : GeometricComponents k H) :
    geometricComponentBaseChangeHomeomorph k K H c =
      geometricComponentBaseChangeEquiv k K H c :=
  rfl

/-- On actual sections, extend the closure coefficient and then use the inverse
tower isomorphism to reach the iterated pullback over K. -/
@[simp]
theorem geometricComponentBaseChangeEquiv_ofPoint
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentBaseChangeEquiv k K H (geometricComponentOfPoint k H x) =
      geometricComponentOfPoint K (baseChanged k K H)
        (geometricComponentBaseChangeSectionHom k K H x) :=
  (fieldBaseChangeComponentData k K H).point_formula x

/-- Compatible absolute Galois automorphisms intertwine the two actual actions;
the compatibility with the specified closure embedding is explicit. -/
theorem geometricComponentBaseChangeEquiv_smul
    (σ : Field.absoluteGaloisGroup k) (τ : Field.absoluteGaloisGroup K)
    (h : ∀ a : AlgebraicClosure k,
      AlgEquiv.toAlgHom τ (algebraMap (AlgebraicClosure k) (AlgebraicClosure K) a) =
        algebraMap (AlgebraicClosure k) (AlgebraicClosure K) (AlgEquiv.toAlgHom σ a))
    (c : GeometricComponents k H) :
    geometricComponentBaseChangeEquiv k K H (σ • c) =
      τ • geometricComponentBaseChangeEquiv k K H c :=
  (fieldBaseChangeComponentData k K H).smul_formula σ τ h c

end FieldExtension

end Langlands.GroupScheme.IdentityComponent
