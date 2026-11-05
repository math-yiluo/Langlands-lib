import Langlands.AlgebraicGeometry.FiniteSeparableNilradicalEtaleScheme

/-! # Prescribed generic extensions over arbitrary irreducible schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Actual data for the prescribed generic extension construction. -/
structure PrescribedGenericCoverData (Y : Scheme.{u}) (η : Y)
    (L : Type u) [Field L] [Algebra (Y.residueField η) L] where
  baseOpen : Y.Opens
  baseOpen_nonempty : (baseOpen : Set Y).Nonempty
  model : Scheme.{u}
  cover : model ⟶ baseOpen.toScheme
  affine : IsAffine model
  irreducible : IrreducibleSpace model
  surjective : Surjective cover
  finite : IsFinite cover
  etale : Etale cover
  generic : model
  isGenericPoint : IsGenericPoint generic Set.univ
  residueIso : Spec (CommRingCat.of L) ≅ Spec (model.residueField generic)
  triangle : residueIso.hom ≫ model.fromSpecResidueField generic ≫ cover ≫ baseOpen.ι =
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField η) L)) ≫
      Y.fromSpecResidueField η

namespace PrescribedGenericCoverData

set_option backward.isDefEq.respectTransparency false in
/-- An affine open chart identifies its ideal residue field with the original
scheme residue field, retaining the chosen equality of points. -/
def chartResidueFieldIso {Y : Scheme.{u}} (R : CommRingCat.{u})
    (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (p : Spec R) (η : Y) (h : f p = η) :
    CommRingCat.of p.asIdeal.ResidueField ≅ Y.residueField η :=
  (Scheme.Spec.residueFieldIso R p).symm ≪≫
    (asIso (f.residueFieldMap p)).symm ≪≫ Y.residueFieldCongr h

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem chartResidueFieldIso_triangle {Y : Scheme.{u}} (R : CommRingCat.{u})
    (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (p : Spec R) (η : Y) (h : f p = η) :
    Spec.map (chartResidueFieldIso R f p η h).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) ≫ f =
        Y.fromSpecResidueField η := by
  simp only [chartResidueFieldIso, Iso.trans_hom, Iso.symm_hom, Spec.map_comp,
    Category.assoc]
  rw [← Category.assoc (Spec.map (Scheme.Spec.residueFieldIso R p).inv),
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField p]
  simp only [← Spec.map_comp_assoc, asIso_inv, IsIso.hom_inv_id,
    Spec.map_id, Category.id_comp]
  exact Y.residueFieldCongr_fromSpecResidueField h

set_option backward.isDefEq.respectTransparency false in
/-- Construct a prescribed finite separable generic extension after shrinking an
arbitrary irreducible scheme, retaining the original residue-field action. -/
theorem nonempty {Y : Scheme.{u}} [IrreducibleSpace Y] (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (L : Type u) [Field L] [Algebra (Y.residueField η) L]
    [FiniteDimensional (Y.residueField η) L]
    [Algebra.IsSeparable (Y.residueField η) L] :
    Nonempty (PrescribedGenericCoverData Y η L) := by
  obtain ⟨R, f, hf, x, hx⟩ := Scheme.exists_Spec_apply_eq η
  let : IsOpenImmersion f := hf
  let : Nonempty (Spec R) := ⟨x⟩
  let : IrreducibleSpace (Spec R) := f.isOpenEmbedding.irreducibleSpace
  let : IrreducibleSpace (PrimeSpectrum R) := by
    change IrreducibleSpace (Spec R)
    infer_instance
  let : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  let p : PrimeSpectrum R := ⟨nilradical R, inferInstance⟩
  have hp : IsGenericPoint p Set.univ := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton]
    exact (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr Set.Subset.rfl
  have hfp : f p = η := by
    rw [← (genericPoint_spec (Spec R)).eq hp,
      genericPoint_eq_of_isOpenImmersion f]
    exact (genericPoint_spec Y).eq hη
  let e := (chartResidueFieldIso R f p η hfp).commRingCatIsoToRingEquiv
  let : Algebra (R ⧸ nilradical R) (Y.residueField η) :=
    (e.toRingHom.comp (algebraMap (R ⧸ nilradical R) p.asIdeal.ResidueField)).toAlgebra
  let : IsFractionRing (R ⧸ nilradical R) (Y.residueField η) :=
    IsFractionRing.of_algEquiv
      ({ e with commutes' := fun _ => rfl } :
        p.asIdeal.ResidueField ≃ₐ[R ⧸ nilradical R] Y.residueField η)
  let : Algebra R (Y.residueField η) :=
    ((algebraMap (R ⧸ nilradical R) (Y.residueField η)).comp
      (Ideal.Quotient.mk (nilradical R))).toAlgebra
  let : IsScalarTower R (R ⧸ nilradical R) (Y.residueField η) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (R ⧸ nilradical R) L :=
    ((algebraMap (Y.residueField η) L).comp
      (algebraMap (R ⧸ nilradical R) (Y.residueField η))).toAlgebra
  let : IsScalarTower (R ⧸ nilradical R) (Y.residueField η) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let d := Langlands.CommutativeAlgebra.finiteSeparableNilradicalEtaleModel
    R (Y.residueField η) L
  let j := d.baseOpen.ι ≫ f
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (d.baseOpen.ι ≫ f))
  let V : Y.Opens := j.opensRange
  let i : d.baseOpen.toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq j V.ι (by rw [Scheme.Opens.range_ι]; rfl)
  have hi : i.hom ≫ V.ι = d.baseOpen.ι ≫ f :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hV : (V : Set Y).Nonempty := by
    obtain ⟨z, hz⟩ := d.baseOpen_nonempty
    exact ⟨j ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩⟩
  refine ⟨{
    baseOpen := V
    baseOpen_nonempty := hV
    model := d.modelScheme
    cover := d.coverMap ≫ i.hom
    affine := inferInstance
    irreducible := inferInstance
    surjective := inferInstance
    finite := inferInstance
    etale := inferInstance
    generic := genericPoint d.modelScheme
    isGenericPoint := genericPoint_spec _
    residueIso := d.modelGenericResidueFieldIso
    triangle := ?_ }⟩
  calc
    _ = d.modelGenericResidueFieldIso.hom ≫
        d.modelScheme.fromSpecResidueField (genericPoint d.modelScheme) ≫
          d.coverMap ≫ d.baseOpen.ι ≫ f := by
      simp only [Category.assoc]
      rw [hi]
    _ = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField η) L)) ≫
        Langlands.CommutativeAlgebra.FiniteSeparableNilradicalModel.originalGenericBaseMap
          (R := R) (K := Y.residueField η) ≫ f :=
      d.modelGenericResidueFieldIso_hom_coverMap_ι_assoc f
    _ = _ := by
      congr 1
      change Spec.map ((CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) ≫
        (chartResidueFieldIso R f p η hfp).hom) ≫ f = _
      rw [Spec.map_comp, Category.assoc]
      exact chartResidueFieldIso_triangle R f p η hfp

/-- Choose the actual cover constructed by `nonempty`. -/
def construct {Y : Scheme.{u}} [IrreducibleSpace Y] (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (L : Type u) [Field L] [Algebra (Y.residueField η) L]
    [FiniteDimensional (Y.residueField η) L]
    [Algebra.IsSeparable (Y.residueField η) L] :
    PrescribedGenericCoverData Y η L :=
  Classical.choice (nonempty η hη L)

end PrescribedGenericCoverData

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
