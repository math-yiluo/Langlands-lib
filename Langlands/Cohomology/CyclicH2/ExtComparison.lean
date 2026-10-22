import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

open CategoryTheory Opposite

namespace Langlands.Cohomology.CyclicH2

universe u

section Unop

variable {V : Type*} [Category* V] [Abelian V] {ι : Type*} {c : ComplexShape ι}

lemma homologyUnop_hom_naturality {K L : HomologicalComplex Vᵒᵖ c} (ψ : K ⟶ L) (i : ι) :
    (L.homologyUnop i).hom ≫ (HomologicalComplex.homologyMap ψ i).unop =
      HomologicalComplex.homologyMap ((HomologicalComplex.unopFunctor V c).map ψ.op) i ≫
        (K.homologyUnop i).hom := by
  have h := HomologicalComplex.homologyOp_hom_naturality
    ((HomologicalComplex.unopFunctor V c).map ψ.op) i
  exact congrArg Quiver.Hom.unop h

end Unop

variable {k G : Type u} [CommRing k] [Group G]

/-- Precomposition with a chain map, as a cochain map between the `Hom(-, A)` complexes. -/
noncomputable def precompMap (A : Rep k G) {X Y : ChainComplex (Rep k G) ℕ} (φ : X ⟶ Y) :
    Y.linearYonedaObj k A ⟶ X.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map φ).op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma groupCohomologyIso_hom_eq (A : Rep k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) (φ : P.complex ⟶ Rep.barComplex k G)
    (hφ : φ.f 0 ≫ (Rep.barResolution k G).π.f 0 = P.π.f 0) :
    (groupCohomologyIso A n P).hom =
      HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso A).hom ≫ precompMap A φ) n := by
  change HomologicalComplex.homologyMap
      (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      (Rep.barResolution.extIso k G A n).inv ≫ (P.isoExt n A).hom = _
  have nat := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P
    (Rep.barResolution k G) φ (hφ.trans (Category.comp_id _).symm) (((linearYoneda k (Rep k G)).obj A).rightOp) n
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at nat
  have key : (P.isoLeftDerivedObj (((linearYoneda k (Rep k G)).obj A).rightOp) n).inv ≫
      ((Rep.barResolution k G).isoLeftDerivedObj
        (((linearYoneda k (Rep k G)).obj A).rightOp) n).hom =
      HomologicalComplex.homologyMap
        ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map φ) n := by
    rw [nat, Iso.inv_hom_id_assoc]
    rfl
  simp only [Rep.barResolution.extIso,
    ProjectiveResolution.isoExt, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Iso.unop_hom, Iso.unop_inv, Category.assoc,
    HomologicalComplex.homologyMap_comp]
  congr 1
  let F := ((linearYoneda k (Rep k G)).obj A).rightOp
  let ψ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ
  have h := congrArg (fun t =>
      (((F.mapHomologicalComplex _).obj (Rep.barResolution k G).complex).homologyUnop n).hom ≫
      t ≫ (((F.mapHomologicalComplex _).obj P.complex).homologyUnop n).inv)
    (congrArg Quiver.Hom.unop key)
  have h' := congrArg (fun t =>
      t ≫ (((F.mapHomologicalComplex _).obj P.complex).homologyUnop n).inv)
    (homologyUnop_hom_naturality ψ n)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  simp only [unop_comp, Category.assoc] at h
  exact h.trans h'

end Langlands.Cohomology.CyclicH2
