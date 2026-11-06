import Langlands.CommutativeAlgebra.EtaleResidueExtensions

/-! # Realizing finite separable residue extensions by etale neighbourhoods -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- An etale neighbourhood realizes any specified finite separable extension
of the actual residue field, with its original scalar structure. -/
theorem exists_etale_residue_extension (S : Scheme.{u}) (s : S) (K : Type u) [Field K]
    [Algebra (S.residueField s) K] [FiniteDimensional (S.residueField s) K]
    [Algebra.IsSeparable (S.residueField s) K] :
    ∃ (U : Scheme.{u}) (p : U ⟶ S) (u : U) (e : U.residueField u ≅ CommRingCat.of K),
      Etale p ∧ p u = s ∧
      Spec.map e.hom ≫ U.fromSpecResidueField u ≫ p =
        Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
          S.fromSpecResidueField s := by
  classical
  obtain ⟨R, j, _, q, hq⟩ := Scheme.exists_Spec_apply_eq s
  have hq' : j q = s := hq
  let e₀ : S.residueField s ≅ (Spec R).residueField q :=
    S.residueFieldCongr hq'.symm ≪≫ asIso (j.residueFieldMap q)
  let e : S.residueField s ≅ CommRingCat.of q.asIdeal.ResidueField :=
    e₀ ≪≫ Scheme.Spec.residueFieldIso R q
  let κ := q.asIdeal.ResidueField
  have hbase : Spec.map e.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R κ)) ≫ j = S.fromSpecResidueField s := by
    dsimp only [e, Iso.trans_inv]
    rw [Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc]
    rw [← j.SpecMap_residueFieldMap_fromSpecResidueField]
    dsimp only [e₀, Iso.trans_inv, asIso_inv]
    simp only [Spec.map_comp, Category.assoc, ← Spec.map_comp_assoc,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    exact S.residueFieldCongr_fromSpecResidueField hq'
  let : Algebra κ K := ((algebraMap (S.residueField s) K).comp e.inv.hom).toAlgebra
  have hscalar : (algebraMap κ K).comp e.hom.hom = algebraMap (S.residueField s) K := by
    ext r
    change algebraMap (S.residueField s) K (e.inv (e.hom r)) = _
    simp
  have : FiniteDimensional κ K := Module.Finite.of_equiv_equiv
    e.commRingCatIsoToRingEquiv (RingEquiv.refl K) hscalar
  have : Algebra.IsSeparable κ K := Algebra.IsSeparable.of_equiv_equiv
    e.commRingCatIsoToRingEquiv (RingEquiv.refl K) hscalar
  let : Algebra R K := ((algebraMap κ K).comp (algebraMap R κ)).toAlgebra
  have : IsScalarTower R κ K := .of_algebraMap_eq fun _ => rfl
  obtain ⟨A, _, _, hA, q', e', hp, he⟩ :=
    Langlands.CommutativeAlgebra.exists_etale_residue_extension R q.asIdeal K
  let U := Spec (CommRingCat.of A)
  let p : U ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ j
  let ε : U.residueField q' ≅ CommRingCat.of K :=
    Scheme.Spec.residueFieldIso (CommRingCat.of A) q' ≪≫ e'.toCommRingCatIso
  let ρ : A →+* K := e'.toRingHom.comp (algebraMap A q'.asIdeal.ResidueField)
  have hρ : (CommRingCat.ofHom (algebraMap R A)) ≫ CommRingCat.ofHom ρ =
      CommRingCat.ofHom (algebraMap R K) := by
    ext r
    exact he r
  have hb : Spec.map ε.hom ≫ U.fromSpecResidueField q' = Spec.map (CommRingCat.ofHom ρ) := by
    have hc : Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) q').hom ≫
        U.fromSpecResidueField q' =
        Spec.map (CommRingCat.ofHom (algebraMap A q'.asIdeal.ResidueField)) := by
      apply (cancel_epi (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) q').inv)).mp
      rw [← Category.assoc, ← Spec.map_comp]
      simp only [Iso.hom_inv_id, Spec.map_id, Category.id_comp]
      exact (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _).symm
    dsimp only [ε, Iso.trans_hom]
    rw [Spec.map_comp, Category.assoc, hc, ← Spec.map_comp]
    rfl
  refine ⟨U, p, q', ε, ?_, ?_, ?_⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hA)
    infer_instance
  · have hpt : Spec.map (CommRingCat.ofHom (algebraMap R A)) q' = q := PrimeSpectrum.ext hp
    change j (Spec.map (CommRingCat.ofHom (algebraMap R A)) q') = s
    rw [hpt]
    exact hq'
  · rw [← Category.assoc, hb]
    dsimp only [p]
    rw [← Category.assoc, ← Spec.map_comp, hρ]
    change Spec.map (CommRingCat.ofHom
      (((algebraMap (S.residueField s) K).comp e.inv.hom).comp (algebraMap R κ))) ≫ j = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, Category.assoc]
    rw [Category.assoc]
    change Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
      (Spec.map e.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap R κ)) ≫ j) = _
    rw [hbase]

/-- Actual etale neighbourhood and its specified finite separable residue field. -/
structure EtaleResidueExtensionData (S : Scheme.{u}) (s : S) (K : Type u) [Field K]
    [Algebra (S.residueField s) K] where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  point : neighbourhood
  residueIso : neighbourhood.residueField point ≅ CommRingCat.of K
  etale : Etale projection
  point_over : projection point = s
  residue_over : Spec.map residueIso.hom ≫ neighbourhood.fromSpecResidueField point ≫ projection =
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫ S.fromSpecResidueField s

/-- Construct an etale neighbourhood realizing the prescribed residue extension. -/
def etaleResidueExtension (S : Scheme.{u}) (s : S) (K : Type u) [Field K]
    [Algebra (S.residueField s) K] [FiniteDimensional (S.residueField s) K]
    [Algebra.IsSeparable (S.residueField s) K] : EtaleResidueExtensionData S s K :=
  Classical.choice <| by
    obtain ⟨U, p, u, e, hp, hu, he⟩ := exists_etale_residue_extension S s K
    exact ⟨⟨U, p, u, e, hp, hu, he⟩⟩

end Langlands.AlgebraicGeometry
