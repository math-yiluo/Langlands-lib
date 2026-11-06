import Langlands.CommutativeAlgebra.PointedEtaleLocalSections

/-! # Constructing pointed etale local sections of smooth morphisms -/

universe u

open CategoryTheory

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry Langlands.CommutativeAlgebra.PointedEtaleLocalSections

set_option backward.isDefEq.respectTransparency false in
/-- Extend a specified residue-field point over a pointed etale neighbourhood. -/
theorem exists_pointed_etale_section {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (s : S) (x₀ : Spec (S.residueField s) ⟶ X)
    (hx₀ : x₀ ≫ f = S.fromSpecResidueField s) :
    ∃ (U : Scheme.{u}) (p : U ⟶ S) (b : Spec (S.residueField s) ⟶ U) (a : U ⟶ X),
      Etale p ∧ b ≫ p = S.fromSpecResidueField s ∧ a ≫ f = p ∧ b ≫ a = x₀ := by
  classical
  let x : X := x₀ default
  have hfx : f x = s := by
    change (x₀ ≫ f) default = s
    rw [hx₀, Scheme.fromSpecResidueField_apply]
  obtain ⟨U, hU, V, hV, hxV, hle, -⟩ := Smooth.exists_isStandardSmooth f x
  have hsU : s ∈ U := hfx ▸ hle hxV
  let R := Γ(S, U)
  let A := Γ(X, V)
  let q : Spec R := hU.primeIdealOf ⟨s, hsU⟩
  have hq : hU.fromSpec q = s := hU.fromSpec_primeIdealOf ⟨s, hsU⟩
  let e₀ : S.residueField s ≅ (Spec R).residueField q :=
    (S.residueFieldCongr hq.symm) ≪≫ asIso (hU.fromSpec.residueFieldMap q)
  let e : S.residueField s ≅ CommRingCat.of q.asIdeal.ResidueField :=
    e₀ ≪≫ Scheme.Spec.residueFieldIso R q
  have hbase : Spec.map e.inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)) ≫ hU.fromSpec =
        S.fromSpecResidueField s := by
    dsimp only [e, Iso.trans_inv]
    rw [Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc]
    rw [← hU.fromSpec.SpecMap_residueFieldMap_fromSpecResidueField]
    dsimp only [e₀, Iso.trans_inv, asIso_inv]
    simp only [Spec.map_comp, Category.assoc, ← Spec.map_comp_assoc,
      IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    exact S.residueFieldCongr_fromSpecResidueField hq
  have hxr : Set.range x₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    have ht : t = default := Subsingleton.elim _ _
    rw [ht]
    exact hxV
  let xV := IsOpenImmersion.lift hV.fromSpec x₀ hxr
  have hxVfac : xV ≫ hV.fromSpec = x₀ := IsOpenImmersion.lift_fac ..
  let z : Spec (CommRingCat.of q.asIdeal.ResidueField) ⟶ Spec A := Spec.map e.hom ≫ xV
  let α := f.appLE U V hle
  have hz : z ≫ Spec.map α =
      Spec.map (CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField)) := by
    apply (cancel_mono hU.fromSpec).mp
    rw [Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hle]
    dsimp only [z]
    rw [Category.assoc, ← Category.assoc xV hV.fromSpec f, hxVfac, hx₀]
    rw [← hbase, ← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    simp
  let : Algebra R A := α.hom.toAlgebra
  have : Algebra.Smooth R A := RingHom.smooth_algebraMap.mp (f.smooth_appLE hU hV hle)
  let γ : A ⟶ CommRingCat.of q.asIdeal.ResidueField := Spec.preimage z
  have hγ : α ≫ γ = CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hz
  let φ : A →ₐ[R] q.asIdeal.ResidueField :=
    ⟨γ.hom, fun r => congrArg (fun h : R ⟶ CommRingCat.of q.asIdeal.ResidueField => h r) hγ⟩
  obtain ⟨R', _, _, hR', ψ, ρ, hfac⟩ := exists_etale_factor_of_smooth q.asIdeal φ
  let p : Spec (CommRingCat.of R') ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ hU.fromSpec
  let a : Spec (CommRingCat.of R') ⟶ X :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec
  let b : Spec (S.residueField s) ⟶ Spec (CommRingCat.of R') :=
    Spec.map e.inv ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom)
  refine ⟨Spec (CommRingCat.of R'), p, b, a, ?_, ?_, ?_, ?_⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hR')
    infer_instance
  · dsimp only [b, p]
    rw [Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom ρ.toRingHom)),
      ← Spec.map_comp]
    have hρ : CommRingCat.ofHom (algebraMap R R') ≫ CommRingCat.ofHom ρ.toRingHom =
        CommRingCat.ofHom (algebraMap R q.asIdeal.ResidueField) := by
      ext r
      exact ρ.commutes r
    rw [hρ]
    exact hbase
  · dsimp only [a, p]
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hle,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact ψ.commutes r
  · dsimp only [b, a]
    rw [Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom ρ.toRingHom)),
      ← Spec.map_comp]
    have hfacc : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom ρ.toRingHom = γ := by
      ext y
      exact congrArg (fun h : A →ₐ[R] q.asIdeal.ResidueField => h y) hfac
    rw [hfacc, Spec.map_preimage]
    dsimp only [z]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    simp [hxVfac]

/-- Actual pointed etale section data, including all structure and point equations. -/
structure PointedEtaleSectionData {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (x₀ : Spec (S.residueField s) ⟶ X) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  point : Spec (S.residueField s) ⟶ neighbourhood
  sectionMap : neighbourhood ⟶ X
  etale : Etale projection
  point_over : point ≫ projection = S.fromSpecResidueField s
  section_over : sectionMap ≫ f = projection
  recovers : point ≫ sectionMap = x₀

/-- Construct a pointed etale section through the prescribed rational point. -/
def pointedEtaleSection {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (s : S) (x₀ : Spec (S.residueField s) ⟶ X)
    (hx₀ : x₀ ≫ f = S.fromSpecResidueField s) : PointedEtaleSectionData f s x₀ :=
  Classical.choice <| by
    obtain ⟨U, p, b, a, hp, hb, ha, hx⟩ := exists_pointed_etale_section f s x₀ hx₀
    exact ⟨⟨U, p, b, a, hp, hb, ha, hx⟩⟩

end Langlands.AlgebraicGeometry
