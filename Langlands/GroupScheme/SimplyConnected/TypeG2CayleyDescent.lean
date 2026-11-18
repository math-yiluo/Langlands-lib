import Langlands.GroupScheme.Composition.CayleyGaloisTwist
import Langlands.LinearAlgebra.GeneralLinearGaloisFixedBasis
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.Rational.FiniteGaloisOverlapDiscrepancy
import Langlands.GroupScheme.LocalGroupIsoOverlap
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.CocycleRefinement
import Langlands.GroupScheme.BaseChangeReflection

/-! # Inner forms of the split Cayley automorphism group are Cayley automorphism groups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

/-- The points of the automorphism group scheme on a test scheme `T` are the automorphism
matrices with coefficients in the global sections of `T`. -/
def points (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ c.automorphismGroup.X) ≃*
      c.automorphismSubgroup
        (algebraMap (CommRingCat.of K) ((algΓ (CommRingCat.of K)).obj T).unop) :=
  Corepresented.pointsEquiv _ (Corepresented.cutCorepresentableBy c.isCutOutBy_automorphismIdeal) T

theorem points_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (y : T ⟶ c.automorphismGroup.X) :
    ((c.points T' (a ≫ y) : GL (Fin 8) ((algΓ (CommRingCat.of K)).obj T').unop)) =
      GeneralLinearGroup.map a.left.appTop.hom
        (c.points T y : GL (Fin 8) ((algΓ (CommRingCat.of K)).obj T).unop) :=
  congrArg Subtype.val (Corepresented.pointsEquiv_naturality _ _ a y)

end CayleyDatum

namespace TypeG2CayleyDescent

open SpecialLinearInnerForm CayleyGaloisTwist

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- Points through a point of `Spec L`: restriction along `s` applies the scalar map of `s`
to the matrix over `L`. -/
theorem points_comp (c : CayleyDatum K) {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K L) (x : ringTest K L ⟶ c.automorphismGroup.X) :
    ((c.points V (s ≫ x) : GL (Fin 8) ((algΓ (CommRingCat.of K)).obj V).unop)) =
      GeneralLinearGroup.map (pointScalars s)
        (GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
          (c.points (ringTest K L) x :
            GL (Fin 8) ((algΓ (CommRingCat.of K)).obj (ringTest K L)).unop)) := by
  rw [c.points_naturality]
  have h : s.left.appTop.hom =
      (pointScalars s).comp (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom := by
    rw [pointScalars, ← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [h]
  rfl

/-- The scalar map of the identity point is the inverse global-section isomorphism. -/
theorem pointScalars_id :
    pointScalars (𝟙 (ringTest K L)) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom := by
  rw [pointScalars]
  rfl

theorem gammaSpec_comp_algebraMap :
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp
        (algebraMap (CommRingCat.of K) ((algΓ (CommRingCat.of K)).obj (ringTest K L)).unop) =
      algebraMap K L := by
  have h1 := pointScalars_comp_algebraMap (𝟙 (ringTest K L))
  rw [pointScalars_id] at h1
  change _ = algebraMap K L
  rw [← h1, ← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
    RingHom.id_comp]

variable (K) in
/-- The automorphism group scheme of the split Cayley datum. -/
abbrev splitGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  (CayleyDatum.split K).automorphismGroup

section GaloisValues

variable (ξ : Cocycle (splitGroup K) (ringTest K L))

/-- The Galois values `ξ(1, σ)` of a cocycle on `Spec L`. -/
def galoisValue (σ : L ≃ₐ[K] L) : ringTest K L ⟶ (splitGroup K).X :=
  ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom)

theorem galoisValue_mul (σ τ : L ≃ₐ[K] L) :
    galoisValue ξ (σ * τ) =
      galoisValue ξ σ * (ringTestMap K σ.toAlgHom ≫ galoisValue ξ τ) := by
  have h : ringTestMap K (σ * τ).toAlgHom =
      ringTestMap K σ.toAlgHom ≫ ringTestMap K τ.toAlgHom := by
    rw [← ringTestMap_comp]
    rfl
  have hc := ξ.cocycle (𝟙 _) (ringTestMap K σ.toAlgHom)
    (ringTestMap K σ.toAlgHom ≫ ringTestMap K τ.toAlgHom)
  have hn := ξ.naturality (ringTestMap K σ.toAlgHom) (𝟙 _) (ringTestMap K τ.toAlgHom)
  rw [Category.comp_id] at hn
  rw [galoisValue, galoisValue, galoisValue, h]
  exact hc.trans (congrArg (fun z => ξ.toFun (𝟙 _) (ringTestMap K σ.toAlgHom) * z) hn)

/-- The Galois value at `σ` as an invertible matrix over `L`. -/
def galoisMatrix (σ : L ≃ₐ[K] L) : GL (Fin 8) L :=
  GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
    ((CayleyDatum.split K).points (ringTest K L) (galoisValue ξ σ) :
      GL (Fin 8) ((algΓ (CommRingCat.of K)).obj (ringTest K L)).unop)

theorem galoisMatrix_isAutomorphismMatrix (σ : L ≃ₐ[K] L) :
    (CayleyDatum.split K).IsAutomorphismMatrix (algebraMap K L) (galoisMatrix ξ σ) := by
  have h := CayleyDatum.IsAutomorphismMatrix.map (CayleyDatum.split K) _
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom
    ((CayleyDatum.split K).points (ringTest K L) (galoisValue ξ σ)).2
  rw [gammaSpec_comp_algebraMap] at h
  exact h

theorem galoisMatrix_mul (σ τ : L ≃ₐ[K] L) :
    galoisMatrix ξ (σ * τ) =
      galoisMatrix ξ σ * GeneralLinearGroup.map (σ : L →+* L) (galoisMatrix ξ τ) := by
  have h1 := points_comp (CayleyDatum.split K) (ringTestMap K σ.toAlgHom) (galoisValue ξ τ)
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp
      (pointScalars (ringTestMap K σ.toAlgHom)) = (σ : L →+* L) := by
    have h := pointScalars_comp_ringTestMap (𝟙 (ringTest K L)) σ
    rw [Category.id_comp, pointScalars_id] at h
    rw [h, ← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
      RingHom.id_comp]
  rw [galoisMatrix, galoisValue_mul, map_mul, Subgroup.coe_mul, map_mul, h1, galoisMatrix]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply]
  exact RingHom.congr_fun h2 _

end GaloisValues

section Chart

variable [FiniteDimensional K L] [IsGalois K L] {P : GL (Fin 8) L} (hP : IsTwist (K := K) P)

/-- The chart over a point `s` of `Spec L`: conjugate the split automorphism matrix by the
image of `P⁻¹`. -/
def chartPoints {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L) :
    (V ⟶ (splitGroup K).X) ≃* (V ⟶ (datum hP).automorphismGroup.X) :=
  ((CayleyDatum.split K).points V).trans
    ((MulEquiv.subgroupCongr (congrArg (CayleyDatum.split K).automorphismSubgroup
        (pointScalars_comp_algebraMap s).symm)).trans
      ((conjEquiv hP (pointScalars s)).symm.trans
        ((MulEquiv.subgroupCongr (congrArg (datum hP).automorphismSubgroup
            (pointScalars_comp_algebraMap s))).trans
          ((datum hP).points V).symm)))

theorem chartPoints_val {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (g : V ⟶ (splitGroup K).X) :
    (((datum hP).points V (chartPoints hP s g) :
        GL (Fin 8) ((algΓ (CommRingCat.of K)).obj V).unop)) =
      (GeneralLinearGroup.map (pointScalars s) P)⁻¹ *
        ((CayleyDatum.split K).points V g : GL (Fin 8) ((algΓ (CommRingCat.of K)).obj V).unop) *
          GeneralLinearGroup.map (pointScalars s) P := by
  simp only [chartPoints, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

/-- The charts as local isomorphisms over `Spec L`. -/
def chartLocalIso :
    LocalGroupIso (splitGroup K) (datum hP).automorphismGroup (ringTest K L) where
  toFun s := chartPoints hP s
  naturality t s g := by
    apply ((datum hP).points _).injective
    apply Subtype.ext
    rw [CayleyDatum.points_naturality, chartPoints_val, chartPoints_val,
      CayleyDatum.points_naturality, pointScalars_comp, GeneralLinearGroup.map_comp,
      MonoidHom.comp_apply, map_mul, map_mul, map_inv]
    rfl

theorem chartPoints_galois (hq : IsAdjointQuotient (𝟙 (splitGroup K)))
    (ξ : Cocycle (splitGroup K) (ringTest K L))
    (hgP : ∀ σ, galoisMatrix ξ σ * GeneralLinearGroup.map (σ : L →+* L) P = P)
    (σ : L ≃ₐ[K] L) {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K L)
    (g : V ⟶ (splitGroup K).X) :
    chartPoints hP s (hq.innerAction.act (s ≫ galoisValue ξ σ) g) =
      chartPoints hP (s ≫ ringTestMap K σ.toAlgHom) g := by
  have hlift := hq.innerAction_act_lift (s ≫ galoisValue ξ σ) g
  simp only [Grp.id_hom_hom, Category.comp_id] at hlift
  rw [hlift]
  apply ((datum hP).points V).injective
  apply Subtype.ext
  rw [chartPoints_val, chartPoints_val, map_mul, map_mul, map_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, points_comp, pointScalars_comp_ringTestMap]
  have hg : galoisMatrix ξ σ = P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹ :=
    eq_mul_inv_of_mul_eq (hgP σ)
  change (GeneralLinearGroup.map (pointScalars s) P)⁻¹ *
      (GeneralLinearGroup.map (pointScalars s) (galoisMatrix ξ σ) * _ *
        (GeneralLinearGroup.map (pointScalars s) (galoisMatrix ξ σ))⁻¹) *
      GeneralLinearGroup.map (pointScalars s) P = _
  rw [hg, GeneralLinearGroup.map_comp, MonoidHom.comp_apply, map_mul, map_inv]
  group

/-- The charts have the discrepancy cocycle `ξ`. -/
theorem chartLocalIso_hasDiscrepancy (hq : IsAdjointQuotient (𝟙 (splitGroup K)))
    (ξ : Cocycle (splitGroup K) (ringTest K L))
    (hgP : ∀ σ, galoisMatrix ξ σ * GeneralLinearGroup.map (σ : L →+* L) P = P) :
    (chartLocalIso hP).HasDiscrepancy hq.innerAction ξ := by
  rw [LocalGroupIso.hasDiscrepancy_iff_overlap]
  apply LocalGroupIso.hasOverlapDiscrepancy_of_galois
  intro σ V s g
  have h : Cocycle.galoisPair σ ≫ ξ.overlap = galoisValue ξ σ := by
    rw [galoisValue, Cocycle.toFun_eq_lift_overlap]
    rfl
  rw [h]
  exact chartPoints_galois hP hq ξ hgP σ s g

variable {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The local isomorphisms from `G` to the automorphism group of the twisted datum. -/
def compareLocalIso (e : LocalGroupIso (splitGroup K) G (ringTest K L)) :
    LocalGroupIso G (datum hP).automorphismGroup (ringTest K L) where
  toFun b := (e.toFun b).symm.trans ((chartLocalIso hP).toFun b)
  naturality t b g := by
    change (chartLocalIso hP).toFun (t ≫ b) ((e.toFun (t ≫ b)).symm (t ≫ g)) =
      t ≫ (chartLocalIso hP).toFun b ((e.toFun b).symm g)
    rw [← (chartLocalIso hP).naturality]
    congr 1
    exact e.symm.naturality t b g

theorem compareLocalIso_isIndependent (hq : IsAdjointQuotient (𝟙 (splitGroup K)))
    (ξ : Cocycle (splitGroup K) (ringTest K L))
    (hgP : ∀ σ, galoisMatrix ξ σ * GeneralLinearGroup.map (σ : L →+* L) P = P)
    (e : LocalGroupIso (splitGroup K) G (ringTest K L))
    (he : e.HasDiscrepancy hq.innerAction ξ) :
    (compareLocalIso hP e).IsIndependent := by
  intro Z b c h
  change (chartLocalIso hP).toFun b ((e.toFun b).symm h) =
    (chartLocalIso hP).toFun c ((e.toFun c).symm h)
  obtain ⟨g, rfl⟩ := (e.toFun c).surjective h
  rw [MulEquiv.symm_apply_apply, ← he b c g, MulEquiv.symm_apply_apply]
  exact chartLocalIso_hasDiscrepancy hP hq ξ hgP b c g

end Chart

/-- **Inner forms of the split Cayley automorphism group.** A group scheme with local
isomorphisms over a finite Galois extension from the split Cayley automorphism group, whose
discrepancy is a cocycle for the inner action, is isomorphic to the automorphism group scheme
of an actual Cayley datum over the ground field. -/
theorem exists_iso_automorphismGroup [FiniteDimensional K L] [IsGalois K L]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (hq : IsAdjointQuotient (𝟙 (splitGroup K)))
    (e : LocalGroupIso (splitGroup K) G (ringTest K L))
    (ξ : Cocycle (splitGroup K) (ringTest K L))
    (he : e.HasDiscrepancy hq.innerAction ξ) :
    ∃ c : CayleyDatum K, Nonempty (G ≅ c.automorphismGroup) := by
  obtain ⟨P, hPfix⟩ := Langlands.LinearAlgebra.GaloisFixedBasis.exists_fixed (galoisMatrix_mul ξ)
  have hP : IsTwist (K := K) P := by
    intro σ
    rw [← eq_mul_inv_of_mul_eq (hPfix σ)]
    exact galoisMatrix_isAutomorphismMatrix ξ σ
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K L
  let : Surjective (ringTest K L).hom := hsurj
  let : Flat (ringTest K L).hom := hflat
  let : QuasiCompact (ringTest K L).hom := hqc
  exact ⟨datum hP, ⟨(compareLocalIso hP e).descend
    (compareLocalIso_isIndependent hP hq ξ hPfix e he)⟩⟩

end TypeG2CayleyDescent

end Langlands.GroupScheme
