import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.CocharacterAffineTransport
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Cocharacters of proper group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)

/-- Properness extends the image of the power-series parameter. Rescaling the
parameter by a unit fixes the specialisation of this image, so the image of
that unit is the identity. -/
private theorem cocharacter_comp_fieldPoint_eq_one
    {H : CommGroupScheme S} [IsProper H.X.hom]
    (f : cocharacterLattice H) (x : Over.mk (𝟙 S) ⟶ (Gm S).X) :
    x ≫ (CommGroupScheme.groupHom f).hom.hom = 1 := by
  let R := PowerSeries k
  let K := FractionRing R
  let a := Gm.affinePointsEquiv (𝟙 S) x
  let α := Spec.algebraMap k R
  let j₀ := Spec.algebraMap R K
  let j : Over.mk (j₀ ≫ α) ⟶ Over.mk α := Gm.affineMap (CommRingCat.ofHom (algebraMap R K)) α
  let projection : Over.mk α ⟶ Over.mk (𝟙 S) := Over.homMk α (by simp)
  let section₀ : Over.mk (𝟙 S) ⟶ Over.mk α :=
    Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) (by
      change Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)) = 𝟙 S
      rw [← Spec.map_comp]
      exact (Spec.map_id _ ▸ rfl : Spec.map (𝟙 (CommRingCat.of k)) = 𝟙 S))
  have hsection : section₀ ≫ projection = 𝟙 _ :=
    Over.OverMorphism.ext section₀.w
  let σ : R →+* R := PowerSeries.rescale a.val
  let σK : K →+* K := IsFractionRing.map (PowerSeries.rescale_injective a.ne_zero)
  have hσK : σK.comp (algebraMap R K) = (algebraMap R K).comp σ :=
    IsLocalization.map_comp _
  let τ : Over.mk α ⟶ Over.mk α := Over.homMk (Spec.map (CommRingCat.ofHom σ)) (by
    change Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = α
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change PowerSeries.rescale a.val (algebraMap k R r) = algebraMap k R r
    rw [← PowerSeries.coe_rescaleAlgHom]
    exact (PowerSeries.rescaleAlgHom a.val).commutes r)
  let τK₀ := Spec.map (CommRingCat.ofHom σK)
  have hbase : j₀ ≫ τ.left = τK₀ ≫ j₀ := by
    change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ Spec.map (CommRingCat.ofHom σ) =
      Spec.map (CommRingCat.ofHom σK) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun e : R →+* K => Spec.map (CommRingCat.ofHom e)) hσK.symm
  let τK : Over.mk (j₀ ≫ α) ⟶ Over.mk (j₀ ≫ α) :=
    Over.homMk τK₀ (by
      change τK₀ ≫ j₀ ≫ α = j₀ ≫ α
      rw [← Category.assoc, ← hbase, Category.assoc, show τ.left ≫ α = α from Over.w τ])
  have hτj : j ≫ τ = τK ≫ j := Over.OverMorphism.ext hbase
  have hτs : section₀ ≫ τ = section₀ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫
      Spec.map (CommRingCat.ofHom σ) = Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff)
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change PowerSeries.constantCoeff (PowerSeries.rescale a.val r) = PowerSeries.constantCoeff r
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
      pow_zero, one_mul]
  let z := Units.mk0 (algebraMap R K PowerSeries.X)
    (by simpa only [map_zero] using
      (IsFractionRing.injective R K).ne PowerSeries.X_ne_zero)
  let p : Over.mk (j₀ ≫ α) ⟶ (Gm S).X := (Gm.affinePointsEquiv (j₀ ≫ α)).symm z
  have hp : τK ≫ p = ((j ≫ projection) ≫ x) * p := by
    apply (Gm.affinePointsEquiv (j₀ ≫ α)).injective
    rw [Gm.affinePointsEquiv_naturality_of_left (CommRingCat.ofHom σK) τK rfl, map_mul,
      Gm.affinePointsEquiv_naturality_of_left
        (CommRingCat.ofHom ((algebraMap R K).comp (algebraMap k R))) (j ≫ projection)
        (by change j₀ ≫ α = _; rw [← Spec.map_comp]; rfl), MulEquiv.apply_symm_apply]
    apply Units.ext
    change σK (algebraMap R K PowerSeries.X) =
      algebraMap R K (algebraMap k R a.val) * algebraMap R K PowerSeries.X
    have h : σK (algebraMap R K PowerSeries.X) =
        algebraMap R K (PowerSeries.rescale (a.val : k) PowerSeries.X) :=
      RingHom.congr_fun hσK (PowerSeries.X : R)
    rw [PowerSeries.rescale_X, PowerSeries.C_eq_algebraMap, map_mul] at h
    exact h
  let g := (CommGroupScheme.groupHom f).hom.hom
  let sq : ValuativeCommSq H.X.hom :=
    ⟨R, K, (p ≫ g).left, α, ⟨Over.w (p ≫ g)⟩⟩
  have hclosed : UniversallyClosed H.X.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hclosed
  obtain ⟨⟨l, hlgen, hlbase⟩⟩ := (hclosed.1 sq).exists_lift
  let q : Over.mk α ⟶ H.X := Over.homMk l hlbase
  have hq : j ≫ q = p ≫ g := Over.OverMorphism.ext hlgen
  have hker : RingHom.ker (algebraMap R K) = ⊥ := by
    rw [RingHom.ker_eq_bot_iff_eq_zero]
    intro r hr
    exact (IsFractionRing.injective R K) (by rwa [map_zero])
  let : IsDominant j₀ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (algebraMap R K)).mpr (hker.symm ▸ bot_le)⟩
  let : IsReduced (Over.mk α).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hext : τ ≫ q = (projection ≫ x ≫ g) * q := by
    apply Over.OverMorphism.ext
    refine ext_of_isDominant_of_isSeparated H.X.hom
      ((Over.w (τ ≫ q)).trans (Over.w ((projection ≫ x ≫ g) * q)).symm) j₀ ?_
    have h : j ≫ (τ ≫ q) = j ≫ ((projection ≫ x ≫ g) * q) := by
      rw [← Category.assoc, hτj, Category.assoc, hq, ← Category.assoc, hp,
        MonObj.mul_comp, MonObj.comp_mul, hq, Category.assoc, Category.assoc]
    exact congrArg (fun v => v.left) h
  have h := congrArg (fun v => section₀ ≫ v) hext
  rw [← Category.assoc section₀ τ q, hτs, MonObj.comp_mul,
    ← Category.assoc section₀ projection, hsection, Category.id_comp] at h
  exact mul_right_cancel (by simpa only [one_mul] using h.symm)

/-- A proper commutative group scheme over a separably closed field has only
the trivial cocharacter. -/
theorem cocharacter_eq_zero_of_isProper [IsSepClosed k] {H : CommGroupScheme S}
    [IsProper H.X.hom] (f : cocharacterLattice H) : f = 0 := by
  let : Smooth (Gm S).X.hom := smooth_gm S
  let : IsReduced (Gm S).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (Gm S).X.hom
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Langlands.AlgebraicGeometry.PointTopology.hom_ext_of_denseRationalPoints
    (Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed
      k (Gm S).X)
  intro x
  change x ≫ (CommGroupScheme.groupHom f).hom.hom =
    x ≫ (CommGroupScheme.groupHom (0 : cocharacterLattice H)).hom.hom
  rw [comp_groupHom_zero]
  exact cocharacter_comp_fieldPoint_eq_one f x

end Langlands.GroupScheme
