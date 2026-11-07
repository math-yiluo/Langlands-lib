import Langlands.GroupScheme.Torus.FieldCocycleDescent
import Langlands.GroupScheme.Torus.TransporterFunctoriality
import Langlands.GroupScheme.Rational.TorusCentralizer
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Descent of transporter points with split-torus centralizer -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H : CommGroupScheme S} {G : GroupScheme S}
  {i₁ i₂ : H.toGrp ⟶ G} {U : Over S} {x y : U ⟶ G.X}

/-- Two transporters for the same maps differ on the right by a centralizer point. -/
theorem IsTransporter.inv_mul_mem_torusCentralizer
    (hx : IsTransporter i₁ i₂ x) (hy : IsTransporter i₁ i₂ y) :
    x⁻¹ * y ∈ (torusCentralizer i₂).carrier U := by
  intro V a t
  change (a ≫ (x⁻¹ * y)) * (t ≫ i₂.hom.hom) =
    (t ≫ i₂.hom.hom) * (a ≫ (x⁻¹ * y))
  rw [MonObj.comp_mul, GrpObj.comp_inv]
  have hx' := hx V a t
  have hy' := hy V a t
  calc
    (a ≫ x)⁻¹ * (a ≫ y) * (t ≫ i₂.hom.hom) =
        (a ≫ x)⁻¹ * ((a ≫ y) * (t ≫ i₂.hom.hom)) := by group
    _ = (a ≫ x)⁻¹ * ((t ≫ i₁.hom.hom) * (a ≫ y)) := by rw [← hy']
    _ = (a ≫ x)⁻¹ * ((t ≫ i₁.hom.hom) * (a ≫ x)) *
        (a ≫ x)⁻¹ * (a ≫ y) := by group
    _ = (a ≫ x)⁻¹ * ((a ≫ x) * (t ≫ i₂.hom.hom)) *
        (a ≫ x)⁻¹ * (a ≫ y) := by rw [hx']
    _ = (t ≫ i₂.hom.hom) * ((a ≫ x)⁻¹ * (a ≫ y)) := by group

/-- Right multiplication by a centralizer point preserves a transporter. -/
theorem IsTransporter.mul_of_mem_torusCentralizer
    (hx : IsTransporter i₁ i₂ x) (hy : y ∈ (torusCentralizer i₂).carrier U) :
    IsTransporter i₁ i₂ (x * y) := by
  intro V a t
  rw [MonObj.comp_mul, ← mul_assoc, hx V a t, mul_assoc, ← (hy V a t).eq, ← mul_assoc]

/-- The overlap cocycle of the inverse transporter takes values in the torus image. -/
theorem IsTransporter.coboundary_inv_mem_range
    (hx : IsTransporter i₁ i₂ x)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂) {Z : Over S} (a b : Z ⟶ U) :
    ∃ t : Z ⟶ H.X, t ≫ i₂.hom.hom = (Cocycle.coboundary x⁻¹).toFun a b := by
  apply SubgroupFunctor.mem_range.mp
  rw [← hC]
  simpa only [Cocycle.coboundary, GrpObj.comp_inv, inv_inv] using
    (hx.restrict a).inv_mul_mem_torusCentralizer (hx.restrict b)

/-- A correction by a cochain trivializing the torus-valued overlap cocycle. -/
def correctedTransporter (i₂ : H.toGrp ⟶ G) (x : U ⟶ G.X)
    (f : U ⟶ H.X) : U ⟶ G.X :=
  x * (f ≫ i₂.hom.hom)

/-- The corrected point remains a transporter. -/
theorem correctedTransporter_isTransporter
    (hx : IsTransporter i₁ i₂ x)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂)
    (f : U ⟶ H.X) : IsTransporter i₁ i₂ (correctedTransporter i₂ x f) := by
  apply hx.mul_of_mem_torusCentralizer
  rw [hC]
  exact SubgroupFunctor.mem_range.mpr ⟨f, rfl⟩

/-- Read the inverse transporter's overlap cocycle in its self-centralizing torus. -/
def transporterCocycle [Mono i₂.hom.hom]
    (hx : IsTransporter i₁ i₂ x)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂) : Cocycle H.toGrp U :=
  (Cocycle.coboundary x⁻¹).lift i₂ (hx.coboundary_inv_mem_range hC)

/-- A trivializing torus cochain makes the corrected transporter agree on overlaps. -/
theorem correctedTransporter_forall_eq [Mono i₂.hom.hom]
    (hx : IsTransporter i₁ i₂ x)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂)
    (f : U ⟶ H.X)
    (hf : ∀ {Z : Over S} (a b : Z ⟶ U),
      (transporterCocycle hx hC).toFun a b = (a ≫ f) * (b ≫ f)⁻¹)
    {Z : Over S} (a b : Z ⟶ U) :
    a ≫ correctedTransporter i₂ x f = b ≫ correctedTransporter i₂ x f := by
  have h := (Cocycle.coboundary x⁻¹).lift_toFun i₂
    (hx.coboundary_inv_mem_range hC) a b
  change (transporterCocycle hx hC).toFun a b ≫ i₂.hom.hom =
    (a ≫ x⁻¹) * (b ≫ x⁻¹)⁻¹ at h
  rw [hf, MonObj.mul_comp, GrpObj.inv_comp, GrpObj.comp_inv,
    GrpObj.comp_inv, inv_inv] at h
  simp only [correctedTransporter, MonObj.comp_mul]
  calc
    (a ≫ x) * ((a ≫ f) ≫ i₂.hom.hom) =
        (a ≫ x) * (((a ≫ f) ≫ i₂.hom.hom) *
          ((b ≫ f) ≫ i₂.hom.hom)⁻¹) * ((b ≫ f) ≫ i₂.hom.hom) := by group
    _ = (a ≫ x) * ((a ≫ x)⁻¹ * (b ≫ x)) * ((b ≫ f) ≫ i₂.hom.hom) := by rw [h]
    _ = (b ≫ x) * ((b ≫ f) ≫ i₂.hom.hom) := by group

/-- A section whose pullback along an fpqc cover is a transporter is a transporter. -/
theorem isTransporter_of_cover [Flat U.hom] [Surjective U.hom] [QuasiCompact U.hom]
    {n : Over.mk (𝟙 S) ⟶ G.X}
    (hx : IsTransporter i₁ i₂ x)
    (hxn : (Over.homMk U.hom (by simp) : U ⟶ Over.mk (𝟙 S)) ≫ n = x) :
    IsTransporter i₁ i₂ n := by
  intro V a t
  let W : Over S := Over.mk (pullback.snd U.hom V.hom ≫ V.hom)
  let e : W ⟶ V := Over.homMk (pullback.snd U.hom V.hom)
  let c : W ⟶ U := Over.homMk (pullback.fst U.hom V.hom) pullback.condition
  have : Epi e.left := inferInstanceAs (Epi (pullback.snd U.hom V.hom))
  have : Epi e := Over.epi_of_epi_left e
  have ha : a.left = V.hom := by
    have ha := Over.w a
    change a.left ≫ 𝟙 S = V.hom at ha
    exact (Category.comp_id _).symm.trans ha
  have hc : e ≫ a = c ≫ Over.homMk U.hom (by simp) := by
    apply Over.OverMorphism.ext
    change pullback.snd U.hom V.hom ≫ a.left =
      pullback.fst U.hom V.hom ≫ U.hom
    rw [ha, pullback.condition]
  apply (cancel_epi e).mp
  simp only [MonObj.comp_mul, ← Category.assoc]
  simpa only [hc, Category.assoc, hxn] using hx W c (e ≫ t)

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i₁ i₂ : T.toGrp ⟶ G} {U : Over (Spec (CommRingCat.of k))}
  [Mono i₂.hom.hom] [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
  {x : U ⟶ G.X}

/-- A transporter under a self-centralizing split torus descends from any affine fpqc cover. -/
theorem exists_transporter_of_cover
    (hT : IsSplitTorus T.toGrp) (hx : IsTransporter i₁ i₂ x)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, IsTransporter i₁ i₂ n := by
  let f := Cocycle.fieldTrivializingCochain hT (transporterCocycle hx hC)
  have hf : ∀ {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ U),
      (transporterCocycle hx hC).toFun a b = (a ≫ f) * (b ≫ f)⁻¹ :=
    fun a b => Cocycle.fieldTrivializingCochain_spec hT (transporterCocycle hx hC) a b
  let y := correctedTransporter i₂ x f
  have hy : IsTransporter i₁ i₂ y := correctedTransporter_isTransporter hx hC f
  obtain ⟨s, hs, hb⟩ := exists_section_of_forall_eq y
    (correctedTransporter_forall_eq hx hC f hf)
  let n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk s hb
  refine ⟨n, isTransporter_of_cover hy ?_⟩
  apply Over.OverMorphism.ext
  exact hs

end Field

end PointwiseSchemeAction
end Langlands.GroupScheme
