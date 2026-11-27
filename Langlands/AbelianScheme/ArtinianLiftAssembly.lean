import Langlands.AbelianScheme.ArtinianConstantCharts
import Langlands.AlgebraicGeometry.TwistedOpenGluingLift

/-! # Smooth proper pointed lifts from lifted transition maps of constant charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.TwistedOpenGluing

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] (S : Setting R' R)
  (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- The open of the constant scheme over an open of `B`. -/
abbrev V (U : B.X.left.Opens) : (S.C B).X.left.Opens :=
  pullback.fst (S.A₀ B).X.hom S.sσ ⁻¹ᵁ S.W B U

theorem VT_eq (U : B.X.left.Opens) : S.VT B U = pullback.fst (S.C B).X.hom S.t ⁻¹ᵁ S.V B U := rfl

theorem nilpotent_ker_φ [IsArtinianRing R'] : IsNilpotent (RingHom.ker S.φ) := by
  obtain ⟨n, hn⟩ := RingTheory.isNilpotent_ker_residue R'
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  have hle : RingHom.ker S.φ ≤ RingHom.ker (residue R') := by
    intro x hx
    rw [RingHom.mem_ker, ← S.hψ, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
  calc RingHom.ker S.φ ^ n ≤ RingHom.ker (residue R') ^ n := Ideal.pow_right_mono hle n
    _ = ⊥ := hn

namespace Charts

variable {S B} (K : S.Charts B) [IsArtinianRing R] [IsLocalRing R]


theorem θS_snd (i j : K.J) :
    K.θS i j ≫ pullback.snd (S.C B).X.hom S.t =
      (S.VT B (K.U i) ⊓ S.VT B (K.U j)).ι ≫ pullback.snd (S.C B).X.hom S.t := by
  rw [show K.θS i j = K.lift i j ≫ (S.VT B (K.U i)).ι from rfl, Category.assoc,
    ← K.κ_base, lift_κ_assoc, K.κ_base, Scheme.homOfLE_ι_assoc]

theorem restrictTo_eq_lift (i j : K.J) (f : (S.VT B (K.U i) ⊓ S.VT B (K.U j)).toScheme ⟶ S.CS B)
    (hf : IsPointwiseInclusion f) (hfθ : f = K.θS i j) :
    restrictTo f hf le_rfl inf_le_left = K.lift i j := by
  rw [← cancel_mono (S.VT B (K.U i)).ι, restrictTo_ι, Scheme.homOfLE_rfl, Category.id_comp, hfθ]
  rfl

omit [IsArtinianRing R] [IsLocalRing R] in
theorem hcov : ⨆ i : K.J, (K.κ i).opensRange = ⊤ := by
  simp_rw [K.opensRange_κ]
  exact K.cover

theorem hpre (i j : K.J) :
    (K.κ j) ⁻¹ᵁ (K.κ i).opensRange ≤ (S.VT B (K.U j)).ι ⁻¹ᵁ S.VT B (K.U i) := by
  intro x hx
  rw [K.opensRange_κ] at hx
  have hx' : K.κ j x ∈ K.U i := hx
  rw [K.κ_apply] at hx'
  exact hx'

/-- Transition maps on the constant scheme over `R'` lifting the transition maps of the charts. -/
structure LiftedTransitions where
  θ : ∀ i j : K.J, (S.V B (K.U i) ⊓ S.V B (K.U j)).toScheme ⟶ (S.C B).X.left
  pointwise : ∀ i j, IsPointwiseInclusion (θ i j)
  self : ∀ i, θ i i = (S.V B (K.U i) ⊓ S.V B (K.U i)).ι
  cocycle : ∀ i j k,
    restrictTo (θ j k) (pointwise j k) (W := S.V B (K.U i) ⊓ S.V B (K.U j) ⊓ S.V B (K.U k))
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ θ i j =
      (S.C B).X.left.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        S.V B (K.U i) ⊓ S.V B (K.U j) ⊓ S.V B (K.U k) ≤ S.V B (K.U i) ⊓ S.V B (K.U k)) ≫ θ i k
  overBase : ∀ i j, θ i j ≫ (S.C B).X.hom = (S.V B (K.U i) ⊓ S.V B (K.U j)).ι ≫ (S.C B).X.hom
  reduces : ∀ i j, (pullback.fst (S.C B).X.hom S.t).resLE (S.V B (K.U i) ⊓ S.V B (K.U j))
      (S.VT B (K.U i) ⊓ S.VT B (K.U j)) le_rfl ≫ θ i j =
    K.θS i j ≫ pullback.fst (S.C B).X.hom S.t

namespace LiftedTransitions

variable {K} (L : K.LiftedTransitions)

/-- The gluing data of the lifted transition maps. -/
def data : Data (S.C B).X.left where
  J := K.J
  V i := S.V B (K.U i)
  θ := L.θ
  pointwise := L.pointwise
  self := L.self
  cocycle := L.cocycle

theorem isOver : L.data.IsOver (S.C B).X.hom := L.overBase

instance : IsClosedImmersion S.t := IsClosedImmersion.spec_of_surjective _ S.surj

theorem θT_eq (i j : K.J) : Data.θT L.isOver S.t i j = K.θS i j := by
  apply pullback.hom_ext
  · exact (Data.θT_fst L.isOver S.t i j).trans (L.reduces i j)
  · exact (Data.θT_snd L.isOver S.t i j).trans (K.θS_snd i j).symm

theorem hκ (i j : K.J) :
    (S.CS B).homOfLE (inf_le_right : S.VT B (K.U i) ⊓ S.VT B (K.U j) ≤ _) ≫ K.κ j =
      restrictTo ((L.data.baseChange L.isOver S.t).θ i j)
        ((L.data.baseChange L.isOver S.t).pointwise i j) le_rfl inf_le_left ≫ K.κ i := by
  have h := restrictTo_eq_lift K i j ((L.data.baseChange L.isOver S.t).θ i j)
    ((L.data.baseChange L.isOver S.t).pointwise i j) (L.θT_eq i j)
  exact (K.lift_κ i j).symm.trans (congrArg (· ≫ K.κ i) h.symm)

instance [IsArtinianRing R'] : Surjective S.t := by
  have := primeSpectrum_subsingleton (R := R')
  constructor
  intro y
  exact ⟨IsLocalRing.closedPoint R, @Subsingleton.elim (PrimeSpectrum R') this _ _⟩

include L in
/-- Lifted transition maps of the charts give a smooth proper pointed lift of `B`. -/
theorem exists_smoothLift [IsArtinianRing R'] :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R')) (s : Spec (CommRingCat.of R') ⟶ X),
      s ≫ p = 𝟙 _ ∧ Smooth p ∧ IsProper p ∧
      ∃ e₀ : B.X.left ≅ pullback p S.t,
        e₀.hom ≫ pullback.snd p S.t = B.X.hom ∧
          η[B.X].left ≫ e₀.hom ≫ pullback.fst p S.t = S.t ≫ s := by
  let D := L.data
  have hπ := L.isOver
  let κ' : ∀ i, ((D.baseChange hπ S.t).V i).toScheme ⟶ B.X.left := K.κ
  have : ∀ i, IsOpenImmersion (κ' i) := fun i ↦ inferInstanceAs (IsOpenImmersion (K.κ i))
  have hq : ∀ i, κ' i ≫ B.X.hom =
      ((D.baseChange hπ S.t).V i).ι ≫ pullback.snd (S.C B).X.hom S.t := K.κ_base
  let e := Data.liftIso hπ S.t κ' K.hcov K.hpre L.hκ
  have he : e.hom ≫ pullback.snd (D.toBase hπ) S.t = B.X.hom :=
    Data.liftIso_hom_snd hπ S.t B.X.hom κ' K.hcov K.hpre L.hκ hq
  have hproper : IsProper (D.toBase hπ) :=
    Data.isProper_toBase hπ S.t B.X.hom κ' K.hcov K.hpre L.hκ hq
  have hsmooth : Smooth (D.toBase hπ) := D.smooth_toBase hπ
  obtain ⟨s, hs₁, hs₂⟩ := Langlands.AlgebraicGeometry.exists_section_lift
    (CommRingCat.ofHom S.φ) S.surj S.nilpotent_ker_φ (D.toBase hπ)
    (η[B.X].left ≫ e.hom) (by rw [Category.assoc, he]; exact Over.w η[B.X])
  refine ⟨D.glued, D.toBase hπ, s, hs₁, hsmooth, hproper, e, he, ?_⟩
  rw [← Category.assoc]
  exact hs₂.symm

end LiftedTransitions

end Charts

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
