import Langlands.AlgebraicGeometry.Picard.LinearSystemAffineBundle
import Langlands.AlgebraicGeometry.Picard.LinearSystemUniversality
import Langlands.RingTheory.Grassmannian.Representability

/-! # The linear system over an affine noetherian base

For `π : X ⟶ Spec R` proper, flat and geometrically integral over a noetherian ring and a line
bundle `L` on `X`, the Grassmannian of rank-one quotients of the module `Q` of a Čech
representative of `L`, with the universal divisor `W`, is universal for the linear system of
`L` over all locally noetherian tests. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)

/-- **A finite ordered affine cover carrying frames of a line bundle.** -/
theorem exists_framed_cover {X : Scheme.{u}} [CompactSpace X] (L : LineBundle X) :
    ∃ (𝒰 : X.OrderedAffineCover) (e : ∀ i, Γ(L.obj, 𝒰.U i)),
      ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i) := by
  classical
  let B : Set X.Opens := {U | IsAffineOpen U ∧ ∃ t : Γ(L.obj, U), Scheme.Modules.IsFrameOn t U}
  have hB : TopologicalSpace.Opens.IsBasis B := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V x hxV
    obtain ⟨U, hxU, t, ht⟩ := exists_affine_frame L x
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'le⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ U.1 ⊓ V from ⟨hxU, hxV⟩)
        (U.1 ⊓ V).2
    have h1 : U' ≤ U.1 := hU'le.trans inf_le_left
    exact ⟨U', ⟨hU', L.obj.presheaf.map (homOfLE h1).op t, (ht.map (homOfLE h1)).mono h1⟩,
      hxU', hU'le.trans inf_le_right⟩
  obtain ⟨Us, hUs, hfinite, hcover⟩ :=
    hB.exists_finite_of_isCompact (U := ⊤) (show IsCompact (⊤ : X.Opens).carrier from isCompact_univ)
  let : Fintype Us := hfinite.fintype
  let : LinearOrder Us :=
    LinearOrder.lift' (Fintype.equivFin Us) (Fintype.equivFin Us).injective
  exact ⟨{
      ι := Us
      U := Subtype.val
      isAffineOpen := fun i => (hUs i.property).1
      iSup_eq_top := by
        simpa only [sSup_eq_iSup'] using hcover.symm },
    fun i => (hUs i.property).2.choose, fun i => (hUs i.property).2.choose_spec⟩

/-- A representing scheme of the Grassmannian of rank-one quotients exists. -/
theorem nonempty_rep (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    Nonempty (Rep R M 1) := by
  obtain ⟨Gr, p, pt, V, hpt, hV, hVaff, hVchart⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover R M 1
  exact ⟨⟨Gr, p, pt, hpt, V, hV, hVaff, hVchart⟩⟩

/-- **The Grassmannian model of the linear system over an affine noetherian base**: a Čech
representative `C` of `L`, a representing scheme `D` of the Grassmannian of rank-one quotients of
its module `Q`, and the universal divisor, universal for the linear system of `L`. -/
theorem exists_model {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsProper π] [Flat π] [GeometricallyIntegral π] (L : LineBundle X) :
    ∃ (𝒰 : X.OrderedAffineCover) (C : CechRep π L.obj 𝒰) (D : Rep R C.Q 1)
      (W : (pullback π D.p).IdealSheafData),
        LinearSystemGluing.IsUniversalOn π L.classOf ⊤ D.p W := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  obtain ⟨𝒰, e, he⟩ := exists_framed_cover L
  have htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.obj ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
    intro x
    obtain ⟨U, hxU, ⟨eU⟩⟩ := L.property x
    exact ⟨U, hxU, ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.obj).symm ≪≫ eU⟩⟩
  obtain ⟨C⟩ := nonempty_cechRep π L.obj 𝒰 htriv
  obtain ⟨D⟩ := nonempty_rep R C.Q
  obtain ⟨W, hW⟩ := LinSys.exists_universalDivisor e he D
  have hWrel := isRelativeEffectiveCartierIdeal_universal e he C D hW
  obtain ⟨N, hN⟩ := exists_lineBundle_universal e he C D hW hWrel
  refine ⟨𝒰, C, D, W, fun _ _ => trivial, ⟨hWrel, N.classOf, hN⟩, fun T _ t _ E hE => ?_,
      fun T _ t k₁ k₂ hk₁ hk₂ h => eq_of_comap_mapX_eq e he C D hW k₁ k₂ hk₁ hk₂ h⟩
  obtain ⟨hE, n, hn⟩ := hE
  exact exists_point e he C D hW t E hE n hn

/-- **The linear system of a line bundle over an affine noetherian base is represented by the
Grassmannian of rank-one quotients of `Q`, proper over the base.** -/
theorem exists_affine_universal {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsProper π] [Flat π] [GeometricallyIntegral π] (L : LineBundle X) :
    ∃ (P : Scheme.{u}) (l : P ⟶ Spec (.of R)) (Wd : (pullback π l).IdealSheafData),
      IsLocallyNoetherian P ∧ IsProper l ∧
        LinearSystemGluing.IsUniversalOn π L.classOf ⊤ l Wd := by
  obtain ⟨𝒰, C, D, W, hU⟩ := exists_model π L
  have : IsProper D.p := D.isProper_p
  have : IsLocallyNoetherian D.Gr := LocallyOfFiniteType.isLocallyNoetherian D.p
  exact ⟨D.Gr, D.p, W, inferInstance, inferInstance, hU⟩

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
