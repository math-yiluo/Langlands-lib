import Langlands.AlgebraicGeometry.Modules.IntegralIdealOpenStatement
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen
import Langlands.AlgebraicGeometry.Modules.TensorSections

/-! # A nonzero ideal contains a unit on a nonempty open -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Order
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

/-- A nonzero ideal sheaf on a reduced scheme agrees with the structure
module on a nonempty open. -/
theorem exists_nonempty_open_isIso_ideal
    (X : Scheme.{u}) [IsReduced X] (I : X.Modules)
    (ι : I ⟶ structureModule X) [Mono ι] (hI : ¬ IsZero I) :
    ∃ V : X.Opens, (V : Set X).Nonempty ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map ι) := by
  classical
  have hex : ∃ (U : X.Opens) (s : Γ(I.restrict U.ι, ⊤)),
      ((Scheme.Modules.restrictFunctor U.ι).map ι).app ⊤ s ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz (U : X.Opens) : ι.app (U.ι ''ᵁ ⊤) = 0 := by
      ext s
      exact hn U s
    have hi : ι = 0 := by
      apply Scheme.Modules.hom_ext
      intro U
      have hzero := hz U
      rw [Scheme.Opens.ι_image_top] at hzero
      simpa only [Scheme.Modules.Hom.zero_app] using hzero
    apply hI
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_mono ι).mp
    simpa only [Category.id_comp, zero_comp] using hi
  obtain ⟨U, s, hs⟩ := hex
  let ρ : I.restrict U.ι ⟶ structureModule U.toScheme :=
    (Scheme.Modules.restrictFunctor U.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom
  let α : structureModule U.toScheme ⟶ I.restrict U.ι :=
    sectionHom (I.restrict U.ι) s
  let ψ : structureModule U.toScheme ⟶ structureModule U.toScheme := α ≫ ρ
  let c : Γ(U.toScheme, ⊤) := unitEndCoefficient ψ ⊤
  have hc : c ≠ 0 := by
    intro hc
    have he : ρ.app ⊤ s = 0 := by
      simpa [c, unitEndCoefficient, ψ, α] using hc
    have hi := (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.restrictUnitIso U.ι).hom.app ⊤)).injective
    apply hs
    apply hi
    rw [map_zero]
    change ρ.app ⊤ s = 0
    exact he
  let W : U.toScheme.Opens := U.toScheme.basicOpen c
  have hW : (W : Set U.toScheme).Nonempty := by
    by_contra hn
    have hb : W = ⊥ := (Opens.not_nonempty_iff_eq_bot W).mp hn
    exact hc ((AlgebraicGeometry.basicOpen_eq_bot_iff c).mp hb)
  have hunit : IsUnit (unitEndCoefficient ψ W) := by
    have he := unitEnd_naturality ψ (homOfLE (show W ≤ ⊤ from le_top))
      (1 : Γ(U.toScheme, ⊤))
    rw [map_one] at he
    rw [show unitEndCoefficient ψ W =
      U.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op c from he]
    exact U.toScheme.toRingedSpace.isUnit_res_basicOpen c
  let F := Scheme.Modules.restrictFunctor W.ι
  have hψ : IsIso (F.map ψ) := unitEnd_restrict_isIso ψ W hunit
  have hcomp : IsIso (F.map α ≫ F.map ρ) := by
    simpa only [ψ, Functor.map_comp] using hψ
  have : Epi (F.map α ≫ F.map ρ) := @IsIso.epi_of_iso _ _ _ _ _ hcomp
  have : Epi (F.map ρ) := epi_of_epi (F.map α) (F.map ρ)
  have : IsIso (F.map ρ) := isIso_of_mono_of_epi _
  have hρ : IsIso
      (F.map ((Scheme.Modules.restrictFunctor U.ι).map ι)) := by
    simpa only [ρ, Functor.map_comp, isIso_comp_right_iff] using
      (inferInstance : IsIso (F.map ρ))
  let V : X.Opens := U.ι ''ᵁ W
  refine ⟨V, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hW
    exact ⟨U.ι y, ⟨y, hy, rfl⟩⟩
  · apply (isIso_iff_stalk_isIso _).mpr
    intro x
    apply (isIso_stalk_restrict_iff ι V x).mpr
    obtain ⟨y, hy, hxy⟩ := x.property
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x.1).map
      ((Scheme.Modules.toPresheaf X).map ι))
    rw [← hxy]
    apply (isIso_stalk_restrict_iff ι U y).mp
    apply (isIso_stalk_restrict_iff
      ((Scheme.Modules.restrictFunctor U.ι).map ι) W ⟨y, hy⟩).mp
    infer_instance

/-- The quotient of a nonzero ideal on an integral scheme has a strictly
smaller support-height bound than the ambient finite dimension. -/
theorem hasSupportDimensionLT_cokernel_ideal
    (X : Scheme.{u}) [IsIntegral X] (I : X.Modules)
    (ι : I ⟶ structureModule X) [Mono ι] (hI : ¬ IsZero I)
    (d : ℕ) (hX : topologicalKrullDim X ≤ d) :
    HasSupportDimensionLT (cokernel ι) d := by
  obtain ⟨U, hU, hι⟩ := exists_nonempty_open_isIso_ideal X I ι hI
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  apply HasSupportDimensionLT.cokernel_of_irreducible_isIso ι T
    (NoetherianVanishing.height_le_of_topologicalKrullDim_le hX T) U
    (by simpa [T] using hU) ?_ hι
  apply (NoetherianVanishing.VanishesOn.bot
    (structureModule X)).mono
  intro x hx
  exact (hx (Set.mem_univ x)).elim

/-- Nonzero ideal generation on an open and its smaller-support quotient. -/
theorem integralIdealOpen : IntegralIdealOpenStatement.{u} := by
  constructor
  · intro X _ I ι hι hI
    exact exists_nonempty_open_isIso_ideal X I ι hI
  · intro X _ I ι hι hI d hX
    exact hasSupportDimensionLT_cokernel_ideal X I ι hI d hX

end Langlands.AlgebraicGeometry.Modules
