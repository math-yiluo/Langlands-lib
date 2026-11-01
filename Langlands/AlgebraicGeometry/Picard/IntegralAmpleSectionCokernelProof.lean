import Langlands.AlgebraicGeometry.Picard.IntegralAmpleSectionCokernelStatement
import Langlands.AlgebraicGeometry.Picard.EulerPositivityPreparationProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Modules.SectionCoefficients
import Langlands.AlgebraicGeometry.Modules.CechResolution.Basic
import Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Nonzero section cokernels for integral ample geometry -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Modules

/-- On an integral scheme a section which is a frame somewhere defines a
monomorphism out of the structure module. -/
theorem mono_sectionHom_of_nonempty_trivializationOpen
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (s : GlobalSections M)
    (hs : (trivializationOpen M s : Set X).Nonempty) :
    Mono (sectionHom M s) := by
  apply CechResolution.mono_of_app_injective
  intro U a b hab
  by_cases hU : (U : Set X).Nonempty
  · obtain ⟨x, hxU, hxS⟩ :=
      nonempty_preirreducible_inter U.isOpen (trivializationOpen M s).isOpen hU hs
    let V : X.Opens := U ⊓ trivializationOpen M s
    let : Nonempty V := ⟨⟨x, hxU, hxS⟩⟩
    let i : V ⟶ U := homOfLE inf_le_left
    apply map_injective_of_isIntegral X i
    apply (bijective_sectionHom_app_of_le M s (V := V) inf_le_right).injective
    have hnat (r : Γ(X, U)) :
        (sectionHom M s).app V (X.presheaf.map i.op r) =
          M.presheaf.map i.op ((sectionHom M s).app U r) :=
      ConcreteCategory.congr_hom ((sectionHom M s).mapPresheaf.naturality i.op) r
    exact (hnat a).trans ((congrArg (M.presheaf.map i.op) hab).trans (hnat b).symm)
  · have hbot : U = ⊥ := by
      apply SetLike.coe_injective
      exact Set.not_nonempty_iff_eq_empty.mp hU
    subst U
    change Γ(X, ⊥) at a b
    exact Subsingleton.elim a b

/-- A generically generating section on an integral scheme has zero
cokernel exactly when its generation open is the whole scheme. -/
theorem isZero_sectionHom_cokernel_iff
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (s : GlobalSections M)
    (hs : (trivializationOpen M s : Set X).Nonempty) :
    IsZero (cokernel (sectionHom M s)) ↔ trivializationOpen M s = ⊤ := by
  have : Mono (sectionHom M s) :=
    mono_sectionHom_of_nonempty_trivializationOpen M s hs
  constructor
  · intro h
    have : Epi (sectionHom M s) := (Preadditive.epi_iff_isZero_cokernel _).mpr h
    exact trivializationOpen_eq_top_of_isIso M s (isIso_of_mono_of_epi _)
  · intro h
    have : IsIso (sectionHom M s) := isIso_sectionHom_of_trivializationOpen_eq_top M s h
    exact isZero_cokernel_of_epi _

/-- Every section cokernel is supported outside the generation open. -/
theorem stalkSupport_sectionHom_cokernel_subset
    {X : Scheme.{u}} (M : X.Modules) (s : GlobalSections M) :
    stalkSupport (cokernel (sectionHom M s)) ⊆
      (trivializationOpen M s : Set X)ᶜ := by
  intro x hx hxU
  let U := trivializationOpen M s
  let F := Scheme.Modules.restrictFunctor U.ι
  have : IsIso (F.map (sectionHom M s)) := trivializesOn_trivializationOpen M s
  have hz : IsZero (F.obj (cokernel (sectionHom M s))) :=
    (isZero_cokernel_of_epi (F.map (sectionHom M s))).of_iso
      (PreservesCokernel.iso F (sectionHom M s))
  let y : U.toScheme := ⟨x, hxU⟩
  let G := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y
  have hzy := G.map_isZero hz
  apply hx
  exact hzy.of_iso ((Scheme.Modules.restrictStalkNatIso U.ι y).app
    (cokernel (sectionHom M s))).symm

/-- For a generically generating section of a line bundle on an integral
scheme, the cokernel support is exactly the closed vanishing locus. -/
theorem stalkSupport_sectionHom_cokernel_eq
    {X : Scheme.{u}} [IsIntegral X] (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : (trivializationOpen L.obj s : Set X).Nonempty) :
    stalkSupport (cokernel (sectionHom L.obj s)) =
      (trivializationOpen L.obj s : Set X)ᶜ := by
  apply Set.Subset.antisymm (stalkSupport_sectionHom_cokernel_subset L.obj s)
  intro x hx
  change ¬ IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
    (cokernel (sectionHom L.obj s)).presheaf)
  intro hz
  let F := PushforwardInjectiveAcyclic.toAbSheaf X ⋙
    (TopCat.Sheaf.forget Ab.{u} X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x)
  have hmono : Mono (sectionHom L.obj s) :=
    mono_sectionHom_of_nonempty_trivializationOpen L.obj s hs
  have : Mono (F.map (sectionHom L.obj s)) := F.map_mono _
  have hz' : IsZero (F.obj (cokernel (sectionHom L.obj s))) := hz
  have hcz : IsZero (cokernel (F.map (sectionHom L.obj s))) :=
    hz'.of_iso (PreservesCokernel.iso F (sectionHom L.obj s)).symm
  have : Epi (F.map (sectionHom L.obj s)) :=
    (Preadditive.epi_iff_isZero_cokernel _).mpr hcz
  apply hx
  rw [← lineBundle_stalkFrame_set_eq L s]
  exact isIso_of_mono_of_epi (F.map (sectionHom L.obj s))

/-- A nonempty generation open on an integral scheme gives the actual
short exact sequence from the structure module to the section cokernel. -/
theorem shortExact_sectionHom_cokernel
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (s : GlobalSections M)
    (hs : (trivializationOpen M s : Set X).Nonempty) :
    (ShortComplex.cokernelSequence (sectionHom M s)).ShortExact := by
  have : Mono (sectionHom M s) :=
    mono_sectionHom_of_nonempty_trivializationOpen M s hs
  exact { exact := ShortComplex.cokernelSequence_exact _
          mono_f := by change Mono (sectionHom M s); infer_instance }

/-- Actual section exact sequences and nonzero ample-power cokernels. -/
theorem integralAmpleSectionCokernel : IntegralAmpleSectionCokernelStatement.{u} := by
  constructor
  · intro X _ M s hs
    exact ⟨shortExact_sectionHom_cokernel M s hs,
      isZero_sectionHom_cokernel_iff M s hs, stalkSupport_sectionHom_cokernel_subset M s⟩
  · intro K _ X _ f hp hd L hL x
    obtain ⟨n, hn, s, hx, ha, y, hy⟩ :=
      (eulerPositivityPreparation K X f).2 hp hd |>.2 L hL x
    have hs : (L.sectionOpen s : Set X).Nonempty := ⟨x, hx⟩
    refine ⟨n, hn, s, hx, ha, shortExact_sectionHom_cokernel _ s hs, ?_,
      stalkSupport_sectionHom_cokernel_subset _ s⟩
    intro hz
    have htop := (isZero_sectionHom_cokernel_iff _ s hs).mp hz
    apply hy
    change y ∈ trivializationOpen _ s
    rw [htop]
    trivial

end Langlands.AlgebraicGeometry.Picard
