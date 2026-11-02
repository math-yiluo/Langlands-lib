import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Support
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Propagation
import Langlands.AlgebraicGeometry.Modules.CoherentIntegralIdealFiltrationProof
import Langlands.AlgebraicGeometry.Modules.IntegralSupportDimensionProof
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPushforward

/-! # Two-bundle vanishing by induction on actual support -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}} {K : Type u} [Field K]

/-- Uniform quadrant vanishing for all coherent coefficients with this support bound. -/
def GoodInSupportDimension (f : X ⟶ Spec (CommRingCat.of K))
    (L₁ L₂ : LineBundle X) (e : ℕ) : Prop :=
  ∀ G : X.Modules, G.IsQuasicoherent → HasFiniteAffineSections G →
    HasSupportDimensionLT G e → Good f L₁.obj L₂.obj G

/-- The lower-dimensional assertion handles the four errors of two ample sections. -/
theorem good_of_irreducible_support (hkill : SectionKillingStatement.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (L₁ L₂ : LineBundle X) (h₁ : L₁.IsAmple) (h₂ : L₂.IsAmple)
    (e : ℕ) (ih : GoodInSupportDimension f L₁ L₂ e)
    (G : X.Modules) [G.IsQuasicoherent] (hG : HasFiniteAffineSections G)
    (hGe : HasSupportDimensionLT G (e + 1))
    (T : IrreducibleCloseds X) (hT : height T ≤ e)
    (hGT : QuasicoherentLocal.VanishesOn G
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩) :
    Good f L₁.obj L₂.obj G := by
  obtain ⟨d₁, hd₁, s₁, hs₁, hk₁, hc₁⟩ :=
    exists_ampleSection_errorsLT L₁ h₁ G T e hT hGT
  obtain ⟨d₂, hd₂, s₂, _, hk₂, hc₂⟩ :=
    exists_ampleSection_errorsLT L₂ h₂ G T e hT hGT
  have htarget₁ := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle G _
    (rankOne_pow L₁.obj L₁.property d₁)
  have htarget₂ := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle G _
    (rankOne_pow L₂.obj L₂.property d₂)
  have hfinite₁ := hG.tensor_lineBundle (rankOne_pow L₁.obj L₁.property d₁)
  have hfinite₂ := hG.tensor_lineBundle (rankOne_pow L₂.obj L₂.property d₂)
  exact Good.of_sectionKilling hkill f L₁.obj L₂.obj G L₁.property L₂.property hG
    (e + 1) hGe d₁ d₂ hd₁ hd₂ s₁ s₂ hs₁
    (ih _ (QuasicoherentLocal.isQuasicoherent_kernel _) (hG.kernel _) hk₁)
    (ih _ (QuasicoherentLocal.isQuasicoherent_cokernel _) (hfinite₁.cokernel _) hc₁)
    (ih _ (QuasicoherentLocal.isQuasicoherent_kernel _) (hG.kernel _) hk₂)
    (ih _ (QuasicoherentLocal.isQuasicoherent_cokernel _) (hfinite₂.cokernel _) hc₂)

/-- A nonzero ideal on an integral closed subscheme has irreducible actual closed support. -/
theorem good_closed_integral_ideal (hkill : SectionKillingStatement.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (L₁ L₂ : LineBundle X) (h₁ : L₁.IsAmple) (h₂ : L₂.IsAmple)
    (e : ℕ) (ih : GoodInSupportDimension f L₁ L₂ e)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.Modules) [I.IsQuasicoherent] (hI : HasFiniteAffineSections I)
    (ι : I ⟶ structureModule Z) [Mono ι] (hne : ¬ IsZero I)
    (hGe : HasSupportDimensionLT ((Scheme.Modules.pushforward i).obj I) (e + 1)) :
    Good f L₁.obj L₂.obj ((Scheme.Modules.pushforward i).obj I) := by
  let : ((Scheme.Modules.pushforward i).obj I).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_pushforward i I
  let T : IrreducibleCloseds X :=
    ⟨Set.range i, by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ Z).image i
          i.continuous.continuousOn,
      i.isClosedEmbedding.isClosed_range⟩
  have hsupp : (closedStalkSupport ((Scheme.Modules.pushforward i).obj I) : Set X) =
      (T : Set X) := by
    rw [coe_closedStalkSupport_pushforward i i.isClosedEmbedding I,
      closedStalkSupport_ideal_eq_top Z I ι hne]
    exact Set.image_univ
  have hT : height T ≤ e := by
    apply (ENat.lt_add_one_iff (ENat.natCast_ne_top e)).mp
    have h := (hasSupportDimensionLT_iff_closedStalkSupport _ (e + 1)).mp hGe T
      (by rw [hsupp])
    simpa only [Nat.cast_add, Nat.cast_one] using h
  exact good_of_irreducible_support hkill f L₁ L₂ h₁ h₂ e ih _ (hI.pushforward i)
    hGe T hT (vanishesOn_pushforward_compl_range i i.isClosedEmbedding I)

/-- An actual coherent integral-ideal filtration reduces the successor bound to its factors. -/
theorem GoodInSupportDimension.succ (hkill : SectionKillingStatement.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (L₁ L₂ : LineBundle X) (h₁ : L₁.IsAmple) (h₂ : L₂.IsAmple)
    (e : ℕ) (ih : GoodInSupportDimension f L₁ L₂ e) :
    GoodInSupportDimension f L₁ L₂ (e + 1) := by
  classical
  intro M hM hMf hMe
  let : M.IsQuasicoherent := hM
  obtain ⟨n, T, h0, ⟨iM⟩, hcoh, hstep⟩ :=
    coherentIntegralIdealFiltration X M hM hMf
  choose Z i hi hZ I ι hι hIc hI hne α β hcomp hshort using hstep
  let F : CoherentFiltration X n :=
    { term := T
      factor := fun j => (Scheme.Modules.pushforward (i j)).obj (I j)
      zero := h0
      inclusion := α
      projection := β
      comp_zero := hcomp
      shortExact := hshort
      term_quasicoherent := fun j => (hcoh j).1
      term_finite := fun j => (hcoh j).2
      factor_quasicoherent := fun j => by
        let : IsClosedImmersion (i j) := hi j
        let : (I j).IsQuasicoherent := hIc j
        exact QuasicoherentLocal.isQuasicoherent_pushforward (i j) (I j)
      factor_finite := fun j => by
        let : IsClosedImmersion (i j) := hi j
        exact (hI j).pushforward (i j) }
  have hfactor : ∀ j, HasSupportDimensionLT (F.factor j) (e + 1) :=
    (F.hasSupportDimensionLT_iff (e + 1)).mp (hMe.of_iso iM.symm)
  apply (Good.filtration f L₁.obj L₂.obj L₁.property L₂.property F ?_).of_iso iM
  intro j
  let : IsClosedImmersion (i j) := hi j
  let : IsIntegral (Z j) := hZ j
  let : (I j).IsQuasicoherent := hIc j
  let : Mono (ι j) := hι j
  exact good_closed_integral_ideal hkill f L₁ L₂ h₁ h₂ e ih
    (Z j) (i j) (I j) (hI j) (ι j) (hne j) (hfactor j)

/-- Conditional on section killing, every finite actual support bound gives Serre vanishing. -/
theorem goodInSupportDimension (hkill : SectionKillingStatement.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (L₁ L₂ : LineBundle X) (h₁ : L₁.IsAmple) (h₂ : L₂.IsAmple) (e : ℕ) :
    GoodInSupportDimension f L₁ L₂ e := by
  induction e with
  | zero =>
      intro G _ _ hG
      exact Good.of_isZero f L₁.obj L₂.obj L₁.property L₂.property hG.isZero
  | succ e ih => exact GoodInSupportDimension.succ hkill f L₁ L₂ h₁ h₂ e ih

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
