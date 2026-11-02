import Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame
import Langlands.AlgebraicGeometry.ProjectiveBundle.CocycleGluing
import Langlands.AlgebraicGeometry.LocallyFreeRank

/-! # Projective schemes from locally free sheaf frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} (M : S.Modules) (n : ℕ)

/-- The opens on which the sheaf has an actual frame of the prescribed size. -/
abbrev FrameOpen := { U : S.Opens // Nonempty (LocalFrame M n U) }

/-- Choose an actual frame on each trivializing open. -/
def frame (U : FrameOpen M n) : LocalFrame M n U.val :=
  U.property.some

/-- Fixed-rank local freeness supplies a genuine frame near every point. -/
lemma exists_frameOpen (hM : IsLocallyFreeOfRank M (n + 1)) (x : S) :
    ∃ U : FrameOpen M n, x ∈ U.val := by
  obtain ⟨q, hq, hn⟩ := hM
  let := hq
  have hcov : iSup q.X = ⊤ := (_root_.Opens.coversTop_iff S q.X).mp q.coversTop
  have hx : x ∈ iSup q.X := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let a : ULift.{u} (Fin (n + 1)) ≃ (q.generators i).I :=
    Equiv.ulift.trans (hn i).some.symm
  let e : LocalFrame M n (q.X i) :=
    (SheafOfModules.freeFunctor (R := S.ringCatSheaf.over (q.X i))).mapIso
        (Equiv.toIso a) ≪≫
      asIso (q.generators i).π
  exact ⟨⟨q.X i, ⟨e⟩⟩, hi⟩

/-- All trivializing opens, with their actual open-subscheme inclusions. -/
abbrev frameCover (hM : IsLocallyFreeOfRank M (n + 1)) : S.OpenCover where
  I₀ := FrameOpen M n
  X U := U.val.toScheme
  f U := U.val.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun U => inferInstance⟩
    obtain ⟨U, hx⟩ := exists_frameOpen M n hM x
    exact ⟨U, ⟨x, hx⟩, rfl⟩

instance (hM : IsLocallyFreeOfRank M (n + 1)) : Preorder (frameCover M n hM).I₀ :=
  inferInstanceAs (Preorder (FrameOpen M n))

/-- Trivializing opens are a topological basis, since frames restrict. -/
lemma isBasis_frameOpen (hM : IsLocallyFreeOfRank M (n + 1)) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun U : FrameOpen M n => U.val)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨V, hxV⟩ := exists_frameOpen M n hM x
  refine ⟨U ⊓ V.val, ?_, ⟨hx, hxV⟩, inf_le_left⟩
  exact ⟨⟨U ⊓ V.val, ⟨(frame M n V).restrict inf_le_right⟩⟩, rfl⟩

instance (hM : IsLocallyFreeOfRank M (n + 1)) :
    (frameCover M n hM).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
    (by intros; simp [frameCover]) (by
      simpa [frameCover] using isBasis_frameOpen M n hM)

@[simp]
lemma frameCover_trans (hM : IsLocallyFreeOfRank M (n + 1))
    {U V : (frameCover M n hM).I₀} (h : U ⟶ V) :
    (frameCover M n hM).trans h = S.homOfLE (show U.val ≤ V.val from leOfHom h) := by
  apply (cancel_mono V.val.ι).mp
  rw [Scheme.homOfLE_ι]
  exact (frameCover M n hM).trans_map h

/-- The canonical comparison of section rings is natural for inclusions of opens. -/
lemma topIso_inv_naturality {U V : S.Opens} (h : U ≤ V) :
    V.topIso.inv ≫ (S.homOfLE h).appTop =
      S.presheaf.map (homOfLE h).op ≫ U.topIso.inv := by
  exact (S.restrictFunctorΓ.inv.naturality (homOfLE h).op).symm

/-- Transport the coefficient ring from sections on an open to global sections of its scheme. -/
def coordinatesOnOpen (U : S.Opens)
    (e : (Fin (n + 1) → Γ(S, U)) ≃ₗ[Γ(S, U)] (Fin (n + 1) → Γ(S, U))) :
    (Fin (n + 1) → Γ(U.toScheme, ⊤)) ≃ₗ[Γ(U.toScheme, ⊤)]
      (Fin (n + 1) → Γ(U.toScheme, ⊤)) :=
  ProjectiveSpace.coordinateBaseChange n U.topIso.inv.hom e

lemma coordinatesOnOpen_restrict {U V : S.Opens} (h : U ≤ V)
    (e : (Fin (n + 1) → Γ(S, V)) ≃ₗ[Γ(S, V)] (Fin (n + 1) → Γ(S, V))) :
    coordinatePullback n (S.homOfLE h) (coordinatesOnOpen n V e) =
      coordinatesOnOpen n U
        (ProjectiveSpace.coordinateBaseChange n (S.presheaf.map (homOfLE h).op).hom e) := by
  dsimp [coordinatesOnOpen, coordinatePullback]
  rw [← ProjectiveSpace.coordinateBaseChange_comp,
    ← ProjectiveSpace.coordinateBaseChange_comp]
  exact congrArg (fun φ => ProjectiveSpace.coordinateBaseChange n φ e)
    (congrArg (fun f => f.hom) (topIso_inv_naturality h))

/-- The dual-frame transitions give the quotient-convention projective cocycle. -/
def frameCocycle (hM : IsLocallyFreeOfRank M (n + 1)) :
    CoordinateCocycle n (frameCover M n hM) where
  transition {U V} h :=
    coordinatesOnOpen n U.val
      ((frame M n U).dual.change (frame M n V).dual U.val le_rfl
        (show U.val ≤ V.val from leOfHom h))
  transition_id U := by
    dsimp [coordinatesOnOpen]
    rw [LocalFrame.change_self, ProjectiveSpace.coordinateBaseChange_refl]
  transition_comp {U V W} hUV hVW := by
    change coordinatesOnOpen n U.val
        ((frame M n U).dual.change (frame M n W).dual U.val le_rfl
          ((leOfHom hUV).trans (leOfHom hVW))) =
      (coordinatesOnOpen n U.val
        ((frame M n U).dual.change (frame M n V).dual U.val le_rfl (leOfHom hUV))).trans
      (coordinatePullback n ((frameCover M n hM).trans hUV)
        (coordinatesOnOpen n V.val
          ((frame M n V).dual.change (frame M n W).dual V.val le_rfl (leOfHom hVW))))
    rw [frameCover_trans, coordinatesOnOpen_restrict, LocalFrame.change_restrict]
    dsimp [coordinatesOnOpen]
    rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- The actual projective scheme constructed from local frames of a locally free sheaf. -/
def frameBundle (hM : IsLocallyFreeOfRank M (n + 1)) : Scheme.{u} :=
  (frameCocycle M n hM).scheme

namespace FrameBundle

variable {M n} (hM : IsLocallyFreeOfRank M (n + 1))

/-- The structure morphism to the original base scheme. -/
def toBase : frameBundle M n hM ⟶ S :=
  (frameCocycle M n hM).toBase

/-- The projective chart over a trivializing open. -/
def chart (U : FrameOpen M n) :
    RelativeProjectiveSpace U.val.toScheme n ⟶ frameBundle M n hM :=
  (frameCocycle M n hM).chart U

instance (U : FrameOpen M n) : IsOpenImmersion (chart hM U) :=
  inferInstanceAs (IsOpenImmersion ((frameCocycle M n hM).chart U))

@[reassoc (attr := simp)]
lemma chart_toBase (U : FrameOpen M n) :
    chart hM U ≫ toBase hM = RelativeProjectiveSpace.toBase U.val.toScheme n ≫ U.val.ι :=
  (frameCocycle M n hM).chart_toBase U

/-- Every chosen projective chart is Cartesian over its trivializing base open. -/
lemma isPullback_chart (U : FrameOpen M n) :
    IsPullback (RelativeProjectiveSpace.toBase U.val.toScheme n) (chart hM U)
      U.val.ι (toBase hM) :=
  (frameCocycle M n hM).isPullback_chart U

/-- The projective charts cover the constructed scheme. -/
def openCover : (frameBundle M n hM).OpenCover :=
  (frameCocycle M n hM).openCover

@[reassoc (attr := simp)]
lemma transition_chart {U V : FrameOpen M n} (h : U ≤ V) :
    globalLinearAction n
        (coordinatesOnOpen n U.val
          ((frame M n U).dual.change (frame M n V).dual U.val le_rfl h)) ≫
      RelativeProjectiveSpace.map n (S.homOfLE h) ≫ chart hM V = chart hM U := by
  simpa [frameCocycle, chart] using
    (frameCocycle M n hM).transition_chart (homOfLE h)

end FrameBundle

end Langlands.AlgebraicGeometry.ProjectiveBundle
