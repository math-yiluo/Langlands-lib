import Langlands.GroupScheme.Torus.FieldTransporterDescent
import Langlands.GroupScheme.LocalCosetDescent

/-! # Zariski local descent of transporters under a split torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.PointwiseSchemeAction

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  {i₁ i₂ : T.toGrp ⟶ G} {U V : Over S}

/-- The all-test transporter condition descends along any fpqc refinement of its domain. -/
theorem isTransporter_of_fpqc_restriction (p : V ⟶ U)
    [Flat p.left] [Surjective p.left] [QuasiCompact p.left]
    {n : U ⟶ G.X} (h : IsTransporter i₁ i₂ (p ≫ n)) :
    IsTransporter i₁ i₂ n := by
  intro Z a t
  let W : Over S := Over.mk (pullback.snd p.left a.left ≫ Z.hom)
  let e : W ⟶ Z := Over.homMk (pullback.snd p.left a.left)
  let c : W ⟶ V := Over.homMk (pullback.fst p.left a.left) (by
    rw [← Over.w p, ← Category.assoc, pullback.condition, Category.assoc, Over.w a]
    rfl)
  have : Epi e.left := inferInstanceAs (Epi (pullback.snd p.left a.left))
  have : Epi e := Over.epi_of_epi_left e
  have hc : c ≫ p = e ≫ a := Over.OverMorphism.ext pullback.condition
  apply (cancel_epi e).mp
  simp only [MonObj.comp_mul, ← Category.assoc]
  simpa only [← Category.assoc, hc] using h W c (e ≫ t)

/-- A transporter with self-centralizing split source has local representatives over
any affine faithfully flat cover. The representatives remain all-test transporters. -/
theorem exists_local_transporter_of_cover [Mono i₂.hom.hom]
    [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (hT : IsSplitTorus T.toGrp) (g : U ⟶ G.X)
    (hg : IsTransporter i₁ i₂ g)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂) (s : S) :
    ∃ W : S.Opens, s ∈ W ∧ ∃ n : Over.mk W.ι ⟶ G.X,
      IsTransporter i₁ i₂ n := by
  have hval : ∀ {Z : Over S} (a b : Z ⟶ U), ∃ t : Z ⟶ T.X,
      t ≫ i₂.hom.hom = (Cocycle.coboundary g⁻¹).toFun a b :=
    fun a b => hg.coboundary_inv_mem_range hC a b
  let ξ := (Cocycle.coboundary g⁻¹).lift i₂ hval
  have hξ : ξ.IsZariskiLocallyTrivial :=
    fun y => Cocycle.nonempty_localTrivialization_of_isSplitTorus hT ξ y
  obtain ⟨W, hs, n, f, hnf⟩ :=
    LocalCosetDescent.hasLocalCosetRepresentatives i₂ g hval hξ s
  let UW : Over S := Over.mk ((U.hom ⁻¹ᵁ W).ι ≫ U.hom)
  let r : UW ⟶ U := Over.homMk (U.hom ⁻¹ᵁ W).ι
  let q : UW ⟶ Over.mk W.ι :=
    Over.homMk (U.hom ∣_ W) (morphismRestrict_ι U.hom W)
  have : Flat q.left := inferInstanceAs (Flat (U.hom ∣_ W))
  have : Surjective q.left := inferInstanceAs (Surjective (U.hom ∣_ W))
  have : QuasiCompact q.left := inferInstanceAs (QuasiCompact (U.hom ∣_ W))
  refine ⟨W, hs, n, isTransporter_of_fpqc_restriction q ?_⟩
  rw [← hnf]
  exact correctedTransporter_isTransporter (hg.restrict r) hC f

/-- An actual transporter on an open neighbourhood of a specified base point. -/
structure LocalTransporterData (i₁ i₂ : T.toGrp ⟶ G) (s : S) where
  openSet : S.Opens
  mem_openSet : s ∈ openSet
  point : Over.mk openSet.ι ⟶ G.X
  transporter : IsTransporter i₁ i₂ point

/-- Choose the local transporter supplied by affine faithfully flat descent. -/
def localTransporterOfCover [Mono i₂.hom.hom]
    [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (hT : IsSplitTorus T.toGrp) (g : U ⟶ G.X)
    (hg : IsTransporter i₁ i₂ g)
    (hC : torusCentralizer i₂ = SubgroupFunctor.range i₂) (s : S) :
    LocalTransporterData i₁ i₂ s := by
  apply Classical.choice
  obtain ⟨W, hs, n, hn⟩ := exists_local_transporter_of_cover hT g hg hC s
  exact ⟨⟨W, hs, n, hn⟩⟩

end Langlands.GroupScheme.PointwiseSchemeAction
