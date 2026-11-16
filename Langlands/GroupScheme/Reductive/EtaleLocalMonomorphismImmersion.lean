import Langlands.AlgebraicGeometry.ImmersionEtaleLocal
import Langlands.GroupScheme.Reductive.MonomorphismImmersion
import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof

/-! # A reductive immersion criterion from closed split torus images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace BaseImmersion

/-- Immersion of a morphism over a base can be checked after an étale base
neighbourhood of each base point. -/
theorem of_etale_base_neighbourhoods {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (b : U ⟶ S),
      Etale b ∧ s ∈ Set.range b ∧ IsImmersion ((Over.pullback b).map f).left) :
    IsImmersion f.left := by
  apply Langlands.AlgebraicGeometry.ImmersionEtaleLocal.isImmersion_of_etale_neighbourhoods
  intro y
  obtain ⟨U, b, hb, hy, hf⟩ := h (Y.hom y)
  let : Etale b := hb
  let p := pullback.fst Y.hom b
  have hp := (BaseClosedImmersion.baseChange_isPullback b f).flip
  refine ⟨pullback Y.hom b, p, inferInstance, ?_, ?_⟩
  · change y ∈ Set.range (pullback.fst Y.hom b)
    rw [Scheme.Pullback.range_fst]
    exact hy
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)
      hp.isoPullback.hom, hp.isoPullback_hom_snd]
    exact hf

end BaseImmersion

namespace ReductiveImmersion

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Every closed coordinate split torus in the source, after any affine étale
base change, has closed composite with the homomorphism. -/
def ClosedSplitTorusImagesAfterEtaleBaseChange (f : H ⟶ G) : Prop :=
  ∀ (R : Type u) [CommRing R] (b : Spec (CommRingCat.of R) ⟶ S) [Etale b]
    (I : Type u) [Fintype I]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ (baseChange b).obj H),
    IsClosedSubgroup i → IsClosedSubgroup (i ≫ (baseChange b).map f)

/-- A monomorphism from a reductive group to a smooth affine group is an
immersion if its split torus images after affine étale base change are closed.
No global splitting or noetherian hypothesis is required. -/
theorem isImmersion_of_closedSplitTorusImages (hH : IsReductive H)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (f : H ⟶ G)
    [Mono f.hom.hom.left] (hc : ClosedSplitTorusImagesAfterEtaleBaseChange f) :
    IsImmersion f.hom.hom.left := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  apply BaseImmersion.of_etale_base_neighbourhoods f.hom.hom
  intro s
  obtain ⟨R, hR, b, hb, hx, I, hI, i, hi, hmax, J, P, hP, _⟩ :=
    etaleLocalSplitReductive S H hH s
  let : CommRing R := hR
  let : Fintype I := hI
  let : Etale b := hb
  refine ⟨Spec (CommRingCat.of R), b, hb, hx, ?_⟩
  let Hb := (baseChange b).obj H
  let Gb := (baseChange b).obj G
  let fb := (baseChange b).map f
  have hHb : IsReductive Hb := hH.baseChange b
  let : IsAffineHom Hb.X.hom := hHb.isAffineHom
  let : Smooth Gb.X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom Gb.X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have : Mono fb.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map f.hom.hom))
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact AffineRegularBorel.isImmersion_of_isClosedSubgroup_torus_comp
    i P hP hHb hmax fb (hc R b I i hi)

end ReductiveImmersion

end Langlands.GroupScheme
