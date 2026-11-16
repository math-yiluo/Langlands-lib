import Langlands.GroupScheme.Reductive.EtaleLocalMonomorphismImmersion
import Langlands.GroupScheme.Torus.RelativeMonomorphismClosedImmersion

/-! # Monomorphisms from reductive groups to smooth affine groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ReductiveImmersion

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Closed split torus images after affine etale base change follow from
monicity when the target is affine and locally of finite type. -/
theorem closedSplitTorusImages_of_mono
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (f : H ⟶ G) [Mono f.hom.hom.left] :
    ClosedSplitTorusImagesAfterEtaleBaseChange f := by
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  intro R _ b _ I _ i hi
  let Gb := (baseChange b).obj G
  let fb := (baseChange b).map f
  let : IsAffineHom Gb.X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : LocallyOfFiniteType Gb.X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have : Mono fb.hom.hom :=
    (inferInstance : Mono ((Over.pullback b).map f.hom.hom))
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono (i ≫ fb).hom.hom :=
    (inferInstance : Mono (i.hom.hom ≫ fb.hom.hom))
  exact (isSplitTorus_splitTorus I).isClosedSubgroup_of_mono (i ≫ fb)

/-- Every scheme-monic homomorphism from a reductive group to a smooth affine
group over an arbitrary base is an immersion. -/
theorem isImmersion_of_mono (hH : IsReductive H)
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : H ⟶ G) [Mono f.hom.hom.left] : IsImmersion f.hom.hom.left :=
  isImmersion_of_closedSplitTorusImages hH f (closedSplitTorusImages_of_mono f)

variable (hH : IsReductive H) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (f : H ⟶ G) [Mono f.hom.hom.left]

/-- The actual largest open subset of the target in which the reductive
monomorphism is a closed immersion. -/
def immersionOpen : G.X.left.Opens :=
  letI := isImmersion_of_mono hH f
  f.hom.hom.left.coborderRange

/-- The actual closed factor of a reductive monomorphism through its
constructed target open. -/
def closedFactor : H.X.left ⟶ (immersionOpen hH f).toScheme :=
  letI := isImmersion_of_mono hH f
  f.hom.hom.left.liftCoborder

theorem isClosedImmersion_closedFactor : IsClosedImmersion (closedFactor hH f) := by
  let := isImmersion_of_mono hH f
  exact inferInstanceAs (IsClosedImmersion f.hom.hom.left.liftCoborder)

@[reassoc (attr := simp)]
theorem closedFactor_ι : closedFactor hH f ≫ (immersionOpen hH f).ι = f.hom.hom.left := by
  let := isImmersion_of_mono hH f
  exact f.hom.hom.left.liftCoborder_ι

end Langlands.GroupScheme.ReductiveImmersion
