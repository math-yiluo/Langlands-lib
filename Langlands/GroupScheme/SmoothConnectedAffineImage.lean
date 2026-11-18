import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.ImageGenerationSourceTransport
import Langlands.GroupScheme.SmoothFieldComponent
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.AlgebraicGeometry.ClosedFibreOpenIntegrality
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Actual affine images of smooth connected field groups -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneratedImage

variable {S : Scheme.{u}} {G A : GroupScheme S} {V : Over S}
  (p : V ⟶ G.X) [IsSchemeTheoreticallyDominant p.left]
  (f : G ⟶ A) (D : GeneratedImage (p ≫ f.hom.hom))

/-- The actual generated-image factor of a group homomorphism is a
homomorphism, by cancellation of the monomorphic closed inclusion. -/
instance sourceFactor_isMonHom : IsMonHom (D.sourceFactor p f.hom.hom) where
  one_hom := by
    have : Mono D.inclusion.hom.hom := D.represents.1
    apply (cancel_mono D.inclusion.hom.hom).mp
    rw [Category.assoc, D.sourceFactor_comp, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    have : Mono D.inclusion.hom.hom := D.represents.1
    apply (cancel_mono D.inclusion.hom.hom).mp
    rw [Category.assoc, D.sourceFactor_comp, IsMonHom.mul_hom, Category.assoc,
      IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, D.sourceFactor_comp]

/-- The descended generated-image factor, as an actual group homomorphism. -/
def sourceHom : G ⟶ D.group := Grp.homMk (D.sourceFactor p f.hom.hom)

@[reassoc]
lemma sourceHom_comp : D.sourceHom p f ≫ D.inclusion = f :=
  Grp.hom_ext _ _ (D.sourceFactor_comp p f.hom.hom)

/-- A dominant ordered power of a generated-image factor forces dominance
of the factor itself, because it is an actual homomorphism. -/
lemma sourceHom_isDominant (n : ℕ) (hn : IsDominant (D.powerMap n).left) :
    IsDominant (D.sourceHom p f).hom.hom.left := by
  have hd := D.sourceFactor_power_isDominant p f.hom.hom n hn
  have he : orderedPowerMap (D.sourceFactor p f.hom.hom) n =
      orderedPowerMap (𝟙 G.X) n ≫ (D.sourceHom p f).hom.hom := by
    rw [orderedPowerMap_comp]
    simp only [Category.id_comp]
    rfl
  rw [he, Over.comp_left] at hd
  have : IsDominant ((orderedPowerMap (𝟙 G.X) n).left ≫
      (D.sourceHom p f).hom.hom.left) := hd
  exact IsDominant.of_comp (orderedPowerMap (𝟙 G.X) n).left _

end GeneratedImage

/-- A smooth connected affine actual image, with a closed inclusion and an
actual faithfully flat quasi-compact factorization of the original map. -/
structure SmoothConnectedAffineImage {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ A) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ A
  projection : G ⟶ group
  comp : projection ≫ inclusion = f
  smooth : Smooth group.X.hom
  connected : ConnectedSpace group.X.left
  affine : IsAffine group.X.left
  closed : IsClosedImmersion inclusion.hom.hom.left
  flat : Flat projection.hom.hom.left
  surjective : Surjective projection.hom.hom.left
  quasiCompact : QuasiCompact projection.hom.hom.left

/-- Over an algebraically closed field, every homomorphism from a smooth
connected group into a smooth affine group has an actual smooth connected
affine image, without an affine-source hypothesis. -/
def smoothConnectedAffineImage {k : Type u} [Field k] [IsAlgClosed k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [Smooth A.X.hom] [IsAffineHom A.X.hom]
    (f : G ⟶ A) : SmoothConnectedAffineImage f := Classical.choice (by
  have : QuasiCompact G.X.hom := quasiCompact_of_smooth_connected G
  have : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  have : GeometricallyIntegral G.X.hom :=
    Langlands.AbelianScheme.smoothGeometricIntegrality k G.X.left G.X.hom
      inferInstance inferInstance
  have : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let z : G.X.left := η[G.X].left (IsLocalRing.closedPoint k)
  obtain ⟨U, hUa, hzU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : G.X.left.Opens)) (show z ∈ (⊤ : G.X.left.Opens) from trivial)
  let V : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ G.X.hom)
  let p : V ⟶ G.X := Over.homMk U.ι
  have : IsAffine V.left := hUa
  have : IsAffineHom V.hom := inferInstance
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ G.X.hom))
  have : Surjective (U.ι ≫ G.X.hom) :=
    ⟨fun y => ⟨⟨z, hzU⟩, Subsingleton.elim _ _⟩⟩
  have hVi : GeometricallyIntegral V.hom :=
    Langlands.AlgebraicGeometry.geometricallyIntegral_open_of_surjective G.X.hom U
  have : IsOpenImmersion p.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsDominant p.left := Opens.isDominant_ι (U.isOpen.dense ⟨z, hzU⟩)
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hr : Set.range η[G.X].left ⊆ Set.range p.left := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst x
    exact ⟨⟨z, hzU⟩, rfl⟩
  let v₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V :=
    FiniteEtaleImage.liftOver p η[G.X] hr
  have hv₀ : v₀ ≫ (p ≫ f.hom.hom) = 1 := by
    rw [← Category.assoc, FiniteEtaleImage.liftOver_fac, IsMonHom.one_hom]
    exact MonObj.one_eq_one _
  obtain ⟨D, hs, ha, hc, n, hn, hd⟩ := ImageGeneration.pointedImageGeneration k A
    inferInstance inferInstance V inferInstance inferInstance hVi v₀ (p ≫ f.hom.hom) hv₀
  have : Smooth D.group.X.hom := hs
  have : IsAffineHom D.group.X.hom := ha
  have : GeometricallyConnected D.group.X.hom := hc
  have : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  have : IsReduced D.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k D.group.X.left D.group.X.hom
  have : IsDominant (D.sourceHom p f).hom.hom.left := D.sourceHom_isDominant p f n hd
  obtain ⟨hqf, hqs, hqc⟩ := DominantHomFlat.flat_surjective (D.sourceHom p f)
  exact ⟨{
    group := D.group
    inclusion := D.inclusion
    projection := D.sourceHom p f
    comp := D.sourceHom_comp p f
    smooth := hs
    connected := inferInstance
    affine := isAffine_of_isAffineHom D.group.X.hom
    closed := D.closed
    flat := hqf
    surjective := hqs
    quasiCompact := hqc }⟩)

end Langlands.GroupScheme
