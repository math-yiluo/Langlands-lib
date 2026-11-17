import Langlands.GroupScheme.Reductive.TitsKernelIndexChoice
import Langlands.GroupScheme.Derived.IsomorphismFunctoriality
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.CenterMovingAutomorphisms

/-! # Actual anisotropic-kernel automorphisms from normalizing points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} (a : d.AnisotropicKernelIndex)

/-- Ambient conjugation by a normalizing point restricts to the supplied
actual centralizer of the distinguished maximal split torus. -/
def normalizerCentralizerIso (n : normalizerPoints d.splitInclusion) :
    a.centralizer ≅ a.centralizer :=
  a.represents.isoOfComap a.represents (G.innerIso n)
    (torusCentralizer_comap_innerIso_normalizer d.splitInclusion n)

@[reassoc]
theorem normalizerCentralizerIso_hom_comp (n : normalizerPoints d.splitInclusion) :
    (a.normalizerCentralizerIso n).hom ≫ a.inclusion =
      a.inclusion ≫ (G.innerIso n).hom :=
  a.represents.isoOfComap_hom_comp a.represents (G.innerIso n)
    (torusCentralizer_comap_innerIso_normalizer d.splitInclusion n)

@[reassoc]
theorem normalizerCentralizerIso_inv_comp (n : normalizerPoints d.splitInclusion) :
    (a.normalizerCentralizerIso n).inv ≫ a.inclusion =
      a.inclusion ≫ (G.innerIso n).inv :=
  a.represents.isoOfComap_inv_comp a.represents (G.innerIso n)
    (torusCentralizer_comap_innerIso_normalizer d.splitInclusion n)

/-- The actual automorphism induced by a normalizing point on the supplied
anisotropic kernel, the derived group of the actual torus centralizer. -/
def normalizerKernelIso (n : normalizerPoints d.splitInclusion) : a.kernel ≅ a.kernel :=
  a.isDerived.mapIso a.isDerived (a.normalizerCentralizerIso n)

@[reassoc]
theorem normalizerKernelIso_hom_comp (n : normalizerPoints d.splitInclusion) :
    (a.normalizerKernelIso n).hom ≫ (a.derived ≫ a.inclusion) =
      (a.derived ≫ a.inclusion) ≫ (G.innerIso n).hom := by
  rw [normalizerKernelIso, ← Category.assoc, IsDerivedSubgroup.mapIso_hom_comp,
    Category.assoc, normalizerCentralizerIso_hom_comp, Category.assoc]

@[reassoc]
theorem normalizerKernelIso_inv_comp (n : normalizerPoints d.splitInclusion) :
    (a.normalizerKernelIso n).inv ≫ (a.derived ≫ a.inclusion) =
      (a.derived ≫ a.inclusion) ≫ (G.innerIso n).inv := by
  rw [normalizerKernelIso, ← Category.assoc, IsDerivedSubgroup.mapIso_inv_comp,
    Category.assoc, normalizerCentralizerIso_inv_comp, Category.assoc]

/-- On every test scheme the induced kernel automorphism is ambient
conjugation after the actual kernel inclusion. -/
theorem normalizerKernelIso_hom_points (n : normalizerPoints d.splitInclusion)
    {U : Over (Spec (CommRingCat.of k))} (z : U ⟶ a.kernel.X) :
    (z ≫ (a.normalizerKernelIso n).hom.hom.hom) ≫
        (a.derived ≫ a.inclusion).hom.hom =
      G.constantPoint n U * (z ≫ (a.derived ≫ a.inclusion).hom.hom) *
        (G.constantPoint n U)⁻¹ := by
  have h :
      (z ≫ (a.normalizerKernelIso n).hom.hom.hom) ≫
          (a.derived ≫ a.inclusion).hom.hom =
        (z ≫ (a.derived ≫ a.inclusion).hom.hom) ≫ (G.innerIso n).hom.hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => z ≫ f.hom.hom) (a.normalizerKernelIso_hom_comp n)
  exact h.trans (G.comp_innerIso_hom n U _)

/-- Fixation of the full kernel centre is exactly fixation of its images
under ambient conjugation, tested over all schemes. -/
theorem normalizerKernelIso_fixesCenter_iff (n : normalizerPoints d.splitInclusion) :
    AutomorphismFixesCenter (a.normalizerKernelIso n) ↔
      ∀ (U : Over (Spec (CommRingCat.of k))) (z : U ⟶ a.kernel.X),
        z ∈ (center a.kernel).carrier U →
          G.constantPoint n U * (z ≫ (a.derived ≫ a.inclusion).hom.hom) *
            (G.constantPoint n U)⁻¹ = z ≫ (a.derived ≫ a.inclusion).hom.hom := by
  constructor
  · intro hf U z hz
    rw [← a.normalizerKernelIso_hom_points n z, hf U z hz]
  · intro h U z hz
    apply a.isDerived.isRepresentedBy.1.right_cancellation
    apply a.represents.1.right_cancellation
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      (a.normalizerKernelIso_hom_points n z).trans (h U z hz)

/-- A single central test point moved by ambient conjugation supplies an
actual centre-moving automorphism of the supplied anisotropic kernel. -/
theorem hasCenterMovingAutomorphism_of_normalizer_centerWitness
    (n : normalizerPoints d.splitInclusion)
    {U : Over (Spec (CommRingCat.of k))} {z : U ⟶ a.kernel.X}
    (hz : z ∈ (center a.kernel).carrier U)
    (hmove : G.constantPoint n U * (z ≫ (a.derived ≫ a.inclusion).hom.hom) *
      (G.constantPoint n U)⁻¹ ≠ z ≫ (a.derived ≫ a.inclusion).hom.hom) :
    HasCenterMovingAutomorphism a.kernel :=
  ⟨a.normalizerKernelIso n,
    fun hf => hmove ((a.normalizerKernelIso_fixesCenter_iff n).mp hf U z hz)⟩

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
