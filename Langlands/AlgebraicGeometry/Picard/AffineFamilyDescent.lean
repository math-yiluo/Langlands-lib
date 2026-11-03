import Langlands.AlgebraicGeometry.Picard.Groupoid
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof

/-! # Descent of actual Picard families over affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The affine test scheme defined by an algebra over the base ring. -/
def affineBase (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The canonical affine-base arrow associated to a subalgebra. -/
def affineSubalgebraMap (B : Subalgebra R A) :
    affineBase R A ⟶ affineBase R B :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap B A))) (by
    dsimp only [affineBase, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)

namespace PicardGroupoid

set_option backward.isDefEq.respectTransparency false in
/-- An actual Picard family over an affine base descends to a finitely generated
subalgebra containing any prescribed finite set of coefficients. The comparison
is an actual isomorphism in the Picard groupoid after its ordinary pullback. -/
theorem exists_affineFamily_subalgebra
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f]
    (M : LineBundle ((relativeSpace f).obj (affineBase R A))) (s : Finset A) :
    ∃ (B : Subalgebra R A), B.FG ∧ (↑s : Set A) ⊆ B ∧
      ∃ (L : LineBundle ((relativeSpace f).obj (affineBase R B))),
        Nonempty
          ((((relative f).map (affineSubalgebraMap B).op.toLoc).toFunctor.obj
            (Core.mk L)) ≅ Core.mk M) := by
  obtain ⟨B, hB, hs, M₀, hM₀, hdesc⟩ :=
    NoetherianApproximation.lineBundleSubalgebraDescent f
      (pullback.snd (affineBase R A).hom f) (pullback.fst (affineBase R A).hom f)
      (IsPullback.of_hasPullback (affineBase R A).hom f).flip M.obj M.property s
  let q := affineSubalgebraMap B
  let eB := relativeSpaceSymmetry f (affineBase R B)
  let c := (relativeSpace f).map q ≫ eB.hom
  have hc₁ : c ≫ pullback.fst f (affineBase R B).hom =
      pullback.snd (affineBase R A).hom f := by
    dsimp only [c, eB, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, relativeSpace_map_snd]
  have hc₂ : c ≫ pullback.snd f (affineBase R B).hom =
      pullback.fst (affineBase R A).hom f ≫
        Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
    dsimp only [c, eB, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact (relativeProjection f).naturality q
  obtain ⟨e⟩ := hdesc c hc₁ hc₂
  let L : LineBundle ((relativeSpace f).obj (affineBase R B)) :=
    ⟨(Scheme.Modules.pullback eB.hom).obj M₀, hM₀.pullback eB.hom⟩
  refine ⟨B, hB, hs, L, ⟨Core.isoMk (ObjectProperty.isoMk _ ?_)⟩⟩
  exact (Scheme.Modules.pullbackComp ((relativeSpace f).map q) eB.hom).app M₀ ≪≫ e

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
