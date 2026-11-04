import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscentStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Ascent along algebraic extensions of fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [Algebra.IsAlgebraic k K]
variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Geometric radical triviality persists along an algebraic extension. -/
theorem IsConnectedReductive.geometricRadical_baseChange_of_algebraicExtension
    (hG : IsConnectedReductive G) :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (toAlgebraicClosure K)).obj
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let r := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))
  let e := IsAlgClosure.equiv k (AlgebraicClosure K) (AlgebraicClosure k)
  let d := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hr : toAlgebraicClosure K ≫ b = r := by
    dsimp [b, r, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq k K (AlgebraicClosure K)]
  have hd : d ≫ toAlgebraicClosure k = r := by
    dsimp [d, r, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (RingHom.ext fun x => e.symm.commutes x)
  have hD := hG.hasTrivialGeometricUnipotentRadical.baseChange_of_bijective
    e.symm.toRingHom e.symm.bijective
  have hR : HasTrivialUnipotentRadical ((GroupScheme.baseChange r).obj G) :=
    hD.of_iso (Descent.pullbackComparison (toAlgebraicClosure k) d r hd G).symm
  exact hR.of_iso (Descent.pullbackComparison b (toAlgebraicClosure K) r hr G)

/-- Connected reductivity persists along an algebraic extension of fields. -/
theorem IsConnectedReductive.baseChange_of_algebraicExtension
    (hG : IsConnectedReductive G) :
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  exact ⟨inferInstanceAs (Smooth (pullback.snd G.X.hom b)),
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b)),
    G.connectedSpace_baseChange_of_smooth_affine b,
    hG.geometricRadical_baseChange_of_algebraicExtension⟩

/-- Semisimplicity persists along an algebraic extension of fields. -/
theorem IsSemisimple.baseChange_of_algebraicExtension
    (hG : IsSemisimple G) :
    IsSemisimple
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) :=
  ⟨hG.isConnectedReductive.baseChange_of_algebraicExtension,
    hG.hasFiniteCenter.baseChange _⟩

/-- Both algebraic-extension ascent assertions, with exactly the published target type. -/
theorem algebraicExtensionAscent : AlgebraicExtensionAscentStatement.{u} :=
  ⟨fun _ _ _ _ _ _ _ hG => hG.baseChange_of_algebraicExtension,
    fun _ _ _ _ _ _ _ hG => hG.baseChange_of_algebraicExtension⟩

end Langlands.GroupScheme
