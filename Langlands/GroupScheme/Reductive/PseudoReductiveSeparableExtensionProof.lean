import Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionStatement
import Langlands.GroupScheme.Reductive.GaloisRadicalDescent
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Mathlib.FieldTheory.IsSepClosed

/-! # Pseudo-reductivity after separable algebraic extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Pseudo-reductivity is preserved by every separable algebraic field extension. -/
theorem IsPseudoReductive.baseChange_of_separableExtension
    (hG : IsPseudoReductive G) :
    IsPseudoReductive
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  refine ⟨inferInstanceAs (Smooth (pullback.snd G.X.hom b)),
    inferInstance, G.connectedSpace_baseChange_of_smooth_affine b, ?_⟩
  let ι : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra K (SeparableClosure k) := ι.toRingHom.toAlgebra
  let c := Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))
  let d := Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure k)))
  have hcomp : d ≫ b = c := by
    dsimp [b, c, d]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => ι.commutes x
  have hL : IsPseudoReductive ((GroupScheme.baseChange c).obj G) :=
    hG.baseChange_galois (K := SeparableClosure k)
  have htotal : HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (d ≫ b)).obj G) := by
    rw [hcomp]
    exact hL.hasTrivialUnipotentRadical
  have hiter : HasTrivialUnipotentRadical
      ((GroupScheme.baseChange d).obj ((GroupScheme.baseChange b).obj G)) :=
    HasTrivialUnipotentRadical.of_iso (baseChangeCompIso b d G).symm htotal
  exact HasTrivialUnipotentRadical.of_fieldExtension hiter

/-- The exact published separable-extension proposition at arbitrary universe `u`. -/
theorem pseudoReductiveSeparableExtension :
    PseudoReductiveSeparableExtensionStatement.{u} := by
  intro k K _ _ _ _ G hG
  exact hG.baseChange_of_separableExtension

end Langlands.GroupScheme
