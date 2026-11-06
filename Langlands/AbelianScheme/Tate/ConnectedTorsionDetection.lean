import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.Tate.Integral
import Langlands.AbelianScheme.TorsionFiniteEtaleStatement
import Langlands.AbelianScheme.TorsionFunctor
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof

/-! # Detecting torsion-kernel vanishing at one geometric point -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- Morphisms of finite étale covers of a connected locally noetherian scheme
are determined by their action at one algebraically closed geometric point. -/
theorem hom_ext_of_geometric_fiber
    {S : Scheme.{u}} [IsLocallyNoetherian S] [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {X Y : Cover S} (f g : X ⟶ Y)
    (h : ∀ x : Fiber s X, x ≫ f.hom = x ≫ g.hom) : f = g := by
  let hfin := geometricFiberFinite s
  obtain ⟨hG, hF⟩ := geometricGaloisFiberFunctor s hfin
  let : GaloisCategory (Cover S) := hG
  let : PreGaloisCategory.FiberFunctor (fiberFunctor s hfin) := hF
  apply (fiberFunctor s hfin).map_injective
  ext x
  exact h x

end Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme.Tate

open GroupScheme

/-- If an actual abelian-scheme homomorphism kills all level-`n` points at one
geometric point, it kills the whole scheme kernel of multiplication by `n`. -/
theorem kernel_comp_eq_one_of_levelMap_eq_zero
    (htor : TorsionFiniteEtaleStatement.{u})
    {S : Scheme.{u}} [IsLocallyNoetherian S] [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {A B : AbelianScheme S} (f : A ⟶ B) (n : ℕ)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (hz : ∀ x : GroupScheme.Tate.Level A.toGrp (Over.mk s) n,
      GroupScheme.Tate.levelMap (Over.mk s) (groupHom f) n x = 0) :
    kernelι (multiplication A.toGrp (n : ℤ)) ≫ groupHom f = 1 := by
  let TA := torsion A.toGrp (n : ℤ)
  let TB := torsion B.toGrp (n : ℤ)
  let CA := torsionCover htor A n hn hunit
  let CB := torsionCover htor B n hn hunit
  let a : CA ⟶ CB :=
    ObjectProperty.homMk (torsionMap (groupHom f) (n : ℤ)).hom.hom
  let b : CA ⟶ CB :=
    ObjectProperty.homMk (1 : TA ⟶ TB).hom.hom
  have hab : a = b := by
    apply Langlands.AlgebraicGeometry.FiniteEtale.hom_ext_of_geometric_fiber s a b
    intro x
    change Over.mk s ⟶ TA.X at x
    have hx := hz (GroupScheme.Tate.kernelLevelEquiv A.toGrp (Over.mk s) n
      (Additive.ofMul x))
    have hx' :
        (x ≫ (torsionι A.toGrp (n : ℤ)).hom.hom) ≫ (groupHom f).hom.hom = 1 :=
      congrArg (fun y : GroupScheme.Tate.Level B.toGrp (Over.mk s) n =>
        (Additive.toMul y).val) hx
    apply (cancel_mono (torsionι B.toGrp (n : ℤ)).hom.hom).mp
    change (x ≫ (torsionMap (groupHom f) (n : ℤ)).hom.hom) ≫
        (torsionι B.toGrp (n : ℤ)).hom.hom =
      (x ≫ (1 : TA ⟶ TB).hom.hom) ≫ (torsionι B.toGrp (n : ℤ)).hom.hom
    rw [Category.assoc]
    change x ≫ (torsionMap (groupHom f) (n : ℤ) ≫
      torsionι B.toGrp (n : ℤ)).hom.hom = _
    rw [torsionMap_ι]
    change x ≫ (torsionι A.toGrp (n : ℤ)).hom.hom ≫ (groupHom f).hom.hom =
      (x ≫ (1 : TA.X ⟶ TB.X)) ≫ (torsionι B.toGrp (n : ℤ)).hom.hom
    rw [MonObj.comp_one, MonObj.one_comp]
    simpa only [Category.assoc] using hx'
  have htorzero :
      torsionMap (groupHom f) (n : ℤ) = (1 : TA ⟶ TB) := by
    apply Grp.hom_ext
    exact congrArg (fun k : CA ⟶ CB => k.hom) hab
  change torsionι A.toGrp (n : ℤ) ≫ groupHom f = 1
  rw [← torsionMap_ι, htorzero, MonObj.one_comp]

end Langlands.AbelianScheme.Tate
