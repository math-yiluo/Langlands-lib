import Langlands.AlgebraicGeometry.FiniteEtale.GeometricGaloisFiberFunctorProof
import Mathlib.CategoryTheory.Galois.Full

/-! # A fixed geometric lift is the value of a section -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- A point of a finite étale fibre that is fixed by the pointed fundamental
group is the value of a section of the supplied cover. -/
def sectionOfFixedGeometricLift {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y)) (Y : Cover S) (x : Fiber s Y)
    (hx : ∀ g : FundamentalGroup s hs, g • x = x) :
    {σ : S ⟶ Y.obj.left // σ ≫ Y.obj.hom = 𝟙 _ ∧ s ≫ σ = x.left} := by
  let hG := geometricGaloisFiberFunctor s hs
  letI : GaloisCategory (Cover S) := Classical.choose hG
  letI : PreGaloisCategory.FiberFunctor (fiberFunctor s hs) := Classical.choose_spec hG
  let F := PreGaloisCategory.functorToAction (fiberFunctor s hs)
  let I : Cover S := cover (𝟙 S)
  let t : Fiber s I := Over.homMk s (by simp [I, cover])
  let ψ : F.obj I ⟶ F.obj Y :=
    { hom := FintypeCat.homMk (fun _ => x)
      comm := fun g => by
        ext a
        exact (hx g).symm }
  let f : I ⟶ Y := F.preimage ψ
  have hfx : (fiberFunctor s hs).map f t = x := by
    have he : F.map f = ψ := F.map_preimage ψ
    exact congrArg (fun a : F.obj I ⟶ F.obj Y => a.hom t) he
  exact ⟨f.hom.left, Over.w f.hom, congrArg (fun a : Fiber s Y => a.left) hfx⟩

end Langlands.AlgebraicGeometry.FiniteEtale
