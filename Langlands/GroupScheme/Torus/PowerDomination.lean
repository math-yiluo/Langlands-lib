import Langlands.GroupScheme.ImageGenerationProducts
import Langlands.GroupScheme.Torus.Products

/-! # A dominant map from a finite power of a torus gives one from a torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}}

/-- The underlying scheme of the group-scheme product of `n` copies of `P`
maps to the scheme-level finite power by the coordinate projections. -/
def piFinitePowerHom (P : GroupScheme B) (n : ℕ) :
    (GroupScheme.pi fun _ : ULift.{u} (Fin n) => P).X ⟶ finitePower P.X n :=
  Pi.lift fun l => (Pi.π (fun _ : ULift.{u} (Fin n) => P) (ULift.up l)).hom.hom

/-- A section of `piFinitePowerHom`, given by the universal property of the
group-scheme product on its underlying scheme. -/
def finitePowerPiHom (P : GroupScheme B) (n : ℕ) :
    finitePower P.X n ⟶ (GroupScheme.pi fun _ : ULift.{u} (Fin n) => P).X :=
  (piPointsEquiv (fun _ : ULift.{u} (Fin n) => P) (finitePower P.X n)).symm
    fun l => Pi.π (fun _ : Fin n => P.X) l.down

theorem finitePowerPiHom_comp (P : GroupScheme B) (n : ℕ) :
    finitePowerPiHom P n ≫ piFinitePowerHom P n = 𝟙 (finitePower P.X n) := by
  apply Pi.hom_ext
  intro l
  rw [Category.assoc, piFinitePowerHom, Pi.lift_comp_π, finitePowerPiHom,
    piPointsEquiv_symm_π, Category.id_comp]

variable {k : Type u} [Field k]

/-- If a finite power of a torus maps to `X` with dense range, then some torus
maps to `X` with dense range. -/
theorem exists_isTorus_dense_of_finitePower {P : GroupScheme (Spec (CommRingCat.of k))}
    (hP : IsTorus P) {X : Over (Spec (CommRingCat.of k))} (n : ℕ)
    (g : finitePower P.X n ⟶ X) (hg : Dense (Set.range g.left)) :
    ∃ (T : GroupScheme (Spec (CommRingCat.of k))) (f : T.X ⟶ X),
      IsTorus T ∧ Dense (Set.range f.left) := by
  refine ⟨GroupScheme.pi fun _ : ULift.{u} (Fin n) => P, piFinitePowerHom P n ≫ g,
    IsTorus.pi _ fun _ => hP, hg.mono ?_⟩
  rintro _ ⟨x, rfl⟩
  refine ⟨(finitePowerPiHom P n).left x, ?_⟩
  have h := congrArg (fun h => (h ≫ g).left x) (finitePowerPiHom_comp P n)
  simpa only [Category.assoc, Category.id_comp, Over.comp_left,
    Scheme.Hom.comp_apply] using h

end Langlands.GroupScheme
