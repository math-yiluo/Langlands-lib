/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
open MonoidalCategory Scheme.Modules
/-- Completion comparison for closed immersion pushforward.
Source: Stacks Project, Cohomology of Schemes, equation 0880.
The proof assembles the canonical quotient comparisons into a natural isomorphism
and checks the stated projection equation at every positive level.
(blueprint: lem-weil-pbc-closed-immersion-coherent-formal-equivalence-completion)
-/
theorem closedImmersion_coherentFormal_equivalence_completion {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X] (I : X.IdealSheafData) :
    ∃ θ : ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        Scheme.Modules.pushforward i ⋙ formalCompletionFunctor I ≅
        ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace) ⋙
        formalCompletionFunctor (I.comap i) ⋙
          (Functor.whiskeringRight ℕᵒᵖ Z.Modules X.Modules).obj
            (Scheme.Modules.pushforward i),
      ∀ (G : CoherentModules Z) (n : ℕ),
        formalModuleQuotientπ I (n + 1)
            ((Scheme.Modules.pushforward i).obj G.obj) ≫
          (θ.hom.app G).app (op n) =
        (Scheme.Modules.pushforward i).map
          (formalModuleQuotientπ (I.comap i) (n + 1) G.obj) := by
  classical
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have hqc (G : CoherentModules Z) : G.obj.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Z G.obj).mp
      G.property |>.1
  let (G : CoherentModules Z) : G.obj.IsQuasicoherent := hqc G
  obtain ⟨_, _, _, ρ, hπ, hnat, hlevel⟩ :=
    Scheme.closedImmersion_pushforward_idealPowers i I
  let e (G : CoherentModules Z) :
      formalCompletionSystem I ((Scheme.Modules.pushforward i).obj G.obj) ≅
        formalCompletionSystem (I.comap i) G.obj ⋙ Scheme.Modules.pushforward i :=
    NatIso.ofComponents (fun n ↦ ρ G.obj (n.unop + 1) (Nat.le_add_left 1 n.unop))
      (fun {m n} f ↦ by
        exact hlevel G.obj (m.unop + 1) (n.unop + 1)
          (Nat.add_le_add_right (leOfHom f.unop) 1) (Nat.le_add_left 1 n.unop))
  refine ⟨NatIso.ofComponents e (fun {G H} f ↦ ?_), ?_⟩
  · apply NatTrans.ext
    funext n
    exact hnat G.obj H.obj f.hom (n.unop + 1) (Nat.le_add_left 1 n.unop)
  · intro G n
    exact hπ G.obj (n + 1) (Nat.le_add_left 1 n)

end AlgebraicGeometry
