import Langlands.GroupScheme.RelativeUnipotent.NaturalModuleTransformations
import Langlands.GroupScheme.RelativeUnipotent.DisjointCoverSections

/-! # Actual sheaf-map reconstruction on disjoint finite-free presentations -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.NaturalModuleTransformations

variable {S : Scheme.{u}} {M N : S.Modules}

namespace Transformation

/-- Actual module pullback agrees with base change of its all-test action. -/
lemma baseChange_ofHom_apply (f : M ⟶ N) {X : Scheme.{u}} (b : X ⟶ S)
    (T : Over X) (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj
      ((Scheme.Modules.pullback b).obj M))) :
    ((ofHom f).baseChange b).app T x =
      ((Scheme.Modules.pullback T.hom).map ((Scheme.Modules.pullback b).map f)).app ⊤ x := by
  apply (baseChangeLinearEquiv b N T).injective
  change (baseChangeLinearEquiv b N T)
      ((baseChangeLinearEquiv b N T).symm
        (((Scheme.Modules.pullback ((Over.map b).obj T).hom).map f).app ⊤
          (baseChangeLinearEquiv b M T x))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun g => g.app ⊤ x)
    ((Scheme.Modules.pullbackComp T.hom b).hom.naturality f).symm

/-- A chosen actual free presentation suffices for reconstruction. -/
def reconstructIsoFree {n : ℕ} (C : Transformation M N)
    (e : M ≅ freeBundle S n) : M ⟶ N :=
  e.hom ≫ ((ofHom e.inv).comp C).reconstructFree

/-- Reconstruction through an actual free isomorphism retains all-test action. -/
lemma reconstructIsoFree_apply {n : ℕ} (C : Transformation M N)
    (e : M ≅ freeBundle S n) (T : Over S)
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    ((Scheme.Modules.pullback T.hom).map (C.reconstructIsoFree e)).app ⊤ x =
      C.app T x := by
  rw [reconstructIsoFree, Functor.map_comp,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, reconstructFree_apply]
  change C.app T (((Scheme.Modules.pullback T.hom).map e.inv).app ⊤
    (((Scheme.Modules.pullback T.hom).map e.hom).app ⊤ x)) = _
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
  rfl

end Transformation

/-- A source module with its actual free pieces on a disjoint open cover.
The ranks of different pieces are independent. -/
structure DisjointFreePresentation (M : S.Modules) where
  cover : S.OpenCover.{u}
  disjoint : DisjointCoverGluing.IsDisjoint cover
  rank : cover.I₀ → ℕ
  pieceIso : ∀ i, (Scheme.Modules.pullback (cover.f i)).obj M ≅
    freeBundle (cover.X i) (rank i)

namespace DisjointFreePresentation

variable (P : DisjointFreePresentation M)

/-- Arbitrary pullback preserves the actual disjoint free presentation. -/
def baseChange {X : Scheme.{u}} (b : X ⟶ S) :
    DisjointFreePresentation ((Scheme.Modules.pullback b).obj M) where
  cover := P.cover.pullback₁ b
  disjoint := by
    intro i j hij
    have := P.disjoint i j hij
    exact Function.isEmpty
      (pullback.map (pullback.fst b (P.cover.f i))
        (pullback.fst b (P.cover.f j)) (P.cover.f i) (P.cover.f j)
        (pullback.snd b (P.cover.f i)) (pullback.snd b (P.cover.f j))
        b pullback.condition pullback.condition)
  rank := P.rank
  pieceIso i :=
    squarePullbackIso (P.cover.f i) (pullback.fst b (P.cover.f i))
        (pullback.snd b (P.cover.f i)) b pullback.condition M ≪≫
      (Scheme.Modules.pullback (pullback.snd b (P.cover.f i))).mapIso (P.pieceIso i) ≪≫
        freePullbackIso (pullback.snd b (P.cover.f i)) (ULift.{u} (Fin (P.rank i)))

include P in
/-- The all-test section action detects actual morphisms out of the source. -/
lemma hom_ext (f g : M ⟶ N)
    (h : ∀ (T : Over S) (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)),
      ((Scheme.Modules.pullback T.hom).map f).app ⊤ x =
        ((Scheme.Modules.pullback T.hom).map g).app ⊤ x) : f = g := by
  apply DisjointCoverSections.hom_ext P.cover P.disjoint
  intro i
  apply (cancel_epi (P.pieceIso i).inv).mp
  apply FreeBundleMatrices.hom_ext
  intro j
  exact h (Over.mk (P.cover.f i))
    ((P.pieceIso i).inv.app ⊤ (FreeBundleMatrices.generator (P.cover.X i) (P.rank i) j))

/-- Each actual free piece reconstructs the corresponding original local map. -/
def pieceHom (C : Transformation M N) (i : P.cover.I₀) :
    (Scheme.Modules.pullback (P.cover.f i)).obj M ⟶
      (Scheme.Modules.pullback (P.cover.f i)).obj N :=
  (C.baseChange (P.cover.f i)).reconstructIsoFree (P.pieceIso i)

/-- Actual disjoint-cover gluing constructs the global original module map. -/
def reconstruct (C : Transformation M N) : M ⟶ N :=
  (DisjointCoverSections.existsUnique_hom P.cover P.disjoint M N (P.pieceHom C)).choose

/-- The reconstructed map restricts to the prescribed original free-piece maps. -/
lemma reconstruct_piece (C : Transformation M N) (i : P.cover.I₀) :
    (Scheme.Modules.pullback (P.cover.f i)).map (P.reconstruct C) = P.pieceHom C i :=
  (DisjointCoverSections.existsUnique_hom P.cover P.disjoint M N (P.pieceHom C)).choose_spec.1 i

/-- Restricting a natural transformation to the original cover detects its
action on every section of every test. -/
lemma agree_of_baseChange (C D : Transformation M N)
    (h : ∀ i (T : Over (P.cover.X i)) (x),
      (C.baseChange (P.cover.f i)).app T x =
        (D.baseChange (P.cover.f i)).app T x)
    (T : Over S) (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    C.app T x = D.app T x := by
  apply DisjointCoverSections.restriction_injective
    (P.baseChange T.hom).cover (P.baseChange T.hom).disjoint
      ((Scheme.Modules.pullback T.hom).obj N)
  funext i
  let W : Over (P.cover.X i) := Over.mk (pullback.snd T.hom (P.cover.f i))
  let V : Over S := (Over.map (P.cover.f i)).obj W
  let a : V ⟶ T := Over.homMk (pullback.fst T.hom (P.cover.f i)) pullback.condition
  have H := congrArg (baseChangeSectionEquiv (P.cover.f i) N W)
    (h i W ((baseChangeSectionEquiv (P.cover.f i) M W).symm
      (sectionPullback M a x)))
  simp only [Transformation.baseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    baseChangeLinearEquiv_apply, baseChangeLinearEquiv_symm_apply,
    AddEquiv.apply_symm_apply] at H
  rw [C.natural, D.natural] at H
  exact (ConcreteCategory.bijective_of_isIso
    ((compIso a.left T.hom V.hom (Over.w a) N).hom.app ⊤)).injective H

/-- The reconstructed actual sheaf map recovers the original transformation on
every scheme test, including tests meeting several rank components. -/
lemma reconstruct_apply (C : Transformation M N) (T : Over S)
    (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    ((Scheme.Modules.pullback T.hom).map (P.reconstruct C)).app ⊤ x =
      C.app T x := by
  apply P.agree_of_baseChange (Transformation.ofHom (P.reconstruct C)) C
  intro i W s
  rw [Transformation.baseChange_ofHom_apply, P.reconstruct_piece]
  exact (C.baseChange (P.cover.f i)).reconstructIsoFree_apply (P.pieceIso i) W s

/-- The reconstructed module morphism is uniquely determined by the actual
natural transformation on all tests. -/
lemma reconstruct_unique (C : Transformation M N) (f : M ⟶ N)
    (h : ∀ (T : Over S) (x : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)),
      ((Scheme.Modules.pullback T.hom).map f).app ⊤ x = C.app T x) :
    P.reconstruct C = f :=
  P.hom_ext _ _ (fun T x => (P.reconstruct_apply C T x).trans (h T x).symm)

/-- Natural inverse section transformations construct an actual module
isomorphism, with their original maps as forward and inverse maps. -/
def reconstructIso (Q : DisjointFreePresentation N)
    (C : Transformation M N) (D : Transformation N M)
    (hCD : ∀ (T : Over S) (x), D.app T (C.app T x) = x)
    (hDC : ∀ (T : Over S) (x), C.app T (D.app T x) = x) : M ≅ N where
  hom := P.reconstruct C
  inv := Q.reconstruct D
  hom_inv_id := by
    apply P.hom_ext
    intro T x
    rw [Functor.map_comp, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      P.reconstruct_apply, Q.reconstruct_apply, hCD,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl
  inv_hom_id := by
    apply Q.hom_ext
    intro T x
    rw [Functor.map_comp, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Q.reconstruct_apply, P.reconstruct_apply, hDC,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl

end DisjointFreePresentation
end Langlands.GroupScheme.RelativeUnipotent.NaturalModuleTransformations
