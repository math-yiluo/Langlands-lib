import Langlands.GroupScheme.Reductive.RelativeCommutatorDescent
import Langlands.GroupScheme.Reductive.RelativeSemisimpleFppfPerfectProof

/-! # Homomorphisms with commuting values kill fppf-local commutators -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.CommutatorTriviality

variable {R : CommRingCat.{u}} {K M : GroupScheme (Spec R)} {T : CommAlgCat.{u} R}
  (c : Under.forget T ⋙ K.affinePointFunctor ⟶ Under.forget T ⋙ M.affinePointFunctor)

/-- A homomorphism of groups whose values commute with each other kills commutators. -/
theorem map_eq_one_of_mem_commutator {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂)
    (hφ : ∀ x y, Commute (φ x) (φ y)) {x : G₁} (hx : x ∈ _root_.commutator G₁) : φ x = 1 := by
  have h1 : φ x ∈ (_root_.commutator G₁).map φ := Subgroup.mem_map_of_mem φ hx
  rw [map_commutator_eq] at h1
  have h2 : ⁅φ.range, φ.range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact (hφ b a).eq
  rw [h2] at h1
  exact (Subgroup.mem_bot).1 h1

variable (hc : ∀ (X : Under T) (x y : (Under.forget T ⋙ K.affinePointFunctor).obj X),
  Commute (c.app X x) (c.app X y))

include hc in
theorem app_eq_one_of_mem_commutator (X : Under T) (x : K.affinePoints X.right)
    (hx : x ∈ _root_.commutator (K.affinePoints X.right)) : c.app X x = 1 :=
  map_eq_one_of_mem_commutator (c.app X).hom (fun a b => hc X a b) hx

/-- The refinement of an fppf cover by the affine open covers of its members. -/
def affineRefinement {Y : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Y) :
    Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) Y :=
  Scheme.Cover.mkOfCovers (Σ i : 𝒰.I₀, (𝒰.X i).affineCover.I₀)
    (fun k => (𝒰.X k.1).affineCover.X k.2)
    (fun k => (𝒰.X k.1).affineCover.f k.2 ≫ 𝒰.f k.1)
    (fun y => by
      obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq y
      obtain ⟨j, v, rfl⟩ := (𝒰.X i).affineCover.exists_eq w
      exact ⟨⟨i, j⟩, v, rfl⟩)
    (fun k => by
      have h := 𝒰.map_prop k.1
      haveI : Flat (𝒰.f k.1) := h.1
      haveI : LocallyOfFinitePresentation (𝒰.f k.1) := h.2
      exact ⟨inferInstance, inferInstance⟩)

/-- The algebra of an affine member of a cover of `Spec X`. -/
abbrev pieceAlg (X : CommAlgCat.{u} R) {S : CommRingCat.{u}}
    (f : Spec S ⟶ ((algSpec R).obj (op X)).left) : CommAlgCat.{u} R :=
  letI : Algebra R S :=
    ((Spec.preimage (R := CommRingCat.of X) (S := S) f).hom.comp (algebraMap R X)).toAlgebra
  CommAlgCat.of R S

/-- The algebra map of an affine member of a cover of `Spec X`. -/
def pieceMap (X : CommAlgCat.{u} R) {S : CommRingCat.{u}}
    (f : Spec S ⟶ ((algSpec R).obj (op X)).left) : X ⟶ pieceAlg X f :=
  letI : Algebra R S :=
    ((Spec.preimage (R := CommRingCat.of X) (S := S) f).hom.comp (algebraMap R X)).toAlgebra
  CommAlgCat.ofHom (X := X) (Y := S)
    { (Spec.preimage (R := CommRingCat.of X) (S := S) f).hom with commutes' := fun _ => rfl }

theorem algSpec_pieceMap_left (X : CommAlgCat.{u} R) {S : CommRingCat.{u}}
    (f : Spec S ⟶ ((algSpec R).obj (op X)).left) :
    ((algSpec R).map (pieceMap X f).op).left = f := by
  change Spec.map (CommRingCat.ofHom
    (Spec.preimage (R := CommRingCat.of X) (S := S) f).hom) = f
  exact Spec.map_preimage f

include hc in
/-- **Commuting values kill fppf-local commutators.** -/
theorem app_eq_one_of_locallyCommutator (X : Under T) (x : K.affinePoints X.right)
    (hx : RelativeDerived.LocallyCommutator x) : c.app X x = 1 := by
  obtain ⟨𝒰, h𝒰⟩ := hx
  haveI := RelativeDerived.effectiveEpiFamily_fppfCover (affineRefinement 𝒰)
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext (affineRefinement 𝒰).X (affineRefinement 𝒰).f
  rintro ⟨i₀, j₀⟩
  let g := (𝒰.X i₀).affineCover.f j₀
  let f : Spec _ ⟶ ((algSpec R).obj (op X.right)).left := g ≫ 𝒰.f i₀
  let incl := pieceMap X.right f
  let Y : Under T := Under.mk (X.hom ≫ incl)
  have hleft : ((algSpec R).map incl.op).left = f := algSpec_pieceMap_left X.right f
  have hpoint : K.affinePointMap incl x ∈ _root_.commutator (K.affinePoints Y.right) := by
    have h1 := RelativeDerived.commutator_precomp
      (Over.homMk g rfl : Over.mk (g ≫ 𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom) ⟶
        Over.mk (𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom)) (h𝒰 i₀)
    let b : (algSpec R).obj (op Y.right) ⟶
        Over.mk (g ≫ 𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom) :=
      Over.homMk (𝟙 _) (by
        have := Over.w ((algSpec R).map incl.op)
        rw [hleft] at this
        rw [Category.id_comp]
        simp only [f, Category.assoc] at this
        exact this)
    have h2 := RelativeDerived.commutator_precomp b h1
    have he : K.affinePointMap incl x = b ≫ (Over.homMk g rfl :
        Over.mk (g ≫ 𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom) ⟶
          Over.mk (𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom)) ≫
        (Over.homMk (𝒰.f i₀) rfl : Over.mk (𝒰.f i₀ ≫ ((algSpec R).obj (op X.right)).hom) ⟶
          (algSpec R).obj (op X.right)) ≫ x := by
      rw [affinePointMap_apply]
      apply Over.OverMorphism.ext
      change ((algSpec R).map incl.op).left ≫ x.left =
        𝟙 _ ≫ g ≫ 𝒰.f i₀ ≫ x.left
      rw [hleft, Category.id_comp]
      simp only [f, Category.assoc]
    rw [he]
    exact h2
  have hnat := congrArg (fun h => GrpCat.Hom.hom h x)
    (c.naturality (Under.homMk incl rfl : X ⟶ Y))
  have h1 : c.app Y (K.affinePointMap incl x) = 1 := app_eq_one_of_mem_commutator c hc Y _ hpoint
  have h3 : M.affinePointMap incl (c.app X x) = M.affinePointMap incl 1 := by
    rw [map_one]
    exact hnat.symm.trans h1
  have h4 := congrArg CommaMorphism.left h3
  rw [affinePointMap_apply, affinePointMap_apply] at h4
  change ((algSpec R).map incl.op).left ≫ (c.app X x).left =
    ((algSpec R).map incl.op).left ≫ (1 : M.affinePoints X.right).left at h4
  rw [hleft] at h4
  exact h4

include hc in
/-- **Base case.** For a reductive group scheme over an affine base whose geometric fibres are
semisimple, a homomorphism with commuting values on its points over `T`-algebras is trivial. -/
theorem app_eq_one_of_semisimple (hred : IsReductive K)
    (hss : ∀ s, IsSemisimple (geometricFiber K s)) (X : Under T) (x : K.affinePoints X.right) :
    c.app X x = 1 :=
  app_eq_one_of_locallyCommutator c hc X x (relativeSemisimpleFppfPerfect (Spec R) K hred hss _ x)

end Langlands.GroupScheme.CommutatorTriviality
