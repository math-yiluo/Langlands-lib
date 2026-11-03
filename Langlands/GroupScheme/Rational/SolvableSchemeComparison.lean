import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.AutomorphicAction.SemidirectProduct

/-! # Uniform all-test solvability and geometric solvability -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace UniformSolvability

/-- An injective homomorphism preserves a supplied derived-series bound. -/
theorem bound_of_injective {M N : Type*} [Group M] [Group N]
    (f : M →* N) (hf : Function.Injective f) (d : ℕ)
    (hd : derivedSeries N d = ⊥) : derivedSeries M d = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hfx := map_derivedSeries_le_derivedSeries f d (Subgroup.mem_map_of_mem f hx)
  rw [hd, Subgroup.mem_bot] at hfx
  exact Subgroup.mem_bot.mpr (hf (hfx.trans (map_one f).symm))

/-- Bounds for a normal factor and quotient add, using only kernel containment
in the image of the normal-factor homomorphism. -/
theorem extension_bound {N P K : Type*} [Group N] [Group P] [Group K]
    (f : N →* P) (q : P →* K) (hker : q.ker ≤ f.range)
    (m n : ℕ) (hm : derivedSeries N m = ⊥) (hn : derivedSeries K n = ⊥) :
    derivedSeries P (n + m) = ⊥ := by
  have hbase : derivedSeries P n ≤ (derivedSeries N 0).map f := by
    simpa only [derivedSeries_zero, Subgroup.map_top] using
      ((derivedSeries P n).map_eq_bot_iff.mp
        (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries q n).trans hn.le))).trans hker
  have hstep : ∀ d : ℕ, derivedSeries P (n + d) ≤ (derivedSeries N d).map f := by
    intro d
    induction d with
    | zero => exact hbase
    | succ d ih => exact Subgroup.commutator_le_map_commutator ih ih
  exact le_bot_iff.mp (by simpa only [hm, Subgroup.map_bot] using hstep m)

end UniformSolvability

namespace IsSolvableScheme

variable {B : Scheme.{u}} {G H : GroupScheme B}

/-- Choose one common derived-series bound for all test schemes. This is a
bound, with no assertion that it is the least possible one. -/
def uniformBound (h : IsSolvableScheme G) : ℕ := h.choose

/-- The chosen bound terminates the derived series on every test scheme. -/
theorem derivedSeries_uniformBound (h : IsSolvableScheme G) (T : Over B) :
    derivedSeries (T ⟶ G.X) h.uniformBound = ⊥ := h.choose_spec T

/-- Uniform solvability supplies solvability of each actual point group. -/
theorem points (h : IsSolvableScheme G) (T : Over B) :
    Group.IsSolvable (T ⟶ G.X) :=
  ⟨⟨h.uniformBound, h.derivedSeries_uniformBound T⟩⟩

/-- A subgroup monomorphism inherits the ambient uniform bound. -/
theorem of_mono (h : IsSolvableScheme G) (i : H ⟶ G) [Mono i.hom.hom] :
    IsSolvableScheme H := by
  refine ⟨h.uniformBound, fun T => ?_⟩
  exact UniformSolvability.bound_of_injective
    ((pointsMap i).app (op T)).hom
    (fun _ _ he => (cancel_mono i.hom.hom).mp he)
    h.uniformBound (h.derivedSeries_uniformBound T)

/-- Base change preserves the very same uniform bound, via the actual
base-change point equivalence on every test scheme over the new base. -/
theorem baseChange (h : IsSolvableScheme G) {B' : Scheme.{u}} (b : B' ⟶ B) :
    IsSolvableScheme ((GroupScheme.baseChange b).obj G) := by
  refine ⟨h.uniformBound, fun T => ?_⟩
  exact UniformSolvability.bound_of_injective
    (baseChangePointsEquiv b G T).toMonoidHom
    (baseChangePointsEquiv b G T).injective
    h.uniformBound (h.derivedSeries_uniformBound ((Over.map b).obj T))

/-- Uniform solvability is invariant under actual group-scheme isomorphism. -/
theorem of_iso (h : IsSolvableScheme G) (e : H ≅ G) : IsSolvableScheme H :=
  h.of_mono e.hom

end IsSolvableScheme

/-- Uniform all-test solvability is invariant under actual group-scheme
isomorphism, without any smoothness or affineness premise. -/
theorem isSolvableScheme_iff_of_iso {B : Scheme.{u}} {G H : GroupScheme B}
    (e : G ≅ H) : IsSolvableScheme G ↔ IsSolvableScheme H :=
  ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- Semidirect products of uniformly solvable group schemes are uniformly
solvable. The sum of the acting and normal bounds works on every test. -/
theorem isSolvableScheme_semidirect {B : Scheme.{u}} {K N : GroupScheme B}
    (a : AutomorphicAction K N) (hK : IsSolvableScheme K)
    (hN : IsSolvableScheme N) : IsSolvableScheme a.semidirectProduct := by
  refine ⟨hK.uniformBound + hN.uniformBound, fun T => ?_⟩
  let e := a.semidirectPointsEquiv T
  have hprod : derivedSeries
      (SemidirectProduct (T ⟶ N.X) (T ⟶ K.X) (a.pointsAction T))
      (hK.uniformBound + hN.uniformBound) = ⊥ :=
    UniformSolvability.extension_bound SemidirectProduct.inl SemidirectProduct.rightHom
      (le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm)
      hN.uniformBound hK.uniformBound
      (hN.derivedSeries_uniformBound T) (hK.derivedSeries_uniformBound T)
  exact UniformSolvability.bound_of_injective e.toMonoidHom e.injective _ hprod

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- All-test uniform solvability implies the geometric-point solvability used
by structural group-scheme theorems, without smoothness or affineness. -/
theorem IsSolvableScheme.isSolvableGroupScheme (h : IsSolvableScheme G) :
    IsSolvableGroupScheme G := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))
  let e := baseChangePointsEquiv (toAlgebraicClosure k) G T
  let := h.points ((Over.map (toAlgebraicClosure k)).obj T)
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective

/-- For smooth affine groups, geometric solvability gives a single bound on
every point group, by the published derived-word argument. -/
theorem isSolvableScheme_of_isSolvableGroupScheme [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom) (h : IsSolvableGroupScheme G) : IsSolvableScheme G :=
  SolvableFieldExtensionProof.exists_uniform_derivedSeries_eq_bot G hG h

/-- The two existing solvability predicates agree for smooth affine groups
over any field. Connectedness and algebraic closedness are unnecessary. -/
theorem isSolvableScheme_iff_isSolvableGroupScheme [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom) : IsSolvableScheme G ↔ IsSolvableGroupScheme G :=
  ⟨IsSolvableScheme.isSolvableGroupScheme,
    isSolvableScheme_of_isSolvableGroupScheme hG⟩

end Field

end Langlands.GroupScheme.RelativeRoot
