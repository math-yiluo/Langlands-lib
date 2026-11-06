import Langlands.Representation.Category.SmoothCoproducts
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Jacquet.CompressionFiniteSupport
import Langlands.Representation.Jacquet.CompressionUniformity

/-! # Actual coproduct carriers and compact compression

The actual algebraic direct sum is equivalent to any supplied smooth coproduct
vertex, even when the index universe exceeds the carrier universe.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.LinearAlgebra.StableEndomorphism

namespace Langlands.SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {κ : Type uI} [DecidableEq κ]
  (A : κ → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A)

/-- The actual summation intertwiner into a supplied cofan vertex. -/
def cofanDirectSumMap :
    (Representation.directSum (fun i => (A i).representation)).IntertwiningMap
      s.pt.representation where
  toLinearMap := DirectSum.toModule ℂ κ s.pt
    (fun i => (hom (s.inj i)).toLinearMap)
  isIntertwining' g := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    change (DirectSum.toModule ℂ κ s.pt (fun i => (hom (s.inj i)).toLinearMap))
        (DirectSum.lmap (fun i => (A i).representation g)
          (DirectSum.lof ℂ κ (fun i => A i) i v)) =
      s.pt.representation g
        ((DirectSum.toModule ℂ κ s.pt (fun i => (hom (s.inj i)).toLinearMap))
          (DirectSum.lof ℂ κ (fun i => A i) i v))
    rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact (hom (s.inj i)).isIntertwining _ _ g v

@[simp]
theorem cofanDirectSumMap_lof (i : κ) (v : A i) :
    cofanDirectSumMap A s (DirectSum.lof ℂ κ (fun i => A i) i v) =
      hom (s.inj i) v :=
  by apply DirectSum.toModule_lof

/-- The universal property of a smooth coproduct supplies all component
projections and makes actual summation injective. -/
theorem cofanDirectSumMap_injective (hs : IsColimit s) :
    Function.Injective (cofanDirectSumMap A s) := by
  let z : ∀ i : κ, Cofan A := fun i => Cofan.mk (A i)
    (fun j => if hji : j = i then eqToHom (congrArg A hji) else 0)
  let p : ∀ i : κ, s.pt ⟶ A i := fun i => hs.desc (z i)
  have hp (i : κ) :
      (hom (p i)).toLinearMap.comp (cofanDirectSumMap A s).toLinearMap =
        DirectSum.component ℂ κ (fun i => A i) i := by
    apply DirectSum.linearMap_ext
    intro j
    ext v
    change hom (p i) (cofanDirectSumMap A s
        (DirectSum.lof ℂ κ (fun i => A i) j v)) =
      DirectSum.component ℂ κ (fun i => A i) i
        (DirectSum.lof ℂ κ (fun i => A i) j v)
    rw [cofanDirectSumMap_lof]
    have hfac := congrArg (fun f => hom f v) (hs.fac (z i) ⟨j⟩)
    change hom (p i) (hom (s.inj j) v) = hom ((z i).inj j) v at hfac
    refine hfac.trans ?_
    by_cases hji : j = i
    · subst j
      simp [z, DirectSum.component.lof_self]
    · simp [z, hji, DirectSum.component.of]
      rfl
  intro x y hxy
  apply DirectSum.ext_component ℂ
  intro i
  rw [← LinearMap.congr_fun (hp i) x, ← LinearMap.congr_fun (hp i) y]
  exact congrArg (hom (p i)) hxy

/-- The quotient by the actual summation image annihilates every summand;
the coproduct universal property forces this quotient map to vanish. -/
theorem cofanDirectSumMap_surjective (hs : IsColimit s) :
    Function.Surjective (cofanDirectSumMap A s) := by
  let q := mkQ s.pt (cofanDirectSumMap A s).range
  have hq : q = 0 := by
    apply hs.hom_ext
    rintro ⟨i⟩
    apply ObjectProperty.hom_ext
    ext v
    change hom q (hom (s.inj i) v) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨DirectSum.lof ℂ κ (fun i => A i) i v, cofanDirectSumMap_lof A s i v⟩
  intro y
  have hy : hom q y = 0 := congrArg (fun f => hom f y) hq
  exact (Submodule.Quotient.mk_eq_zero _).mp hy

/-- Actual summation identifies the algebraic direct sum with any supplied
smooth coproduct vertex, across independent carrier and index universes. -/
def cofanDirectSumEquiv (hs : IsColimit s) :
    (Representation.directSum (fun i => (A i).representation)).Equiv
      s.pt.representation :=
  (cofanDirectSumMap A s).ofBijective
    ⟨cofanDirectSumMap_injective A s hs, cofanDirectSumMap_surjective A s hs⟩

@[simp]
theorem cofanDirectSumEquiv_lof (hs : IsColimit s) (i : κ) (v : A i) :
    cofanDirectSumEquiv A s hs (DirectSum.lof ℂ κ (fun i => A i) i v) =
      hom (s.inj i) v :=
  cofanDirectSumMap_lof A s i v

/-- Finite nonzero fixed-vector support and eventual stability of all
components imply eventual stability on an actual categorical coproduct. -/
theorem compressedAction_eventuallyStable_of_cofan_finite_support
    [IsTopologicalGroup G] (hs : IsColimit s)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfinite : Jacquet.FiniteFixedVectorSupport
      (fun i => (A i).representation) K.toSubgroup)
    (hpoint : ∀ i, EventuallyStable
      (Jacquet.compressedAction (A i).representation (A i).isSmooth K hK g)) :
    EventuallyStable (Jacquet.compressedAction s.pt.representation s.pt.isSmooth K hK g) := by
  let e := cofanDirectSumEquiv A s hs
  have hsum : IsSmooth (Representation.directSum (fun i => (A i).representation)) :=
    Langlands.isSmooth_of_injective e.toIntertwiningMap e.injective s.pt.isSmooth
  obtain ⟨b, hb, hstable⟩ :=
    Jacquet.compressedAction_eventuallyStable_directSum_of_finite_support
      (fun i => (A i).representation) (fun i => (A i).isSmooth) hsum
      K hK g hfinite hpoint
  refine ⟨b, hb, ?_⟩
  exact Jacquet.compactCompressionStablePower_of_retract
    s.pt.representation (Representation.directSum (fun i => (A i).representation))
    s.pt.isSmooth hsum K hK g e.symm.toIntertwiningMap e.toIntertwiningMap
    (by ext x; exact e.apply_symm_apply x) b hstable

end Langlands.SmoothRep
