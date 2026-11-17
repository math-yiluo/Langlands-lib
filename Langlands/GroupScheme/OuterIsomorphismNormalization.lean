import Langlands.GroupScheme.OuterIsomorphismNormalizedSection
import Mathlib.AlgebraicGeometry.Limits

/-! # Outer quotients represented by fixed points of normalization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)

/-- Natural normalization of all isomorphism points, constant on the acting
orbits, with a unique acting point taking the normalization to the original. -/
structure PointNormalization where
  normalize : ∀ {T : Over S}, (T ⟶ I.parameter) → (T ⟶ I.parameter)
  naturality : ∀ {T W : Over S} (t : W ⟶ T) (p : T ⟶ I.parameter),
    normalize (t ≫ p) = t ≫ normalize p
  invariant : ∀ {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter),
    normalize (lift d p ≫ I.actionHom a) = normalize p
  decomposition : ∀ {T : Over S} (p : T ⟶ I.parameter),
    ∃! d : T ⟶ A.X, lift d (normalize p) ≫ I.actionHom a = p

namespace PointNormalization

variable {I a} (n : I.PointNormalization a)

/-- The normalization of the universal point is an actual endomorphism. -/
def endomorphism : I.parameter ⟶ I.parameter :=
  n.normalize (𝟙 I.parameter)

/-- Naturality identifies every normalization with this endomorphism. -/
theorem normalize_eq {T : Over S} (p : T ⟶ I.parameter) :
    n.normalize p = p ≫ n.endomorphism := by
  simpa only [Category.comp_id, endomorphism] using
    n.naturality p (𝟙 I.parameter)

/-- Invariance and the orbit decomposition force normalization to be idempotent. -/
theorem idempotent {T : Over S} (p : T ⟶ I.parameter) :
    n.normalize (n.normalize p) = n.normalize p := by
  obtain ⟨d, hd, _⟩ := n.decomposition p
  have h := n.invariant d (n.normalize p)
  rw [hd] at h
  exact h.symm

theorem endomorphism_idempotent :
    n.endomorphism ≫ n.endomorphism = n.endomorphism := by
  calc
    n.endomorphism ≫ n.endomorphism = n.normalize n.endomorphism :=
      (n.normalize_eq n.endomorphism).symm
    _ = n.normalize (n.normalize (𝟙 I.parameter)) := rfl
    _ = n.normalize (𝟙 I.parameter) := n.idempotent _
    _ = n.endomorphism := rfl

/-- The actual relative scheme of normalized points. -/
def parameter : Over S :=
  equalizer n.endomorphism (𝟙 I.parameter)

/-- Inclusion of the normalized parameter scheme into the isomorphism scheme. -/
def inclusion : n.parameter ⟶ I.parameter :=
  equalizer.ι n.endomorphism (𝟙 I.parameter)

instance : Mono n.inclusion :=
  inferInstanceAs (Mono (equalizer.ι n.endomorphism (𝟙 I.parameter)))

theorem inclusion_endomorphism :
    n.inclusion ≫ n.endomorphism = n.inclusion := by
  simpa only [inclusion, Category.comp_id] using
    equalizer.condition n.endomorphism (𝟙 I.parameter)

/-- The normalization factors through its fixed point scheme. -/
def classMap : I.parameter ⟶ n.parameter :=
  equalizer.lift n.endomorphism (by
    simpa only [Category.comp_id] using n.endomorphism_idempotent)

theorem classMap_inclusion :
    n.classMap ≫ n.inclusion = n.endomorphism :=
  equalizer.lift_ι _ _

theorem inclusion_classMap :
    n.inclusion ≫ n.classMap = 𝟙 n.parameter := by
  apply equalizer.hom_ext
  change (n.inclusion ≫ n.classMap) ≫ n.inclusion =
    𝟙 n.parameter ≫ n.inclusion
  rw [Category.assoc, n.classMap_inclusion, n.inclusion_endomorphism,
    Category.id_comp]

/-- Every point of the fixed point scheme is normalized on the original test. -/
theorem normalize_inclusion {T : Over S} (q : T ⟶ n.parameter) :
    n.normalize (q ≫ n.inclusion) = q ≫ n.inclusion := by
  rw [n.normalize_eq, Category.assoc, n.inclusion_endomorphism]

/-- Unique normalization produces a unique group/fixed-point decomposition
on every relative scheme test. -/
theorem orbit_bijective (T : Over S) :
    Function.Bijective (fun z : (T ⟶ A.X) × (T ⟶ n.parameter) =>
      lift z.1 (z.2 ≫ n.inclusion) ≫ I.actionHom a) := by
  constructor
  · intro z w h
    have hq : z.2 ≫ n.inclusion = w.2 ≫ n.inclusion := by
      have hn := congrArg n.normalize h
      simpa only [n.invariant, n.normalize_inclusion] using hn
    have hqw : z.2 = w.2 := (cancel_mono n.inclusion).mp hq
    let p := lift z.1 (z.2 ≫ n.inclusion) ≫ I.actionHom a
    have hn : n.normalize p = z.2 ≫ n.inclusion := by
      exact (n.invariant z.1 (z.2 ≫ n.inclusion)).trans
        (n.normalize_inclusion z.2)
    have hd : z.1 = w.1 := by
      apply (n.decomposition p).unique
      · rw [hn]
      · rw [hn, hq]
        exact h.symm
    exact Prod.ext hd hqw
  · intro p
    obtain ⟨d, hd, _⟩ := n.decomposition p
    refine ⟨(d, p ≫ n.classMap), ?_⟩
    change lift d ((p ≫ n.classMap) ≫ n.inclusion) ≫ I.actionHom a = p
    rw [Category.assoc, n.classMap_inclusion, ← n.normalize_eq]
    exact hd

/-- Natural unique normalization represents the actual outer quotient by an
equalizer. No separate normalized parameter scheme is assumed. -/
def outer [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme I a :=
  I.outerOfNormalizedSection a n.inclusion n.orbit_bijective

end PointNormalization

end Langlands.GroupScheme.GroupIsomorphismScheme
