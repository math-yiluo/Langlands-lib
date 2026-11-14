import Langlands.GroupScheme.Torus.WeylQuotientSplittingCoverOrder
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Finiteness of a supplied Weyl quotient from a general local-base criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A general universal local-base cardinality criterion implies finiteness of a
supplied quasi-compact separated étale Weyl quotient of a maximal relative torus. -/
def WeylQuotientFinitenessReductionStatement : Prop :=
  (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    QuasiCompact f → IsSeparated f → Etale f →
    (∀ (R : Type u) [CommRing R] [IsLocalRing R]
      (b : Spec (CommRingCat.of R) ⟶ Y),
      ∃ d : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
        Nat.card {x : Spec (CommRingCat.of k) ⟶ X //
          x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ b} = d) →
    IsFinite f) →
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∀ (N : GroupScheme S) (n : N ⟶ G) (W : GroupScheme S) (q : N ⟶ W),
        IsClosedSubgroup n → (torusNormalizer t).IsRepresentedBy n →
        QuasiCompact W.X.hom → IsSeparated W.X.hom → Etale W.X.hom →
        Surjective q.hom.hom.left →
        (∀ (U : Over S) (y : U ⟶ N.X),
          y ≫ q.hom.hom = 1 ↔ y ≫ n.hom.hom ∈ (torusCentralizer t).carrier U) →
        IsFinite W.X.hom

/-- Apply the general criterion on a torus splitting cover and descend finiteness
using its fppf target locality. -/
theorem weylQuotientFinitenessReduction :
    WeylQuotientFinitenessReductionStatement.{u} := by
  intro hfinite S G hG T t hT ht hmax N n W q hnclosed hn hqc hsep het hq hker
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion n.hom.hom.left := hnclosed
  let : LocallyOfFiniteType N.X.hom := by
    have h : LocallyOfFiniteType (n.hom.hom.left ≫ G.X.hom) := inferInstance
    rwa [n.hom.hom.w] at h
  let : QuasiCompact W.X.hom := hqc
  let : IsSeparated W.X.hom := hsep
  let : Etale W.X.hom := het
  obtain ⟨𝒰, h𝒰⟩ := exists_splittingCover_natCard_quotientFibre_constant
    hG t ht hmax hn q hq hker hT
  let 𝒱 : S.Cover Scheme.fppfPrecoverage :=
    𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun j => ⟨inferInstance, inferInstance⟩)
  let : MorphismProperty.IsLocalAtTarget
      (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage @IsFinite
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover
    (P := @IsFinite) 𝒱 (fun j => ?_)
  change IsFinite (Limits.pullback.snd W.X.hom (𝒰.f j))
  refine hfinite _ _ _ inferInstance inferInstance inferInstance ?_
  intro R _ _ b
  exact h𝒰 j R b

end Langlands.GroupScheme
