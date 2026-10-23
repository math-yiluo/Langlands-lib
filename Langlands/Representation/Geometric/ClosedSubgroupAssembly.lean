import Langlands.Representation.Geometric.CompactOrbitRestriction
import Langlands.Representation.Geometric.OrbitSectionExtensionStatement
import Langlands.Representation.Filtration.QuotientFirstIso

/-! Assembly of the specified graded quotient from orbit topology and extension. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric.OrderedDoubleCosets

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
  {P Q : Subgroup G} {n : ℕ}

/-- The pointwise extension assertion makes actual support-step restriction
surjective at every smooth inducing representation. -/
theorem supportStepOrbitRestriction_surjective
    (hExt : ClosedOrbitSectionExtension.{uG, uV})
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (s : OrderedDoubleCosets P Q n) (i : Fin n)
    (e : Induction.LeftQuotient (orbitStabilizer P Q (s.representative i)) ≃ₜ
      cosetOrbit P Q (s.representative i))
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q (s.representative i)) q)).val =
      Induction.quotientMap P ((s.representative i)⁻¹ * (q : G)))
    (A : Induction.SmoothRep.{0, uG, uV} ℂ P) :
    Function.Surjective ((s.supportStepOrbitRestriction i e he).app A).hom := by
  intro g
  obtain ⟨f, hf, hfg⟩ := hExt G P Q hP hQ (s.representative i)
    (s.initialOrbits i.succ) (s.initial_open i.succ)
    (s.cosetOrbit_subset_initialOrbits_succ i) (s.cosetOrbit_isClosed_in_next i) A g
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  exact hfg q

/-- Assemble the actual natural graded-piece isomorphism from a genuine orbit
homeomorphism and the compact section-extension assertion. -/
def supportGradedOrbitIsoOfExtension
    (hExt : ClosedOrbitSectionExtension.{uG, uV})
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (s : OrderedDoubleCosets P Q n) (i : Fin n)
    (e : Induction.LeftQuotient (orbitStabilizer P Q (s.representative i)) ≃ₜ
      cosetOrbit P Q (s.representative i))
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q (s.representative i)) q)).val =
      Induction.quotientMap P ((s.representative i)⁻¹ * (q : G))) :
    (s.supportFiltration.{0, uG, uV} (R := ℂ)).graded i ≅
      orbitPiece.{0, uG, uV} (R := ℂ) P Q (s.representative i) :=
  ((s.supportFiltration (R := ℂ)).step i.castSucc).quotientNatIsoOfSurjective
    ((s.supportFiltration (R := ℂ)).step i.succ)
    (s.supportStepOrbitRestriction i e he)
    (s.supportStepOrbitRestriction_kernel i e he)
    (s.supportStepOrbitRestriction_surjective hExt hP hQ i e he)

/-- The assembled comparison sends a support class to its actual orbit restriction. -/
@[simp]
theorem supportGradedOrbitIsoOfExtension_hom_projection
    (hExt : ClosedOrbitSectionExtension.{uG, uV})
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (s : OrderedDoubleCosets P Q n) (i : Fin n)
    (e : Induction.LeftQuotient (orbitStabilizer P Q (s.representative i)) ≃ₜ
      cosetOrbit P Q (s.representative i))
    (he : ∀ q : Q, (e (Induction.quotientMap (orbitStabilizer P Q (s.representative i)) q)).val =
      Induction.quotientMap P ((s.representative i)⁻¹ * (q : G)))
    (A : Induction.SmoothRep.{0, uG, uV} ℂ P)
    (f : ((s.supportFiltration (R := ℂ)).step i.succ).representation A) :
    ((s.supportGradedOrbitIsoOfExtension hExt hP hQ i e he).hom.app A).hom
        ((((s.supportFiltration (R := ℂ)).step i.castSucc).quotientProjection
          ((s.supportFiltration (R := ℂ)).step i.succ) A).hom f) =
      ((s.supportStepOrbitRestriction i e he).app A).hom f := rfl

end Langlands.Geometric.OrderedDoubleCosets
