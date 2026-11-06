import Langlands.Geometry.Analytic.AtlasDomainTensorIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing

/-! # Agreement and bounded test-map gluing across full local domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- Agreement over one common containing domain implies agreement over any
other containing domain. Full bounded maps, including nilpotents, are retained. -/
theorem restriction_eq_of_common_container
    {S T U V : LocalDomain a} (f : S ⟶ U) (g : T ⟶ U)
    (p : S ⟶ V) (q : T ⟶ V) (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K S.algebra R) (β : BoundedAlgHom K T.algebra R)
    (h : α.comp f.restriction = β.comp g.restriction) :
    α.comp p.restriction = β.comp q.restriction := by
  let θ : BoundedAlgHom K (interOver f g).algebra R :=
    AffinoidPushout.lift f.restriction g.restriction R α β h
  have hα : θ.comp (interOverLeft f g).restriction = α := by
    rw [interOverLeft_restriction]
    exact AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _
  have hβ : θ.comp (interOverRight f g).restriction = β := by
    rw [interOverRight_restriction]
    exact AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _
  have heq : interOverLeft f g ≫ p = interOverRight f g ≫ q :=
    @Subsingleton.elim (Inclusion (interOver f g) V) inferInstance _ _
  have hθ := congrArg (fun r : interOver f g ⟶ V => θ.comp r.restriction) heq
  simpa only [Inclusion.restriction_comp, ← BoundedAlgHom.comp_assoc, hα, hβ] using hθ

/-- A finite family of actual full local domains with inclusions into two
specified containers. Coverage is required only after an eligible test map. -/
structure CommonSubdomainFamily (U V : LocalDomain a) where
  size : ℕ
  obj : Fin size → LocalDomain a
  left : ∀ i, obj i ⟶ U
  right : ∀ i, obj i ⟶ V

namespace CommonSubdomainFamily

variable {U V : LocalDomain a} (c : CommonSubdomainFamily U V)
  (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K U.algebra R)

/-- The test image is covered by the literal ambient images of the family. -/
def CoversTest : Prop :=
  ∀ x : BanachSpectrum R,
    ∃ i, U.ambientMap (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ (c.obj i).locus

variable (hφ : c.CoversTest R φ)

/-- Pull the full domains back along the original test to cover the whole
actual test spectrum, with the original base-change maps. -/
def testCover : Domain.FiniteCover (Domain.whole K R) where
  size := c.size
  obj i := Domain.pullback φ (c.left i).relativeDomain
  map i := ⟨(Domain.pullback φ (c.left i).relativeDomain).baseMap,
    BoundedAlgHom.comp_id _⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := hφ x
    exact ⟨i, hi⟩

/-- The original V restriction followed by the actual pulled-domain map. -/
def testLocalMap (i : Fin c.size) :
    BoundedAlgHom K V.algebra ((c.testCover R φ hφ).obj i).algebra :=
  (Domain.pullbackMap φ (c.left i).relativeDomain).comp (c.right i).restriction

/-- Compatibility follows from equality of maps over U on each actual test
overlap, transported to V through the constructed common-domain intersection. -/
theorem testLocalMap_compatible :
    (c.testCover R φ hφ).BoundedMapCompatible (c.testLocalMap R φ hφ) := by
  intro i j W p q
  let α := p.restriction.comp (Domain.pullbackMap φ (c.left i).relativeDomain)
  let β := q.restriction.comp (Domain.pullbackMap φ (c.left j).relativeDomain)
  have hα : α.comp (c.left i).restriction = W.baseMap.comp φ := by
    change (p.restriction.comp (Domain.pullbackMap φ (c.left i).relativeDomain)).comp
      (c.left i).relativeDomain.baseMap = W.baseMap.comp φ
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, p.comp_baseMap]
  have hβ : β.comp (c.left j).restriction = W.baseMap.comp φ := by
    change (q.restriction.comp (Domain.pullbackMap φ (c.left j).relativeDomain)).comp
      (c.left j).relativeDomain.baseMap = W.baseMap.comp φ
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, q.comp_baseMap]
  exact restriction_eq_of_common_container (c.left i) (c.left j)
    (c.right i) (c.right j) W.algebra α β (hα.trans hβ.symm)

/-- Actual bounded scalar descent constructs the V map on every covered test. -/
def testFactor : BoundedAlgHom K V.algebra R :=
  (c.testCover R φ hφ).glueBoundedAlgHom (c.testLocalMap R φ hφ)
    (c.testLocalMap_compatible R φ hφ)

/-- The original pulled-domain maps compute every local restriction of the
glued map as a full bounded-map identity. -/
theorem testFactor_local (i : Fin c.size) :
    (Domain.pullback φ (c.left i).relativeDomain).baseMap.comp (c.testFactor R φ hφ) =
      (Domain.pullbackMap φ (c.left i).relativeDomain).comp (c.right i).restriction :=
  (c.testCover R φ hφ).restriction_comp_glueBoundedAlgHom _ _ i

/-- Agreement with these actual local restrictions uniquely determines the
bounded map on the test algebra. -/
theorem testFactor_unique (ψ : BoundedAlgHom K V.algebra R)
    (hψ : ∀ i,
      (Domain.pullback φ (c.left i).relativeDomain).baseMap.comp ψ =
        (Domain.pullbackMap φ (c.left i).relativeDomain).comp (c.right i).restriction) :
    ψ = c.testFactor R φ hφ :=
  (c.testCover R φ hφ).glueBoundedAlgHom_unique (c.testLocalMap R φ hφ)
    (c.testLocalMap_compatible R φ hφ) ψ hψ

end CommonSubdomainFamily
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain
