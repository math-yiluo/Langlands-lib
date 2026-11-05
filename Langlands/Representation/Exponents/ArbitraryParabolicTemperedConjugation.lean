import Langlands.Representation.Exponents.NormalizedTemperedStandardReductionStatement
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationAmbientTransport

/-! # All-presentation normalized exponent conditions under conjugation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {G G' P M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Pull a presentation of the transported parabolic back to the original map. -/
def invCompAmbientIso (e : G ≅ G')
    (r : ParabolicRootPresentation (p ≫ e.hom) l a) :
    ParabolicRootPresentation p l a where
  data := (r.compAmbientIso e.symm).data
  isCompatible := by
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] using
      (r.compAmbientIso e.symm).isCompatible

private theorem eq_of_data_eq {r s : ParabolicRootPresentation p l a}
    (h : r.data = s.data) : r = s := by
  cases r
  cases s
  cases h
  rfl

/-- Ambient transport is an equivalence of the entire presentation types. -/
def compAmbientIsoEquiv (e : G ≅ G') :
    ParabolicRootPresentation p l a ≃
      ParabolicRootPresentation (p ≫ e.hom) l a where
  toFun r := r.compAmbientIso e
  invFun := invCompAmbientIso e
  left_inv r := by
    apply eq_of_data_eq
    cases r with
    | mk d hd =>
      cases d
      simp only [invCompAmbientIso, compAmbientIso, Category.assoc, Iso.symm_hom,
        Iso.hom_inv_id, Category.comp_id]
  right_inv r := by
    apply eq_of_data_eq
    cases r with
    | mk d hd =>
      cases d
      simp only [invCompAmbientIso, compAmbientIso, Category.assoc, Iso.symm_hom,
        Iso.inv_hom_id, Category.comp_id]

/-- Inverse ambient transport also preserves the actual restricted vectors. -/
theorem restrictedRoots_invCompAmbientIso (e : G ≅ G')
    (r : ParabolicRootPresentation (p ≫ e.hom) l a) :
    (invCompAmbientIso e r).restrictedRoots = r.restrictedRoots := by
  change restrictedSimpleRoots (r.data.i ≫ e.inv) r.data.ν r.data.J r.data.f = _
  have hs := simpleRelativeRoots_comp_ambientIso r.data.i r.data.ν e.symm
  simp only [Iso.symm_hom] at hs
  simp only [restrictedSimpleRoots, hs]

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]

/-- Inverse ambient transport preserves the full nonnegative cone. -/
theorem nonnegCone_invCompAmbientIso (e : G ≅ G')
    (r : ParabolicRootPresentation (p ≫ e.hom) l a) :
    (invCompAmbientIso e r).nonnegCone = r.nonnegCone := by
  ext x
  rw [mem_nonnegCone, mem_nonnegCone, restrictedRoots_invCompAmbientIso]

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance temperedConjugationAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

section ConeCondition

variable [LocallyOfFiniteType G.X.hom]
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (ha : IsSplitComponent a)

/-- Inner conjugation preserves nonempty coverage and every presentation,
radical, decomposition and exponent test of the normalized cone condition. -/
theorem satisfiesNormalizedExponentConeCondition_comp_innerIso_iff
    (g : rationalPoints G) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    SatisfiesNormalizedExponentConeCondition (p ≫ (G.innerIso g).hom) l a
        (hp.comp_iso (G.innerIso g)) hl ha π ↔
      SatisfiesNormalizedExponentConeCondition p l a hp hl ha π := by
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨pres⟩ := hne
      exact ⟨pres.invCompAmbientIso (G.innerIso g)⟩
    · intro pres U r hr hmul χ hχ
      have hc := h (pres.compAmbientIso (G.innerIso g)) U r hr hmul χ
        ((isNormalizedJacquetExponent_comp_innerIso_iff
          p l r hp hl hr hmul ha g π χ).mpr hχ)
      simpa only [ParabolicRootPresentation.nonnegCone_compAmbientIso] using hc
  · rintro ⟨hne, h⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨pres⟩ := hne
      exact ⟨pres.compAmbientIso (G.innerIso g)⟩
    · intro pres U r hr hmul χ hχ
      have hc := h (pres.invCompAmbientIso (G.innerIso g)) U r hr hmul χ
        ((isNormalizedJacquetExponent_comp_innerIso_iff
          p l r hp hl hr hmul ha g π χ).mp hχ)
      simpa only [ParabolicRootPresentation.nonnegCone_invCompAmbientIso] using hc

end ConeCondition

/-- The forward standard restriction uses the same all-presentation condition
already required at every actual parabolic by normalized temperedness. -/
theorem IsNormalizedExponentTempered.standardRestriction
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (h : IsNormalizedExponentTempered hG π)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) :
    haveI := hG.smooth
    IsAdmissible π.representation ∧
      ∀ (J : Set (characterLattice T)) (ζ : cocharacterLattice T),
        IsStandardCocharacter i ν J ζ →
        ∀ (P M : GroupScheme (Spec (CommRingCat.of k)))
          (A : CommGroupScheme (Spec (CommRingCat.of k)))
          (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
          (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
          (ha : IsSplitComponent a),
          SubgroupFunctor.range p = standardParabolic i ν J →
          SubgroupFunctor.range (l ≫ p) = standardLevi i ν J →
          SubgroupFunctor.range p =
            Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) →
          SubgroupFunctor.range (l ≫ p) =
            Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) →
          SatisfiesNormalizedExponentConeCondition p l a hp hl ha π := by
  let := hG.smooth
  refine ⟨h.isAdmissible, ?_⟩
  intro J ζ hζ P M A p l a hp hl ha hP hM hPζ hMζ
  exact h.parabolic p l a hp hl ha

end Langlands.Aubert.General.RepresentedParabolic
