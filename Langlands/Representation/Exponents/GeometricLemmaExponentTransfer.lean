import Langlands.Representation.Exponents.GeometricLemmaSplitComponent
import Langlands.Representation.Exponents.ArbitraryParabolicInductionComparison
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.EquivalencePullback
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Exponents through the graded pieces of the geometric lemma

A generalized eigencharacter of a functor glued from pieces occurs in one of the pieces.
For the pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}` of an intersection datum, an exponent of `A_L`
restricts from a normalized Jacquet exponent of `A_{M'}` along `P'`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Postcomposing a split component with an isomorphism gives a split component. -/
theorem IsSplitComponent.comp_iso {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G}
    (hi : IsSplitComponent i) (e : G ≅ G') : IsSplitComponent (i ≫ e.hom) := by
  refine ⟨⟨(IsSplitSubtorus.comp_iso_iff i e).mpr hi.1.1, hi.1.2.comp_iso e⟩, ?_⟩
  intro A' i' hi' f hf
  apply hi.2 A' (i' ≫ e.inv)
    ⟨(IsSplitSubtorus.comp_iso_iff i' e.symm).mpr hi'.1, hi'.2.comp_iso e.symm⟩ f
  rw [← Category.assoc, hf, Category.assoc, e.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme

namespace Langlands

/-- A generalized eigencharacter of a functor glued from pieces is a generalized
eigencharacter of one of the pieces, at the same object and after the same restriction. -/
theorem IsGluedFrom.exists_isGeneralizedEigencharacter {R : Type*} [CommRing R]
    {G : Type*} [Group G] {H : Type*} [Group H] {C : Type*} [Category C]
    {F : C ⥤ Rep.{v} R G} {n : ℕ} {pieces : Fin n → C ⥤ Rep.{v} R G}
    (h : IsGluedFrom F pieces) (X : C) (j : H →* G) (χ : H →* Rˣ)
    (hχ : IsGeneralizedEigencharacter ((F.obj X).ρ.comp j) χ) :
    ∃ i, IsGeneralizedEigencharacter (((pieces i).obj X).ρ.comp j) χ := by
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨i, hi⟩ := s.exists_graded_isGeneralizedEigencharacter X j χ hχ
  obtain ⟨iso⟩ := hs i
  exact ⟨e i, (isGeneralizedEigencharacter_iff_of_equiv
    (Cohomology.HyperextAbutment.equivComp (Representation.equivOfIso (iso.app X)) j) χ).mp hi⟩

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Ambient

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance exponentTransferAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A AG : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ M} {aG : AG.toGrp ⟶ G}

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- `leviPointsEquiv` sends the points of a torus of `M` to their split-component image. -/
theorem leviPointsEquiv_comp_map (a : A.toGrp ⟶ M) :
    letI := leviPointTopology l hl
    (leviPointsEquiv p l hp hl).toMonoidHom.comp (rationalPoints.map a) =
      splitComponentPointsMap (l ≫ p) a :=
  MonoidHom.ext fun _ => Subtype.ext rfl

/-- A normalized Jacquet exponent is a generalized eigencharacter of `A(F)`, acting through
`M(F)`, on the Jacquet module transported to `M(F)`. -/
theorem isNormalizedJacquetExponent_iff_leviJacquet (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (χ : rationalPoints A.toGrp →* ℂˣ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ↔
      letI := leviPointTopology l hl
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
          (rationalPoints.map a)) χ := by
  rw [isNormalizedJacquetExponent_iff, ← leviPointsEquiv_comp_map p l hp hl a]
  rfl

/-- Renard VII.1.1 (i) for representations of `M(F)` itself: an exponent of `A_G` on the
normalized induction of an admissible `τ` restricts along `f` from a smooth generalized
eigencharacter of `A_M` on `τ`. -/
theorem exists_isGeneralizedEigencharacter_of_leviInduction (ha : IsSplitComponent a)
    (haG : IsSplitComponent aG) (f : AG ⟶ A)
    (hf : CommGroupScheme.groupHom f ≫ a ≫ l ≫ p = aG) :
    letI := leviPointTopology l hl
    ∀ (τ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), τ.IsAdmissible →
      ∀ χ : rationalPoints AG.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter
          (((leviInductionFunctor p l r hp hr hl hmul).obj τ).representation.comp
            (rationalPoints.map aG)) χ →
        ∃ ψ : rationalPoints A.toGrp →* ℂˣ,
          @IsOpen _ (RationalPointFamily.splitComponentPointTopology ha)
            (ψ.ker : Set (rationalPoints A.toGrp)) ∧
          IsGeneralizedEigencharacter (τ.representation.comp (rationalPoints.map a)) ψ ∧
          ψ.comp (rationalPoints.map (CommGroupScheme.groupHom f)) = χ := by
  let := leviPointTopology l hl
  intro τ hτ χ hχ
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let W := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm τ
  have hW : W.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv τ.representation _ hτ
  have hχ' : groupWeightSpace haG ((inductionFunctor p l r hp hr hl hmul).obj W) χ ≠ ⊥ :=
    (generalizedWeightSpace_ne_bot_iff (rationalPoints.map aG) χ
      haG.isCentralSplitTorus.isCentral.map_mem_center
      ((inductionFunctor p l r hp hr hl hmul).obj W).isSmooth).mpr hχ
  have he : ∀ t : rationalPoints AG.toGrp,
      ((splitComponentPointsMap (l ≫ p) a
        (rationalPoints.map (CommGroupScheme.groupHom f) t) : pointImage (l ≫ p)) :
          rationalPoints G) = rationalPoints.map aG t := by
    intro t
    rw [splitComponentPointsMap_val, ← pointMap_comp_apply, ← pointMap_comp_apply, ← hf]
  obtain ⟨ψ, ⟨hψo, hψ⟩, hψχ⟩ := inducedExponent_restrict p l r hp hl hr hmul ha haG
    (rationalPoints.map (CommGroupScheme.groupHom f)) he W χ hW hχ'
  refine ⟨ψ, hψo, ?_, hψχ⟩
  have hg := (generalizedWeightSpace_ne_bot_iff (splitComponentPointsMap (l ≫ p) a) ψ
    (splitComponentPointsMap_mem_center (l ≫ p) ha) W.isSmooth).mp hψ
  have hcomp : W.representation.comp (splitComponentPointsMap (l ≫ p) a) =
      τ.representation.comp (rationalPoints.map a) := by
    rw [← leviPointsEquiv_comp_map p l hp hl a]
    apply MonoidHom.ext
    intro t
    change τ.representation ((leviPointsEquiv p l hp hl).symm
      (leviPointsEquiv p l hp hl (rationalPoints.map a t))) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  rwa [hcomp] at hg

end Ambient

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance pieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
  {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ L} {a' : A'.toGrp ⟶ D.L'}

/-- An exponent of `A_L` on the piece `i^L_{Q'} ∘ ι ∘ r^M_{P'}` at `σ` restricts along
`f : A_L → A_{L'}` from a normalized Jacquet exponent of `σ` along `P'`, for the split
component `a' ≫ φ` of `M'`. The Jacquet module of `σ` along `P'` must be admissible. -/
theorem exists_isNormalizedJacquetExponent_of_piece (ha : IsSplitComponent a)
    (ha' : IsSplitComponent a') (f : A ⟶ A')
    (hf : CommGroupScheme.groupHom f ≫ a' ≫ D.lQ' ≫ D.q' = a) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI := leviPointTopology l hl
    haveI := leviPoints_locallyCompactSpace p l hp hl
    haveI := leviPoints_nonarchimedeanGroup p l hp hl
    letI := leviPointTopology D.l' D.hl'
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ).IsAdmissible →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsGeneralizedEigencharacter ((D.pieceFunctor.obj σ).ρ.comp (rationalPoints.map a)) χ →
        ∃ ψ : rationalPoints A'.toGrp →* ℂˣ,
          IsNormalizedJacquetExponent D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul'
              (ha'.comp_iso D.φ) σ ψ ∧
            ψ.comp (rationalPoints.map (CommGroupScheme.groupHom f)) = χ := by
  have := hl.isConnectedReductive.isAffineHom
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  intro σ hσ χ hχ
  let J := (leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj σ
  let τ := SmoothRep.pullback D.e J
  have hτ : τ.IsAdmissible := isAdmissible_comp_continuousMulEquiv J.representation D.e hσ
  obtain ⟨ψ, hψo, hψ, hψχ⟩ := exists_isGeneralizedEigencharacter_of_leviInduction
    D.q' D.lQ' D.rQ' D.hq' D.hlQ' D.hrQ' D.hmulQ' ha' ha f hf τ hτ χ hχ
  refine ⟨ψ, ?_, hψχ⟩
  rw [isNormalizedJacquetExponent_iff_leviJacquet]
  have hcomp : τ.representation.comp (rationalPoints.map a') =
      J.representation.comp (rationalPoints.map (a' ≫ D.φ.hom)) := by
    apply MonoidHom.ext
    intro t
    change J.representation (D.e (rationalPoints.map a' t)) = _
    rw [D.e_apply, ← pointMap_comp_apply]
    rfl
  rwa [hcomp] at hψ

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
