import Langlands.Representation.Geometric.FullIntersectionIrreducible
import Langlands.Representation.Exponents.IsoParabolicInduction
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Full pieces of the geometric lemma for a parabolic with the same Levi

Let `P = MN` and `Q` be represented parabolics whose Levi factors have the same source `M`.
For a double coset `P z Q` whose source intersection `P' = M ∩ zQz⁻¹` is all of `M`, the
graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}` of the geometric lemma (Renard VI.5.1) is the twist of
`ρ` by an automorphism of `M`, and that automorphism is conjugation by `z` inside `G` when
`Q` and `P` have the same Levi image. This generalizes the published self-intersection case
`Q = P`. For a supercuspidal `ρ` on which a split component acts by a character, each piece
is therefore zero, or irreducible with the split component acting by a conjugate character.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Split components are unique up to a unique-compatible isomorphism: for split components
`a : A ⟶ M`, `a' : A' ⟶ M'` and an isomorphism `τ : M ≅ M'`, some isomorphism `e : A ≅ A'`
satisfies `e ≫ a' = a ≫ τ`. -/
theorem IsSplitComponent.exists_iso_comp {M M' : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M'.X.hom] {A A' : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M'} (ha : IsSplitComponent a)
    (ha' : IsSplitComponent a') (τ : M ≅ M') :
    ∃ e : A ≅ A', CommGroupScheme.groupHom e.hom ≫ a' = a ≫ τ.hom := by
  have haτ := ha.comp_iso τ
  obtain ⟨f, hf⟩ := ha'.exists_factor ha.isCentralSplitTorus.1.1
    haτ.isCentralSplitTorus.isCentral
  have hfi : IsIso f := haτ.2 A' a' ha'.isCentralSplitTorus f hf
  exact ⟨{ hom := Additive.ofMul f
           inv := Additive.ofMul (inv f)
           hom_inv_id := congrArg Additive.ofMul (IsIso.hom_inv_id f)
           inv_hom_id := congrArg Additive.ofMul (IsIso.inv_hom_id f) }, hf⟩

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance leviConjugatePieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : M ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- For a full source intersection `P' = M` and a parabolic `Q` whose Levi has source `M`,
the automorphism `M ≅ L' ≅ M' ≅ M` of `M`: the inverse of `L' ⟶ Q' ⟶ M`, the intersection
isomorphism `φ`, and `M' ⟶ P' ⟶ M`. -/
def leviConjugation [IsIso D.p'] : M ≅ M :=
  haveI := D.isIso_l'_of_isIso_p'
  haveI := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso (Iso.refl M)
  (asIso (D.lQ' ≫ D.q')).symm ≪≫ D.φ ≪≫ asIso (D.l' ≫ D.p')

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
theorem leviConjugation_hom [IsIso D.p'] :
    haveI := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso (Iso.refl M)
    D.leviConjugation.hom = inv (D.lQ' ≫ D.q') ≫ D.φ.hom ≫ D.l' ≫ D.p' := by
  simp only [leviConjugation, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- When `Q` and `P` have the same Levi composite into `G`, the automorphism
`leviConjugation` is conjugation by `z` inside `G`. -/
theorem leviConjugation_comp [IsIso D.p'] (hcomp : lQ ≫ q = l ≫ p) :
    D.leviConjugation.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso (Iso.refl M)
  rw [D.leviConjugation_hom]
  simp only [Category.assoc]
  rw [D.φ_comp, ← Category.assoc lQ q, hcomp, ← Category.assoc D.lQ' D.q',
    IsIso.inv_hom_id_assoc, Category.assoc]

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- On rational points, `leviConjugation` sends the image of `b ∈ L'(F)` in `M(F)` to the
image of `φ(b) ∈ M'(F)`. -/
theorem leviConjugation_map_rationalPoints [IsIso D.p'] (b : rationalPoints D.L') :
    rationalPoints.map D.leviConjugation.hom (rationalPoints.map (D.lQ' ≫ D.q') b) =
      rationalPoints.map (D.l' ≫ D.p') (rationalPoints.map D.φ.hom b) := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'_of_iso (Iso.refl M)
  have hc : ∀ {A B C : GroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ B) (g : B ⟶ C)
      (x : rationalPoints A),
      rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
    intros
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have h : (D.lQ' ≫ D.q') ≫ D.leviConjugation.hom = D.φ.hom ≫ D.l' ≫ D.p' := by
    rw [D.leviConjugation_hom, IsIso.hom_inv_id_assoc]
  rw [← hc, ← hc, h]

/-- For a full source intersection `P' = M` and a parabolic `Q` whose Levi has source `M`, the
graded piece `D.pieceFunctor.obj ρ` is linearly equivalent to `ρ`: evaluation
at `1` on the induction along the full parabolic `Q'`, followed by the identification of the
Jacquet module along the full parabolic `P'` with `ρ`. -/
def leviPieceEquiv [IsIso D.p']
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ :=
  haveI := hl.isConnectedReductive.isAffineHom
  letI := leviPointTopology l hl
  haveI := leviPoints_locallyCompactSpace p l hp hl
  haveI := leviPoints_nonarchimedeanGroup p l hp hl
  haveI := hlQ.isConnectedReductive.isAffineHom
  letI := leviPointTopology lQ hlQ
  haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
  haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  letI := leviPointTopology D.l' D.hl'
  letI := leviPointTopology D.lQ' D.hlQ'
  haveI := D.isIso_l'_of_isIso_p'
  haveI := D.isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  haveI := D.isIso_lQ'_of_isIso_p'_of_iso (Iso.refl M)
  (isoParabolicInductionEquiv D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ'
      ((SmoothRep.pullbackFunctor D.e).obj
        ((leviJacquetFunctor D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul').obj ρ))).trans
    (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ)

/-- The equivalence `leviPieceEquiv` intertwines the action of `m ∈ M(F)` on the graded piece
with the action on `ρ` of the image of `m` under `leviConjugation`. -/
theorem leviPieceEquiv_representation [IsIso D.p']
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (m : rationalPoints M) (x : D.pieceFunctor.obj ρ) :
    letI := leviPointTopology l hl
    D.leviPieceEquiv ρ ((D.pieceFunctor.obj ρ).ρ m x) =
      ρ.representation (rationalPoints.map D.leviConjugation.hom m) (D.leviPieceEquiv ρ x) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  have := hlQ.isConnectedReductive.isAffineHom
  let := leviPointTopology lQ hlQ
  have := leviPoints_locallyCompactSpace q lQ hq hlQ
  have := leviPoints_nonarchimedeanGroup q lQ hq hlQ
  let := leviPointTopology D.l' D.hl'
  let := leviPointTopology D.lQ' D.hlQ'
  have := D.isIso_l'_of_isIso_p'
  have := D.isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  have := D.isIso_lQ'_of_isIso_p'_of_iso (Iso.refl M)
  obtain ⟨b, rfl⟩ : ∃ b, rationalPoints.map (D.lQ' ≫ D.q') b = m :=
    ⟨rationalPoints.map (inv (D.lQ' ≫ D.q')) m, by
      rw [← pointMap_comp_apply, IsIso.inv_hom_id]
      simp [rationalPoints.map_apply]⟩
  rw [D.leviConjugation_map_rationalPoints, ← D.e_apply]
  exact (congrArg (fullLeviJacquetEquiv D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ)
    (isoParabolicInductionEquiv_map D.q' D.lQ' D.rQ' D.hq' D.hrQ' D.hlQ' D.hmulQ' _ b x)).trans
      (fullLeviJacquetEquiv_representation D.p' D.l' D.r' D.hp' D.hr' D.hl' D.hmul' ρ (D.e b) _)

/-- **Pieces of the geometric lemma along a parabolic with Levi `M`.** Let `Q` have a Levi
factor with source `M` and the same composite into `G` as `l ≫ p`. Let `ρ` be an irreducible
representation of `M(F)` whose Jacquet modules along proper parabolics of `M` vanish, and let
a split component `a : A ⟶ M` act on `ρ` through a character `ωA`. Then the graded piece at
`P z Q` is zero, or `P' = M`, the piece is irreducible, and for some automorphism `ψ` of `M`
that is conjugation by `z` in `G` and some lift `e : A ≅ A` of `ψ`, every `a(t)` acts on the
piece by the scalar `ωA(e(t))`. -/
theorem subsingleton_or_isIrreducible_scalar (hcomp : lQ ≫ q = l ≫ p)
    (ρ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hirr : letI := leviPointTopology l hl; ρ.IsIrreducible)
    (hsuper : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (ωA : rationalPoints A.toGrp →* ℂˣ)
    (hωA : letI := leviPointTopology l hl; ∀ (t : rationalPoints A.toGrp) (y : ρ),
      ρ.representation (rationalPoints.map a t) y = (ωA t : ℂ) • y) :
    Subsingleton (D.pieceFunctor.obj ρ) ∨
      (IsIso D.p' ∧ (D.pieceFunctor.obj ρ).ρ.IsIrreducible ∧
        ∃ (ψ : M ≅ M) (e : A ≅ A), ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom ∧
          CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom ∧
          ∀ (t : rationalPoints A.toGrp) (y : D.pieceFunctor.obj ρ),
            (D.pieceFunctor.obj ρ).ρ (rationalPoints.map a t) y =
              (ωA (rationalPoints.map (CommGroupScheme.groupHom e.hom) t) : ℂ) • y) := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  by_cases h : IsIso D.p'
  · obtain ⟨e, he⟩ := IsSplitComponent.exists_iso_comp ha ha D.leviConjugation
    refine Or.inr ⟨h, D.pieceFunctor_isIrreducible_of_isIso_source_of_iso ρ (Iso.refl M) hirr,
      D.leviConjugation, e, D.leviConjugation_comp hcomp, he, fun t y => ?_⟩
    apply (D.leviPieceEquiv ρ).injective
    rw [LinearEquiv.map_smul, D.leviPieceEquiv_representation, ← pointMap_comp_apply, ← he,
      pointMap_comp_apply, hωA]
  · exact Or.inl (D.subsingleton_pieceFunctor_obj ρ
      (hsuper _ _ _ D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' h))

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
