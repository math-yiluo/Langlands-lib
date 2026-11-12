import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.GroupScheme.Rational.LeviAmbientTransport
import Langlands.Representation.Exponents.ArbitraryParabolicLeviReparametrization

/-! # Transport of embeddings under conjugacy of represented inducing data -/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M M' U : GroupScheme (Spec (CommRingCat.of k))}

section Jacquet

variable [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]

local instance conjugateEmbeddingAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Conjugate the ambient parabolic and change the source of its Levi map.
The actual Jacquet quotient is translated by the ambient point. -/
def leviJacquetConjugatePresentationEquiv
    (p : P ⟶ G) (l : M' ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (e : M ≅ M') (g : rationalPoints G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
    haveI := (hl.iso_comp e).isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
    Representation.Equiv
      (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
        (rationalPoints.map e.hom))
      (((leviJacquetFunctor (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r
        (hp.comp_iso (G.innerIso g)) hr (hl.iso_comp e)
        (isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul)).obj π).representation) := by
  haveI := hl.isConnectedReductive.isAffineHom
  letI : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
  haveI := (hl.iso_comp e).isConnectedReductive.isAffineHom
  letI : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
  have hN : ∀ x : rationalPoints G,
      x ∈ pointImage (r ≫ (p ≫ (G.innerIso g).hom)) ↔
        g⁻¹ * x * g ∈ pointImage (r ≫ p) := by
    intro x
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (r ≫ p) g x
  have hL : ∀ x : rationalPoints G,
      x ∈ pointImage ((e.hom ≫ l) ≫ (p ≫ (G.innerIso g).hom)) ↔
        g⁻¹ * x * g ∈ pointImage (l ≫ p) := by
    intro x
    rw [Category.assoc, pointImage_iso_comp]
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (l ≫ p) g x
  apply normalizedJacquetRestrictedConjugationEquiv
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr)
    (isClosed_pointImage_comp (p ≫ (G.innerIso g).hom) r
      (hp.comp_iso (G.innerIso g)).isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r hr)
    g hN hL
    ((leviPointsEquiv p l hp hl).toMonoidHom.comp (rationalPoints.map e.hom))
    (leviPointsEquiv (p ≫ (G.innerIso g).hom) (e.hom ≫ l)
      (hp.comp_iso (G.innerIso g)) (hl.iso_comp e)).toMonoidHom
    _ π
  intro m
  apply Subtype.ext
  change g⁻¹ * rationalPoints.map (G.innerIso g).hom
      (rationalPoints.map (l ≫ p) (rationalPoints.map e.hom m)) * g =
    rationalPoints.map (l ≫ p) (rationalPoints.map e.hom m)
  rw [rationalPoints_map_innerIso]
  change g⁻¹ * (g * _ * g⁻¹) * g = _
  group

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- An irreducible representation that embeds into one induction also embeds
into the induction obtained by conjugating the parabolic and transporting its
inducing representation along an isomorphism of Levi presentations. -/
theorem exists_embedding_conjugate_presentation
    (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M' ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (e : M ≅ M') (g : rationalPoints G) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
    haveI := (hl.iso_comp e).isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ρ' : SmoothRep.{0, u, z} ℂ (rationalPoints M'))
      (_T : Representation.Equiv ρ.representation
        (ρ'.representation.comp (rationalPoints.map e.hom)))
      (σ : SmoothRep.{0, u, w} ℂ (rationalPoints G)),
      σ.IsIrreducible →
      (∃ f : σ.representation.IntertwiningMap
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ').representation,
        Function.Injective f) →
      ∃ f : σ.representation.IntertwiningMap
          ((leviInductionFunctor (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r
            (hp.comp_iso (G.innerIso g)) hr (hl.iso_comp e)
            (isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul)).obj ρ).representation,
        Function.Injective f := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
  have := (hl.iso_comp e).isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
  intro ρ ρ' T σ hσ ⟨f, hf⟩
  let := hσ
  have : Nontrivial σ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) σ.representation.asModule
  have hf0 : f ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : σ)
    apply hx
    apply hf
    simp [h]
  obtain ⟨F, _⟩ := leviFrobeniusReciprocity k G hG P M' U p l r hp hl hr hmul σ ρ'
  let J := leviJacquetConjugatePresentationEquiv p l r hp hl hr hmul e g σ
  let b := F f
  have hb : b ≠ 0 := F.map_ne_zero_iff.mpr hf0
  let bM : Representation.IntertwiningMap
      (((leviJacquetFunctor p l r hp hr hl hmul).obj σ).representation.comp
        (rationalPoints.map e.hom))
      (ρ'.representation.comp (rationalPoints.map e.hom)) :=
    { toLinearMap := b.toLinearMap
      isIntertwining' m := b.isIntertwining' (rationalPoints.map e.hom m) }
  let bQ := T.symm.toIntertwiningMap.comp (bM.comp J.symm.toIntertwiningMap)
  have hbQ : bQ ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y, b y ≠ 0 := by
      by_contra! hn
      exact hb (by ext y; exact hn y)
    intro hz
    have hval := congrArg (fun z => z (J y)) hz
    change T.toLinearEquiv.symm (b (J.toLinearEquiv.symm (J.toLinearEquiv y))) = 0 at hval
    rw [J.toLinearEquiv.symm_apply_apply] at hval
    exact hy (T.toLinearEquiv.symm.map_eq_zero_iff.mp hval)
  obtain ⟨FQ, _⟩ := leviFrobeniusReciprocity k G hG P M U
    (p ≫ (G.innerIso g).hom) (e.hom ≫ l) r
    (hp.comp_iso (G.innerIso g)) (hl.iso_comp e) hr
    (isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul) σ ρ
  refine ⟨FQ.symm bQ, ?_⟩
  exact (Representation.IsIrreducible.injective_or_eq_zero _).resolve_right
    (FQ.symm.map_ne_zero_iff.mpr hbQ)

/-- Association of the inducing data lets one keep a prescribed Levi embedding
in an ambient parabolic into whose induction the irreducible representation embeds. -/
theorem exists_parabolic_embedding_of_associated
    (hG : IsConnectedReductive G)
    (j : M ⟶ G) (p : P ⟶ G) (l : M' ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (e : M ≅ M') (g : rationalPoints G)
    (hAssoc : e.hom ≫ l ≫ p = j ≫ (G.innerIso g).hom) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
    haveI := (hl.iso_comp e).isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
    ∀ (ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
      (ρ' : SmoothRep.{0, u, z} ℂ (rationalPoints M'))
      (T : ρ ≃ₗ[ℂ] ρ'),
      (∀ (m : rationalPoints M) (x : ρ),
        T (ρ.representation m x) =
          ρ'.representation (rationalPoints.map e.hom m) (T x)) →
      ∀ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints G),
      σ.IsIrreducible →
      (∃ f : σ.representation.IntertwiningMap
          ((leviInductionFunctor p l r hp hr hl hmul).obj ρ').representation,
        Function.Injective f) →
      ∃ (Q UQ : GroupScheme (Spec (CommRingCat.of k)))
        (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : UQ ⟶ Q)
        (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
        (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
        (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
        lQ ≫ q = j ∧
        ∃ f : σ ⟶ (leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ρ,
          Function.Injective (SmoothRep.hom f) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M') := leviPointTopology l hl
  have := (hl.iso_comp e).isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology (e.hom ≫ l) (hl.iso_comp e)
  intro ρ ρ' T hT σ hσ ⟨f, hf⟩
  let TE : Representation.Equiv ρ.representation
      (ρ'.representation.comp (rationalPoints.map e.hom)) :=
    Representation.Equiv.mk T (fun m => by ext x; exact hT m x)
  obtain ⟨fQ, hfQ⟩ := exists_embedding_conjugate_presentation hG p l r hp hl hr hmul
    e g⁻¹ ρ ρ' TE σ hσ ⟨f, hf⟩
  refine ⟨P, U, p ≫ (G.innerIso g⁻¹).hom, e.hom ≫ l, r,
    hp.comp_iso (G.innerIso g⁻¹), hl.iso_comp e, hr,
    isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul, ?_, SmoothRep.ofHom fQ, hfQ⟩
  calc
    (e.hom ≫ l) ≫ (p ≫ (G.innerIso g⁻¹).hom) =
        (e.hom ≫ l ≫ p) ≫ (G.innerIso g⁻¹).hom := by simp only [Category.assoc]
    _ = (j ≫ (G.innerIso g).hom) ≫ (G.innerIso g⁻¹).hom := by rw [hAssoc]
    _ = j := by rw [innerIso_inv_hom]; simp

end Jacquet

end Langlands.Aubert.General.RepresentedParabolic
