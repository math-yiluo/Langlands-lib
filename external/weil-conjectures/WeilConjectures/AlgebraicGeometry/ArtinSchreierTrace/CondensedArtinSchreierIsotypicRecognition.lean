/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedCharacterImageEvaluationMono
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.Mathlib.CategoryTheory.Conj

/-! # Recognition of condensed character images

Source: blueprint lemma-artin-schreier-character-sheaf, proof Step 5, and the finite-torsor
isotypic argument in `WeilConjectures.SixFunctors.Finite.Isotypic`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ArtinSchreierTrace

private theorem comp_average_ring
    {C : Type*} [Category C] [Preadditive C]
    {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] [Fintype G]
    [Invertible (Fintype.card G : R)] {A B : C}
    (β : R →+* End B) (τ : G → (B ⟶ B)) (χ : AddChar G R) (φ : A ⟶ B)
    (hφ : ∀ a, φ ≫ τ a = φ ≫ (β (χ a)).asHom) :
    φ ≫ (∑ a : G, τ a ≫ (β (⅟(Fintype.card G : R) * χ (-a))).asHom) = φ := by
  rw [Preadditive.comp_sum]
  calc
    _ = ∑ _a : G, φ ≫ (β (⅟(Fintype.card G : R))).asHom := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Category.assoc, hφ a, Category.assoc]
      change φ ≫ (β (⅟(Fintype.card G : R) * χ (-a)) * β (χ a)).asHom = _
      rw [← map_mul, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, mul_one]
    _ = φ ≫ (β (∑ _a : G, ⅟(Fintype.card G : R))).asHom := by
      rw [map_sum, End.sum_asHom, Preadditive.comp_sum]
    _ = φ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_invOf_self, map_one]
      exact Category.comp_id φ
private theorem factor_isIso
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) {A B : C} {N : D} (P : B ⟶ B) [HasImage P] (φ : A ⟶ B)
    (ε : L.obj B ⟶ N) (hfix : φ ≫ P = φ)
    [Mono (L.map (image.ι P) ≫ ε)] [IsIso (L.map φ ≫ ε)] :
    IsIso (L.map (φ ≫ factorThruImage P)) := by
  let M := L.map (image.ι P) ≫ ε
  have hfac : L.map (φ ≫ factorThruImage P) ≫ M = L.map φ ≫ ε := by
    dsimp only [M]
    rw [← Category.assoc, ← Functor.map_comp, Category.assoc, image.fac, hfix]
  have : IsSplitEpi M := ⟨⟨inv (L.map φ ≫ ε) ≫ L.map (φ ≫ factorThruImage P), by
    rw [Category.assoc, hfac, IsIso.inv_hom_id]⟩⟩
  have : IsIso M := isIso_of_mono_of_isSplitEpi _
  have hmap : L.map (φ ≫ factorThruImage P) = (L.map φ ≫ ε) ≫ inv M := by
    rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hmap]
  infer_instance

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.lowerStar
  ProEtale.CondensedRing.upperStarLowerStarAdjunction

/-- An eigenmap into the direct image of the regular module whose adjoint trivializes
its domain. Scalars act on the regular coefficient module before direct image.
Source: finite-cover isotypic descent in blueprint lemma-artin-schreier-character-sheaf Step 5
(blueprint: lem-fd-as-condensed-isotypic-recognition). -/
def CondensedEigenmap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    (G : Type u) [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    {F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (φ : F ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj
      (condensedUnit Λ Y.left)) : Prop :=
  (∀ a : G, φ ≫ condensedPull Λ (σ (Multiplicative.ofAdd a)).asIso.hom =
    φ ≫ (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
      (Mod.regularEndRingHom
        (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y.left) (χ a))).asHom) ∧
  IsIso ((ProEtale.CondensedRing.upperStar Λ Y.hom).map φ ≫
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app
      (condensedUnit Λ Y.left))

private theorem projector_fixes_eigenmap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    (G : Type u) [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    (hq : IsUnit (Fintype.card G : MonObj.Γ Λ))
    {F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (φ : F ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj
      (condensedUnit Λ Y.left)) (hφ : CondensedEigenmap Λ Y G σ χ φ) :
    φ ≫ (condensedProjector Λ G Y
      (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom = φ := by
  classical
  let : Invertible (Fintype.card G : MonObj.Γ Λ) := hq.invertible
  let β : MonObj.Γ Λ →+* End ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj
      (condensedUnit Λ Y.left)) :=
    ((ProEtale.CondensedRing.lowerStar Λ Y.hom).mapEndRingHom
      (condensedUnit Λ Y.left)).comp
        (Mod.regularEndRingHom.comp
          (MonObj.Γ.mapFunctor (ProEtale.upperStarFromPoint Y.left) (R := Λ)))
  unfold condensedProjector
  simp only [Ring.inverse_invertible, End.sum_asHom]
  exact comp_average_ring β (fun a ↦ condensedPull Λ (σ (Multiplicative.ofAdd a)).asIso.hom)
    χ φ hφ.1

private theorem exists_cover_satisfying
    {X Y : Scheme.{u}} (p : Y ⟶ X) [Etale p]
    (hsurj : Function.Surjective p.base)
    (Q : ∀ {Z : Scheme.{u}}, (Z ⟶ X) → Prop) (hp : Q p) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : U.I₀, Q (U.f i) := by
  let U₀ : Scheme.Cover.{u} Scheme.etalePrecoverage X :=
    .singleton p
      ((Scheme.singleton_mem_precoverage_iff (P := @AlgebraicGeometry.Etale) _).2
        ⟨hsurj, inferInstance⟩)
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    ⟨U₀.toPreZeroHypercover, Scheme.etalePrecoverage_le_proetalePrecoverage X U₀.mem₀⟩
  refine ⟨U, ?_⟩
  intro i
  change Q p
  exact hp

-- Image and covering comparisons involve the concrete condensed module functors.
/-- A character eigenmap with invertible adjoint identifies its domain locally with the
image of the averaging projector on a finite etale torsor.
Source: blueprint lemma-artin-schreier-character-sheaf Step 5, finite-cover eigenfunctions;
the argument of `Etale.isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent`
(blueprint: lem-fd-as-condensed-isotypic-recognition).

Proof: equivariance and invertibility of the group order imply that averaging fixes
φ. Factor φ through the projector image using φ followed by factorThruImage.
After splitting the finite etale cover, the pushforward is a finite product of regular
coefficient modules. Transitivity makes a character eigenfunction determined by one
coordinate: translation carries every other coordinate to that coordinate and χ(a)
is a unit with inverse χ(-a). Thus evaluation of the image is monic. Its composite
with the factored φ is the invertible adjoint, so evaluation is also split epic and
hence invertible. Cancelling it proves that the factored φ is invertible on every
splitting chart. These charts cover X by surjectivity; the empty base is included. -/
theorem condensed_isotypic_recognition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (Y : Over X)
    [IsFinite Y.hom] [Etale Y.hom] (hsurj : Function.Surjective Y.hom.base)
    (G : Type u) [AddCommGroup G] [Fintype G]
    (σ : Multiplicative G →* Aut Y) (χ : AddChar G (MonObj.Γ Λ))
    (hq : IsUnit (Fintype.card G : MonObj.Γ Λ))
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ Y.left), s ≫ Y.hom = t ≫ Y.hom →
        ∃ a : G, s = t ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left)
    {F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (φ : F ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj
      (condensedUnit Λ Y.left)) (hφ : CondensedEigenmap Λ Y G σ χ φ) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ i : U.I₀, IsIso ((ProEtale.CondensedRing.upperStar Λ (U.f i)).map
        (φ ≫ factorThruImage (condensedProjector Λ G Y
          (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom)) := by
  classical
  let P := (condensedProjector Λ G Y
    (fun a ↦ (σ (Multiplicative.ofAdd a)).asIso.hom) χ).asHom
  have hfix : φ ≫ P = φ := projector_fixes_eigenmap Λ Y G σ χ hq φ hφ
  let L := ProEtale.CondensedRing.upperStar Λ Y.hom
  let ε := (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ Y.hom).counit.app
    (condensedUnit Λ Y.left)
  let M := L.map (image.ι P) ≫ ε
  have : Mono M := condensed_character_image_evaluation_mono Λ Y G σ χ hq htrans
  have : IsIso (L.map φ ≫ ε) := hφ.2
  have : IsIso (L.map (φ ≫ factorThruImage P)) := factor_isIso L P φ ε hfix
  exact exists_cover_satisfying Y.hom hsurj
    (fun {Z} p ↦ IsIso ((ProEtale.CondensedRing.upperStar Λ p).map
      (φ ≫ factorThruImage P))) inferInstance

end AlgebraicGeometry.ArtinSchreierTrace
