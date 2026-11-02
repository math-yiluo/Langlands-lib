import Langlands.AlgebraicGeometry.AffineDifferentialSlice
import Langlands.AlgebraicGeometry.AffineLocalizedSliceChart
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Scheme slices from residue cotangent spanning -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Algebra TensorProduct

namespace Langlands.AlgebraicGeometry

variable {U R : Scheme.{u}}

local instance {B : Type u} [CommRing B] (q : Spec (CommRingCat.of B)) :
    q.asIdeal.IsPrime := (q : PrimeSpectrum B).isPrime

/-- A common section admits affine neighborhoods on which both maps land
in the same affine neighborhood of the chosen base point. -/
lemma exists_common_affine_slice_charts
    (t s : R ⟶ U) (e : U ⟶ R)
    (het : e ≫ t = 𝟙 U) (hes : e ≫ s = 𝟙 U) (x : U) :
    ∃ (V : U.Opens), IsAffineOpen V ∧ x ∈ V ∧
      ∃ (W : R.Opens), IsAffineOpen W ∧ e x ∈ W ∧
        W ≤ t ⁻¹ᵁ V ∧ W ≤ s ⁻¹ᵁ V := by
  obtain ⟨V, hV, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U) (U := ⊤) (Set.mem_univ x)
  have htx : t (e x) = x := by
    rw [← Scheme.Hom.comp_apply, het]
    rfl
  have hsx : s (e x) = x := by
    rw [← Scheme.Hom.comp_apply, hes]
    rfl
  have heV : e x ∈ t ⁻¹ᵁ V ⊓ s ⁻¹ᵁ V := by
    change t (e x) ∈ V ∧ s (e x) ∈ V
    simpa only [htx, hsx] using And.intro hx hx
  obtain ⟨W, hW, heW, hWV⟩ := exists_isAffineOpen_mem_and_subset heV
  exact ⟨V, hV, hx, W, hW, heW, fun y hy ↦ (hWV hy).1,
    fun y hy ↦ (hWV hy).2⟩

/-- Residue cotangent spanning on common affine charts supplies a finitely
presented slice and a formally etale stalk above the chosen source prime. -/
theorem exists_schemeSlice_formallyEtale_of_residue_span
    (t s : R ⟶ U) [Smooth s]
    (V : U.Opens) (hV : IsAffineOpen V) (W : R.Opens) (hW : IsAffineOpen W)
    (hWt : W ≤ t ⁻¹ᵁ V) (hWs : W ≤ s ⁻¹ᵁ V)
    (p : Ideal Γ(U, V)) (q : Spec (CommRingCat.of Γ(R, W)))
    (hpq : p ≤ q.asIdeal.comap (t.appLE V W hWt).hom)
    (hC : letI := (s.appLE V W hWs).hom.toAlgebra
      Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (Set.range (fun x : (t.appLE V W hWt).hom '' (p : Set Γ(U, V)) ↦
          (1 : IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) ⊗ₜ[Localization.AtPrime q.asIdeal]
            KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q.asIdeal)
              (algebraMap Γ(R, W) (Localization.AtPrime q.asIdeal) x))) = ⊤) :
    ∃ (I : Ideal Γ(U, V)), I.FG ∧ I ≤ p ∧
      LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) ∧
      ∃ b : (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec)
        t : Scheme.{u}),
        (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) t)
          b = hW.fromSpec q ∧
        ((pullback.snd _ _ ≫ s).stalkMap b).hom.FormallyEtale := by
  let := (s.appLE V W hWs).hom.toAlgebra
  let : Algebra.Smooth Γ(U, V) Γ(R, W) := by
    rw [← RingHom.smooth_algebraMap]
    exact s.smooth_appLE hV hW hWs
  obtain ⟨I, hIfg, hIp, g, hg, he⟩ :=
    exists_ideal_etale_quotient_of_residue_span (t.appLE V W hWt).hom p q.asIdeal hC
  refine ⟨I, hIfg, hIp,
    locallyOfFinitePresentation_affineQuotientChart V hV I hIfg, ?_⟩
  apply exists_formallyEtale_stalk_sliceChart t V hV W hW hWt I g s hWs q hg
    (hIp.trans hpq)
  let := he
  change ((algebraMap (Localization.Away g)
    ((Localization.Away g) ⧸ I.map
      ((algebraMap Γ(R, W) (Localization.Away g)).comp (t.appLE V W hWt).hom))).comp
        ((algebraMap Γ(R, W) (Localization.Away g)).comp
          (algebraMap Γ(U, V) Γ(R, W)))).Etale
  rw [← IsScalarTower.algebraMap_eq Γ(U, V) Γ(R, W) (Localization.Away g),
    ← IsScalarTower.algebraMap_eq, RingHom.etale_algebraMap]
  exact he

/-- Equation slices in affine charts are preimmersions, including when the
ideal is not finitely generated. -/
lemma isPreimmersion_affineQuotientChart
    (V : U.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(U, V)) :
    IsPreimmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec) := by
  infer_instance

/-- For a preimmersed slice, a point above an identity arrow is the
canonical identity point of that slice. -/
lemma exists_identity_formallyEtale_of_slice_point
    {U' : Scheme.{u}} (g : U' ⟶ U) [IsPreimmersion g]
    (t s : R ⟶ U) (e : U ⟶ R) (het : e ≫ t = 𝟙 U)
    (x : U) (b : (pullback g t : Scheme.{u}))
    (hb : pullback.snd g t b = e x)
    (hfe : ((pullback.snd g t ≫ s).stalkMap b).hom.FormallyEtale) :
    ∃ a : U', g a = x ∧
      ((pullback.snd g t ≫ s).stalkMap
        ((pullback.lift (𝟙 U') (g ≫ e)
          (by simp only [Category.id_comp, Category.assoc, het, Category.comp_id])) a)).hom.FormallyEtale := by
  have ha : g (pullback.fst g t b) = x := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      hb, ← Scheme.Hom.comp_apply, het]
    rfl
  have hid :
      (pullback.lift (𝟙 U') (g ≫ e)
        (by simp only [Category.id_comp, Category.assoc, het, Category.comp_id]))
          (pullback.fst g t b) = b := by
    apply (pullback.snd g t).isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply, ha, hb]
  refine ⟨pullback.fst g t b, ha, ?_⟩
  rwa [hid]

/-- Differential spanning at an identity point gives a finitely presented,
preimmersed slice with a formally etale canonical identity point. -/
theorem exists_identity_slice_of_residue_span
    (t s : R ⟶ U) [Smooth s] (e : U ⟶ R)
    (het : e ≫ t = 𝟙 U) (x : U)
    (V : U.Opens) (hV : IsAffineOpen V) (W : R.Opens) (hW : IsAffineOpen W)
    (hWt : W ≤ t ⁻¹ᵁ V) (hWs : W ≤ s ⁻¹ᵁ V)
    (p : Ideal Γ(U, V)) (q : Spec (CommRingCat.of Γ(R, W)))
    (hq : hW.fromSpec q = e x)
    (hpq : p ≤ q.asIdeal.comap (t.appLE V W hWt).hom)
    (hC : letI := (s.appLE V W hWs).hom.toAlgebra
      Submodule.span (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (Set.range (fun z : (t.appLE V W hWt).hom '' (p : Set Γ(U, V)) ↦
          (1 : IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) ⊗ₜ[Localization.AtPrime q.asIdeal]
            KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q.asIdeal)
              (algebraMap Γ(R, W) (Localization.AtPrime q.asIdeal) z))) = ⊤) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ U),
      IsPreimmersion g ∧ LocallyOfFinitePresentation g ∧
      ∃ a : Z, g a = x ∧
        ((pullback.snd g t ≫ s).stalkMap
          ((pullback.lift (𝟙 Z) (g ≫ e)
            (by simp only [Category.id_comp, Category.assoc, het, Category.comp_id])) a)).hom.FormallyEtale := by
  obtain ⟨I, _, _, hfg, b, hb, hfe⟩ :=
    exists_schemeSlice_formallyEtale_of_residue_span t s V hV W hW hWt hWs p q hpq hC
  let g : Spec (CommRingCat.of (Γ(U, V) ⧸ I)) ⟶ U :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.fromSpec
  have : IsPreimmersion g := isPreimmersion_affineQuotientChart V hV I
  refine ⟨_, g, inferInstance, hfg, ?_⟩
  exact exists_identity_formallyEtale_of_slice_point g t s e het x b (hb.trans hq) hfe

/-- The formally etale point supplied by a finitely presented slice has an
open neighborhood etale over the target. -/
lemma exists_etale_neighborhood_of_slice_point
    {U' : Scheme.{u}} (g : U' ⟶ U) [LocallyOfFinitePresentation g]
    (t s : R ⟶ U) [LocallyOfFinitePresentation s]
    (b : (pullback g t : Scheme.{u}))
    (hfe : ((pullback.snd g t ≫ s).stalkMap b).hom.FormallyEtale) :
    ∃ O : (pullback g t : Scheme.{u}).Opens, b ∈ O ∧
      Etale (O.ι ≫ (pullback.snd g t ≫ s)) :=
  exists_open_etale_of_formallyEtale_stalk _ b hfe

end Langlands.AlgebraicGeometry
