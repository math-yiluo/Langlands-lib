import Mathlib

/-! # Differential generation from a monomorphic relation -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

open _root_.AlgebraicGeometry

/-- The graph of a derivation is a ring homomorphism into the trivial square-zero extension. -/
def derivationGraph {A : Type v} {B : Type w} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    [Module A M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (δ : Derivation A B M) : B →+* TrivSqZeroExt B M where
  toFun b := ⟨b, δ b⟩
  map_one' := TrivSqZeroExt.ext rfl δ.map_one_eq_zero
  map_zero' := TrivSqZeroExt.ext rfl (map_zero δ)
  map_add' a b := TrivSqZeroExt.ext rfl (map_add δ a b)
  map_mul' a b := TrivSqZeroExt.ext rfl (by
    change δ (a * b) = a • δ b + MulOpposite.op b • δ a
    rw [op_smul_eq_smul, δ.leibniz])

@[simp]
lemma derivationGraph_snd {A : Type v} {B : Type w} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module B M]
    [Module A M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (δ : Derivation A B M) (b : B) :
    (derivationGraph δ b).snd = δ b := rfl

variable {U R : Scheme.{u}} {t s : R ⟶ U}

/-- The two chart maps of a monomorphic relation jointly determine ring homomorphisms. -/
lemma ringHom_ext_of_mono (hmono : Mono (prod.lift t s))
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    {C : Type u} [CommRing C] (f g : Γ(R, W) →+* C)
    (hs : f.comp (s.appLE V W hWs).hom = g.comp (s.appLE V W hWs).hom)
    (ht : f.comp (t.appLE V W hWt).hom = g.comp (t.appLE V W hWt).hom) :
    f = g := by
  have hspec : Spec.map (CommRingCat.ofHom f) ≫ hW.fromSpec =
      Spec.map (CommRingCat.ofHom g) ≫ hW.fromSpec := by
    apply (cancel_mono (prod.lift t s)).mp
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      rw [← hV.SpecMap_appLE_fromSpec t hW hWt, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc]
      congr 2
      exact CommRingCat.hom_ext ht
    · simp only [Category.assoc, prod.lift_snd]
      rw [← hV.SpecMap_appLE_fromSpec s hW hWs, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc]
      congr 2
      exact CommRingCat.hom_ext hs
  exact congrArg CommRingCat.Hom.hom
    (Spec.map_injective ((cancel_mono hW.fromSpec).mp hspec))

/-- A derivation over the source chart vanishing on the target chart is zero. -/
lemma derivation_eq_zero_of_mono (hmono : Mono (prod.lift t s))
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    {M : Type u} [AddCommGroup M] [Module Γ(R, W) M] [Module Γ(U, V) M]
    (δ : Derivation Γ(U, V) Γ(R, W) M)
    (hδ : ∀ a, δ ((t.appLE V W hWt).hom a) = 0) : δ = 0 := by
  let : Module Γ(R, W)ᵐᵒᵖ M :=
    Module.compHom M (RingEquiv.toOpposite Γ(R, W)).symm.toRingHom
  let : IsCentralScalar Γ(R, W) M := ⟨fun _ _ ↦ rfl⟩
  have heq : derivationGraph δ = TrivSqZeroExt.inlHom Γ(R, W) M := by
    apply ringHom_ext_of_mono hmono hV hW hWs hWt
    · apply RingHom.ext
      intro a
      exact TrivSqZeroExt.ext rfl (by
        change δ ((s.appLE V W hWs).hom a) = 0
        rw [← hσ, δ.map_algebraMap])
    · apply RingHom.ext
      intro a
      exact TrivSqZeroExt.ext rfl (hδ a)
  ext b
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun heq b)

/-- The target-chart differentials generate the relative differentials of the source chart. -/
theorem span_targetDifferentials_eq_top_of_mono (hmono : Mono (prod.lift t s))
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom) :
    Submodule.span Γ(R, W)
      (Set.range fun a ↦ KaehlerDifferential.D Γ(U, V) Γ(R, W)
        ((t.appLE V W hWt).hom a)) = ⊤ := by
  let N := Submodule.span Γ(R, W)
    (Set.range fun a ↦ KaehlerDifferential.D Γ(U, V) Γ(R, W)
      ((t.appLE V W hWt).hom a))
  have hδ : N.mkQ.compDer (KaehlerDifferential.D Γ(U, V) Γ(R, W)) = 0 := by
    apply derivation_eq_zero_of_mono hmono hV hW hWs hWt hσ
    intro a
    change N.mkQ (KaehlerDifferential.D Γ(U, V) Γ(R, W)
      ((t.appLE V W hWt).hom a)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨a, rfl⟩)
  apply top_unique
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).mp (Derivation.congr_fun hδ b)

/-- The target-chart differentials still generate after any localization of the relation chart. -/
theorem span_targetDifferentials_localization_eq_top_of_mono
    (hmono : Mono (prod.lift t s))
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (S : Submonoid Γ(R, W)) (T : Type*) [CommRing T]
    [Algebra Γ(R, W) T] [Algebra Γ(U, V) T]
    [IsScalarTower Γ(U, V) Γ(R, W) T] [IsLocalization S T] :
    Submodule.span T (Set.range fun a ↦ KaehlerDifferential.D Γ(U, V) T
      (algebraMap Γ(R, W) T ((t.appLE V W hWt).hom a))) = ⊤ := by
  have h := span_eq_top_of_isLocalizedModule T S
    (KaehlerDifferential.map Γ(U, V) Γ(U, V) Γ(R, W) T)
    (span_targetDifferentials_eq_top_of_mono hmono hV hW hWs hWt hσ)
  simpa only [← Set.range_comp, Function.comp_def, KaehlerDifferential.map_D] using h

/-- In particular, target-chart differentials generate at every prime of the relation chart. -/
lemma span_targetDifferentials_atPrime_eq_top_of_mono
    (hmono : Mono (prod.lift t s))
    {V : U.Opens} (hV : IsAffineOpen V) {W : R.Opens} (hW : IsAffineOpen W)
    (hWs : W ≤ s ⁻¹ᵁ V) (hWt : W ≤ t ⁻¹ᵁ V)
    [Algebra Γ(U, V) Γ(R, W)]
    (hσ : algebraMap Γ(U, V) Γ(R, W) = (s.appLE V W hWs).hom)
    (q : Ideal Γ(R, W)) [q.IsPrime] :
    Submodule.span (Localization.AtPrime q)
      (Set.range fun a ↦ KaehlerDifferential.D Γ(U, V) (Localization.AtPrime q)
        (algebraMap Γ(R, W) (Localization.AtPrime q)
          ((t.appLE V W hWt).hom a))) = ⊤ :=
  span_targetDifferentials_localization_eq_top_of_mono hmono hV hW hWs hWt hσ
    q.primeCompl (Localization.AtPrime q)

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
