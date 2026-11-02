import Langlands.AlgebraicGeometry.SmoothRelationGoodPointCotangent

/-! # Replacing cotangent coordinates by simple integer equations -/

noncomputable section

universe u v w

open Polynomial TensorProduct IsLocalRing

namespace Langlands.AlgebraicGeometry.SmoothRelationGoodPoint

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The integer polynomial chain rule after a second ring map. -/
lemma differential_map_integerPolynomial (θ : A →+* B) (g : A) (P : Polynomial ℤ) :
    KaehlerDifferential.D A B (θ (aeval g P)) =
      θ (aeval g P.derivative) • KaehlerDifferential.D A B (θ g) := by
  have hmap (Q : Polynomial ℤ) : θ (aeval g Q) = aeval (θ g) Q := by
    simpa only [Polynomial.map_id] using
      (Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id ℤ) (ψ := θ)
        (by ext z; simp) Q g)
  rw [hmap, hmap]
  exact (KaehlerDifferential.D A B).restrictScalars ℤ |>.map_aeval P (θ g)

variable [IsLocalRing B] {ι : Type w}

/-- Replacing each coordinate by an integer polynomial with invertible derivative
preserves spanning in the residue cotangent space. -/
lemma span_simpleIntegerEquations_eq_top (θ : A →+* B) (g : ι → A)
    (P : ι → Polynomial ℤ)
    (hspan : Submodule.span (ResidueField B) (Set.range fun i ↦
      (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D A B (θ (g i))) = ⊤)
    (hderivative : ∀ i, θ (aeval (g i) (P i).derivative) ∉ maximalIdeal B) :
    Submodule.span (ResidueField B) (Set.range fun i ↦
      (1 : ResidueField B) ⊗ₜ[B]
        KaehlerDifferential.D A B (θ (aeval (g i) (P i)))) = ⊤ := by
  apply top_unique
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hd : residue B (θ (aeval (g i) (P i).derivative)) ≠ 0 :=
    fun h ↦ hderivative i ((residue_eq_zero_iff _).mp h)
  have hm := Submodule.subset_span (R := ResidueField B)
    (s := Set.range fun i ↦ (1 : ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.D A B (θ (aeval (g i) (P i)))) ⟨i, rfl⟩
  dsimp only at hm
  rw [differential_map_integerPolynomial, one_tmul_smul] at hm
  exact (Submodule.smul_mem_iff _ hd).mp hm

/-- At a point with equal contractions for the two ring maps, simple integer
equations for spanning coordinates imply the required cotangent span. -/
lemma cotangentSpan_eq_top_of_simpleIntegerRoots (θ : A →+* B) (g : ι → A)
    (hcomap : (maximalIdeal B).comap θ =
      (maximalIdeal B).comap (algebraMap A B))
    (hspan : Submodule.span (ResidueField B) (Set.range fun i ↦
      (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D A B (θ (g i))) = ⊤)
    (hsimple : ∀ i, ∃ P : Polynomial ℤ,
      θ (aeval (g i) P) ∈ maximalIdeal B ∧
      θ (aeval (g i) P.derivative) ∉ maximalIdeal B) :
    cotangentSpan θ = ⊤ := by
  classical
  choose P hzero hderivative using hsimple
  apply top_unique
  rw [← span_simpleIntegerEquations_eq_top θ g P hspan hderivative, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨aeval (g i) (P i), ?_⟩, rfl⟩
  rw [← hcomap]
  exact hzero i

/-- The maximal-ideal criterion follows from simple integer equations, with
the rationality and finite-generation hypotheses needed by the converse. -/
lemma maximalIdeal_eq_of_simpleIntegerRoots (θ : A →+* B) (g : ι → A)
    (hcomap : (maximalIdeal B).comap θ =
      (maximalIdeal B).comap (algebraMap A B))
    (hrat : IsRationalPoint A B)
    (hfg : ∃ N : Ideal B, N.FG ∧ N ≤ maximalIdeal B ∧
      maximalIdeal B ≤ ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔ N)
    (hspan : Submodule.span (ResidueField B) (Set.range fun i ↦
      (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D A B (θ (g i))) = ⊤)
    (hsimple : ∀ i, ∃ P : Polynomial ℤ,
      θ (aeval (g i) P) ∈ maximalIdeal B ∧
      θ (aeval (g i) P.derivative) ∉ maximalIdeal B) :
    maximalIdeal B = ((maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) ⊔
      ((maximalIdeal B).comap (algebraMap A B)).map θ :=
  maximalIdeal_eq_of_cotangentSpan_eq_top θ hcomap hrat hfg
    (cotangentSpan_eq_top_of_simpleIntegerRoots θ g hcomap hspan hsimple)

/-- Chosen integer equations vanishing in the common contracted prime whose
differentials still span the residue cotangent space. -/
structure SimpleIntegerCotangentData (θ : A →+* B) (g : ι → A) where
  polynomial : ι → Polynomial ℤ
  equation_mem : ∀ i, aeval (g i) (polynomial i) ∈
    (maximalIdeal B).comap (algebraMap A B)
  derivative_not_mem : ∀ i, θ (aeval (g i) (polynomial i).derivative) ∉ maximalIdeal B
  span_eq_top : Submodule.span (ResidueField B) (Set.range fun i ↦
    (1 : ResidueField B) ⊗ₜ[B]
      KaehlerDifferential.D A B (θ (aeval (g i) (polynomial i)))) = ⊤

/-- Choose vanishing integer equations for simple-root coordinates, retaining
their cotangent spanning property. -/
def simpleIntegerCotangentData (θ : A →+* B) (g : ι → A)
    (hcomap : (maximalIdeal B).comap θ =
      (maximalIdeal B).comap (algebraMap A B))
    (hspan : Submodule.span (ResidueField B) (Set.range fun i ↦
      (1 : ResidueField B) ⊗ₜ[B] KaehlerDifferential.D A B (θ (g i))) = ⊤)
    (hsimple : ∀ i, ∃ P : Polynomial ℤ,
      θ (aeval (g i) P) ∈ maximalIdeal B ∧
      θ (aeval (g i) P.derivative) ∉ maximalIdeal B) :
    SimpleIntegerCotangentData θ g := by
  classical
  choose P hzero hderivative using hsimple
  refine ⟨P, ?_, hderivative, span_simpleIntegerEquations_eq_top θ g P hspan hderivative⟩
  intro i
  rw [← hcomap]
  exact hzero i

end Langlands.AlgebraicGeometry.SmoothRelationGoodPoint
