import Langlands.GroupScheme.CorepresentedLinearEmbedding
import Langlands.GroupScheme.FiniteFieldTorsorPoint.LangAlgebra

/-! # Lang's theorem for corepresented group functors over a finite field -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.FiniteFieldTorsorPoint

open Corepresented.LinearEmbedding

variable (k : Type u) [Field k] [Fintype k]

/-- The `#k`-power Frobenius endomorphism of an algebra over the finite field `k`. -/
def frob (S : CommAlgCat.{u} (CommRingCat.of k)) : S ⟶ S :=
  CommAlgCat.ofHom (FiniteField.frobeniusAlgHom k S)

theorem frob_apply (S : CommAlgCat.{u} (CommRingCat.of k)) (x : S) :
    (frob k S).hom x = x ^ Fintype.card k := rfl

theorem frob_naturality {S T : CommAlgCat.{u} (CommRingCat.of k)} (g : S ⟶ T) :
    frob k S ≫ g = g ≫ frob k T := by
  ext x
  change g.hom (x ^ _) = (g.hom x) ^ _
  exact map_pow _ _ _

variable {k} {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The universal point of a corepresented functor. -/
def univ : F.obj B := pt e (𝟙 B)

/-- The Lang map `x ↦ x⁻¹ * Frob(x)` evaluated at the universal point. -/
def langUniv : F.obj B := (univ e)⁻¹ * F.map (frob k B) (univ e)

/-- The algebra endomorphism of the corepresenting algebra classifying the Lang map. -/
def langCo : B ⟶ B := cls e (langUniv e)

theorem map_langUniv {S : CommAlgCat.{u} (CommRingCat.of k)} (g : B ⟶ S) :
    F.map g (langUniv e) = (pt e g)⁻¹ * F.map (frob k S) (pt e g) := by
  simp only [langUniv, univ, map_mul, map_inv, ← pt_comp, Category.id_comp]
  rw [frob_naturality]

/-- A point is a Lang image as soon as its classifying map factors through `langCo`. -/
theorem exists_lang_eq_of_factor {S : CommAlgCat.{u} (CommRingCat.of k)} (y : F.obj S)
    (g : B ⟶ S) (hg : langCo e ≫ g = cls e y) :
    ∃ x : F.obj S, y = x⁻¹ * F.map (frob k S) x :=
  ⟨pt e g, by rw [← map_langUniv, ← pt_cls e (F.map g _), cls_map, ← langCo, hg, pt_cls]⟩

/-- The coordinate algebra is integral over the image of the Lang comorphism. -/
theorem isIntegral_langCo_range [Algebra.FiniteType (CommRingCat.of k) B] :
    Algebra.IsIntegral (langCo e).hom.range B := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  obtain ⟨s, hs⟩ := ‹Algebra.FiniteType (CommRingCat.of k) B›.out
  obtain ⟨n, a, hmul, hone, hspan⟩ :=
    Comodule.exists_matrix (coassoc e) (leftCounit e) (rightCounit e) s
  set ψ := (langCo e).hom
  have hmat : a * ψ.mapMatrix a = (frob k B).hom.mapMatrix a := by
    have h := congrArg (coeffHom e a hmul hone B)
      (mul_inv_cancel_left (univ e) (F.map (frob k B) (univ e)))
    rw [map_mul, coeffHom_apply, coeffHom_apply, coeffHom_apply, univ, cls_pt, cls_map,
      cls_pt] at h
    exact h
  have hrel : ∀ i j, a i j ^ Fintype.card k = ∑ l, a i l * ψ (a l j) := by
    intro i j
    rw [← (show ((frob k B).hom.mapMatrix a) i j = a i j ^ Fintype.card k from rfl), ← hmat,
      Matrix.mul_apply]
    rfl
  let v : Fin n × Fin n → B := fun p => a p.1 p.2
  have hgen : Algebra.adjoin ψ.range (Set.range v) = ⊤ := by
    have h1 : Algebra.adjoin (CommRingCat.of k) (Set.range v) = ⊤ := by
      rw [eq_top_iff, ← hs]
      exact Algebra.adjoin_le fun b hb => Algebra.span_le_adjoin _ _ (hspan b hb)
    rw [← Algebra.adjoin_adjoin_of_tower (R := CommRingCat.of k), h1, Algebra.coe_top,
      Algebra.adjoin_univ]
  have hq : 2 ≤ Fintype.card k := Fintype.one_lt_card
  have hfin : Module.Finite ψ.range B := by
    refine finite_of_pow_mem_span v hgen hq fun p => ?_
    rw [show v p ^ Fintype.card k =
        ∑ l, (⟨ψ (a l p.2), ψ.mem_range_self _⟩ : ψ.range) • v (p.1, l) from ?_]
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(p.1, l), rfl⟩))
    · rw [hrel]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
  exact Algebra.IsIntegral.of_finite _ _

include e in
/-- **Lang's theorem** for a corepresented group functor over a finite field whose
corepresenting algebra is a finitely generated domain: over an algebraically closed field every
point has the form `x⁻¹ * Frob(x)`. -/
theorem exists_lang_eq [IsDomain B] [Algebra.FiniteType (CommRingCat.of k) B]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
    (y : F.obj (CommAlgCat.of (CommRingCat.of k) K)) :
    ∃ x, y = x⁻¹ * F.map (frob k _) x := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  have := isIntegral_langCo_range e
  obtain ⟨g, hg⟩ := exists_comp_eq_of_isIntegral_range (langCo e).hom (cls e y).hom
  refine exists_lang_eq_of_factor e y (CommAlgCat.ofHom g) ?_
  ext b
  exact congr($hg b)

end Langlands.GroupScheme.FiniteFieldTorsorPoint
