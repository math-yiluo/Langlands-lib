import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalRestrictionBound

/-! # Bounded algebra-map descent on actual finite full-domain covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {U : Domain K A} (c : FiniteCover U)

/-- A finite full-domain cover detects the original stored algebra norm up to a
positive constant, by an actual relative rational refinement. -/
theorem exists_algebraRestrictionBound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : U.algebra, ‖a‖ ≤ C * ‖c.algebraRestrict a‖ := by
  classical
  let r := c.relativeRationalRefinement
  obtain ⟨C, hCpos, hC⟩ := RationalChart.exists_finiteRestrictionBound r.chart r.covers
  choose M hMpos hM using fun i => (r.map i).restriction.bounded
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpos i).le
  have hMi (i : Fin r.size) : M i ≤ (∑ j, M j) + 1 := by
    apply (Finset.single_le_sum (fun j _ => (hMpos j).le) (Finset.mem_univ i)).trans
    linarith
  have hprod (a : U.algebra) :
      ‖fun i => (r.chart i).baseMap a‖ ≤
        ((∑ i, M i) + 1) * ‖c.algebraRestrict a‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _))).2
    intro i
    have heq := congrArg (fun f : BoundedAlgHom K U.algebra (r.chart i).algebra => f a)
      (r.restriction_comp i)
    rw [← heq]
    exact (hM i _).trans
      (mul_le_mul (hMi i) (norm_le_pi_norm (c.algebraRestrict a) (r.index i))
        (norm_nonneg _) (by linarith))
  refine ⟨C * ((∑ i, M i) + 1), mul_pos hCpos (by linarith), fun a => ?_⟩
  exact (hC a).trans ((mul_le_mul_of_nonneg_left (hprod a) hCpos.le).trans_eq
    (mul_assoc _ _ _).symm)

/-- A chosen positive inverse norm constant for the original stored restrictions. -/
def algebraRestrictionBound : ℝ := c.exists_algebraRestrictionBound.choose

theorem algebraRestrictionBound_pos : 0 < c.algebraRestrictionBound :=
  c.exists_algebraRestrictionBound.choose_spec.1

theorem norm_le_algebraRestrictionBound (a : U.algebra) :
    ‖a‖ ≤ c.algebraRestrictionBound * ‖c.algebraRestrict a‖ :=
  c.exists_algebraRestrictionBound.choose_spec.2 a

variable {S : Type v} [NormedCommRing S] [NormedAlgebra K S]

/-- Boundedness of an algebra homomorphism is detected on any finite full-domain cover. -/
theorem bounded_of_restrictions (f : S →ₐ[K] U.algebra)
    (hf : ∀ i : Fin c.size,
      ((c.map i).restriction.toAlgHom.comp f).toRingHom.IsBounded) :
    f.toRingHom.IsBounded := by
  classical
  choose M hMpos hM using hf
  have hsum : 0 ≤ ∑ i, M i := Finset.sum_nonneg fun i _ => (hMpos i).le
  have hMi (i : Fin c.size) : M i ≤ (∑ j, M j) + 1 := by
    apply (Finset.single_le_sum (fun j _ => (hMpos j).le) (Finset.mem_univ i)).trans
    linarith
  refine ⟨c.algebraRestrictionBound * ((∑ i, M i) + 1),
    mul_pos c.algebraRestrictionBound_pos (by linarith), fun s => ?_⟩
  have hh : ‖c.algebraRestrict (f s)‖ ≤ ((∑ i, M i) + 1) * ‖s‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by linarith) (norm_nonneg s))).2
    intro i
    exact (hM i s).trans (mul_le_mul_of_nonneg_right (hMi i) (norm_nonneg s))
  exact (c.norm_le_algebraRestrictionBound (f s)).trans
    ((mul_le_mul_of_nonneg_left hh c.algebraRestrictionBound_pos.le).trans_eq
      (mul_assoc _ _ _).symm)

/-- Local bounded maps agree after every actual full-domain test into two cover members. -/
def BoundedMapCompatible
    (f : ∀ i : Fin c.size, BoundedAlgHom K S (c.obj i).algebra) : Prop :=
  ∀ (i j : Fin c.size) (W : Domain K A) (p : W ⟶ c.obj i) (q : W ⟶ c.obj j),
    p.restriction.comp (f i) = q.restriction.comp (f j)

variable (f : ∀ i : Fin c.size, BoundedAlgHom K S (c.obj i).algebra)
  (hf : c.BoundedMapCompatible f)

include hf in
/-- Compatibility of bounded maps supplies the scalar gluing equations on every input. -/
theorem algebraCompatible_mapFamily (s : S) :
    c.AlgebraCompatible (fun i => f i s) := by
  intro i j W p q
  exact congrArg (fun g : BoundedAlgHom K S W.algebra => g s) (hf i j W p q)

/-- The value obtained from actual scalar descent, before bundling its algebra laws. -/
def mapGlueValue (s : S) : U.algebra :=
  c.algebraGlue (fun i => f i s) (c.algebraCompatible_mapFamily f hf s)

@[simp]
theorem restriction_mapGlueValue (i : Fin c.size) (s : S) :
    (c.map i).restriction (c.mapGlueValue f hf s) = f i s :=
  congrFun (c.algebraRestrict_glue _ _) i

/-- The pointwise scalar descents form an actual algebra homomorphism. -/
def glueAlgHom : S →ₐ[K] U.algebra where
  toFun := c.mapGlueValue f hf
  map_zero' := by
    apply c.algebra_ext_of_restrict_eq
    intro i
    simp only [restriction_mapGlueValue, map_zero]
  map_one' := by
    apply c.algebra_ext_of_restrict_eq
    intro i
    simp only [restriction_mapGlueValue, map_one]
  map_add' s t := by
    apply c.algebra_ext_of_restrict_eq
    intro i
    simp only [restriction_mapGlueValue, map_add]
  map_mul' s t := by
    apply c.algebra_ext_of_restrict_eq
    intro i
    simp only [restriction_mapGlueValue, map_mul]
  commutes' z := by
    apply c.algebra_ext_of_restrict_eq
    intro i
    simp only [restriction_mapGlueValue, AlgHom.commutes]

@[simp]
theorem restriction_comp_glueAlgHom (i : Fin c.size) :
    (c.map i).restriction.toAlgHom.comp (c.glueAlgHom f hf) = (f i).toAlgHom := by
  apply AlgHom.ext
  intro s
  exact c.restriction_mapGlueValue f hf i s

/-- Compatible local bounded algebra maps descend to an actual bounded algebra map. -/
def glueBoundedAlgHom : BoundedAlgHom K S U.algebra where
  toAlgHom := c.glueAlgHom f hf
  bounded := c.bounded_of_restrictions (c.glueAlgHom f hf) fun i => by
    rw [c.restriction_comp_glueAlgHom f hf i]
    exact (f i).bounded

@[simp]
theorem restriction_comp_glueBoundedAlgHom (i : Fin c.size) :
    (c.map i).restriction.comp (c.glueBoundedAlgHom f hf) = f i := by
  apply BoundedAlgHom.ext
  intro s
  exact c.restriction_mapGlueValue f hf i s

/-- Descent is unique among actual bounded algebra homomorphisms. -/
theorem glueBoundedAlgHom_unique (g : BoundedAlgHom K S U.algebra)
    (hg : ∀ i, (c.map i).restriction.comp g = f i) :
    g = c.glueBoundedAlgHom f hf := by
  apply BoundedAlgHom.ext
  intro s
  apply c.algebra_ext_of_restrict_eq
  intro i
  exact (congrArg (fun q : BoundedAlgHom K S (c.obj i).algebra => q s) (hg i)).trans
    (c.restriction_mapGlueValue f hf i s).symm

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
