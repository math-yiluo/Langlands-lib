import Langlands.GroupScheme.Rational.AffineVectorExtension
import Langlands.GroupScheme.Rational.TorusVectorLinearizationStatement

/-! # Quotient-torus conjugation on a vector kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorExtensionDescent

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {E V H : GroupScheme (Spec (CommRingCat.of k))}
    (n : V ⟶ E) [Mono n.hom.hom] (q : E ⟶ H)
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {d : ℕ} (hV : RelativeRoot.IsVectorGroupOfDimension V d)

include hV in
/-- Conjugation on a commutative vector kernel depends only on the quotient
point, on every scheme test. -/
theorem action_eq_of_comp_eq {T : Over (Spec (CommRingCat.of k))}
    (g g' : T ⟶ E.X) (hg : g ≫ q.hom.hom = g' ≫ q.hom.hom) (v : T ⟶ V.X) :
    (action n q hn).act g v = (action n q hn).act g' v := by
  have hk : g⁻¹ * g' ∈ (SubgroupFunctor.range n).carrier T := by
    rw [hn, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, hg,
      inv_mul_cancel]
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.1 hk
  have hg' : g' = g * (w ≫ n.hom.hom) := by
    rw [hw]
    group
  have hc : (w ≫ n.hom.hom) * (v ≫ n.hom.hom) =
      (v ≫ n.hom.hom) * (w ≫ n.hom.hom) := by
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, (hV.points_commute w v).eq]
  apply (cancel_mono n.hom.hom).1
  rw [action_act_comp, action_act_comp, hg']
  symm
  calc
    (g * (w ≫ n.hom.hom)) * (v ≫ n.hom.hom) * (g * (w ≫ n.hom.hom))⁻¹ =
        g * ((w ≫ n.hom.hom) * (v ≫ n.hom.hom)) * (w ≫ n.hom.hom)⁻¹ * g⁻¹ := by group
    _ = g * ((v ≫ n.hom.hom) * (w ≫ n.hom.hom)) * (w ≫ n.hom.hom)⁻¹ * g⁻¹ := by rw [hc]
    _ = g * (v ≫ n.hom.hom) * g⁻¹ := by group

variable (s : H.X ⟶ E.X) (hs : s ≫ q.hom.hom = 𝟙 H.X)

/-- Conjugation by a scheme section, before proving its action laws. -/
def quotientAct (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ H.X) (v : T ⟶ V.X) :
    T ⟶ V.X :=
  (action n q hn).act (t ≫ s) v

/-- Conjugation through the section is natural on all scheme tests. -/
theorem quotientAct_naturality {T W : Over (Spec (CommRingCat.of k))}
    (f : W ⟶ T) (t : T ⟶ H.X) (v : T ⟶ V.X) :
    f ≫ quotientAct n q hn s T t v = quotientAct n q hn s W (f ≫ t) (f ≫ v) := by
  simp only [quotientAct, (action n q hn).naturality, Category.assoc]

include hs hV in
/-- The quotient identity acts trivially even when the scheme section is not
normalized at the identity. -/
theorem quotientAct_one (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) :
    quotientAct n q hn s T 1 v = v := by
  rw [quotientAct, action_eq_of_comp_eq n q hn hV (1 ≫ s) 1 (by
    rw [Category.assoc, hs, Category.comp_id, MonObj.one_comp]),
    AutomorphicAction.act_one_left]

include hs hV in
/-- Section defects lie in the commutative kernel, so conjugation through the
section satisfies the quotient multiplication law. -/
theorem quotientAct_mul (T : Over (Spec (CommRingCat.of k)))
    (t r : T ⟶ H.X) (v : T ⟶ V.X) :
    quotientAct n q hn s T (t * r) v =
      quotientAct n q hn s T t (quotientAct n q hn s T r v) := by
  simp only [quotientAct]
  rw [← AutomorphicAction.act_mul_left]
  apply action_eq_of_comp_eq n q hn hV
  rw [Category.assoc, hs, Category.comp_id]
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, hs,
    Category.comp_id, Category.comp_id]

/-- Conjugation through the section preserves multiplication in the kernel. -/
theorem quotientAct_mul_right (T : Over (Spec (CommRingCat.of k)))
    (t : T ⟶ H.X) (v w : T ⟶ V.X) :
    quotientAct n q hn s T t (v * w) =
      quotientAct n q hn s T t v * quotientAct n q hn s T t w :=
  (action n q hn).act_mul_right (t ≫ s) v w

/-- The actual quotient action on a full vector kernel, constructed from a
scheme section; multiplicativity of the section is not assumed. -/
def quotientAction : AutomorphicAction H V :=
  AutomorphicAction.ofPoints (quotientAct n q hn s) (quotientAct_naturality n q hn s)
    (quotientAct_one n q hn hV s hs) (quotientAct_mul n q hn hV s hs)
    (quotientAct_mul_right n q hn s)

@[simp]
theorem quotientAction_act {T : Over (Spec (CommRingCat.of k))}
    (t : T ⟶ H.X) (v : T ⟶ V.X) :
    (quotientAction n q hn hV s hs).act t v = (action n q hn).act (t ≫ s) v :=
  AutomorphicAction.ofPoints_act _ _ _ _ _ t v

/-- Restricting the quotient action along the original quotient recovers the
actual ambient conjugation action. -/
theorem quotientAction_restrict :
    (quotientAction n q hn hV s hs).restrict q = action n q hn := by
  apply AutomorphicAction.ext_act
  intro T g v
  rw [AutomorphicAction.restrict_act, quotientAction_act]
  apply action_eq_of_comp_eq n q hn hV
  rw [Category.assoc, Category.assoc, hs, Category.comp_id]

end Langlands.GroupScheme.VectorExtensionDescent

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {E V H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsAffineHom H.X.hom]
    (n : V ⟶ E) [Mono n.hom.hom] (q : E ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {d : ℕ} (hV : RelativeRoot.IsVectorGroupOfDimension V d)

include hV hn in
/-- Torus linearization and affine torsor triviality split every affine
faithfully flat extension of a torus by a full vector kernel. -/
theorem IsTorus.exists_vectorExtensionSection
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u}) (hH : IsTorus H) :
    ∃ σ : H ⟶ E, σ ≫ q = 𝟙 H := by
  let : IsAffineHom V.X.hom := hV.isAffineHom
  obtain ⟨s, hs⟩ := hV.exists_quotientSection n q hn
  obtain ⟨e, he⟩ := hlinear k H V d hH hV
    (VectorExtensionDescent.quotientAction n q hn hV s hs)
  have he' := he.restrict q
  rw [VectorExtensionDescent.quotientAction_restrict] at he'
  exact hH.exists_extensionSection n q hn s hs e he'

/-- A chosen homomorphic section of a vector extension of a torus, using the
exact torus-action linearization statement. -/
def IsTorus.vectorExtensionSection
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u}) (hH : IsTorus H) :
    H ⟶ E :=
  Classical.choose (hH.exists_vectorExtensionSection n q hn hV hlinear)

/-- The chosen homomorphism splits the original quotient. -/
theorem IsTorus.vectorExtensionSection_comp
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u}) (hH : IsTorus H) :
    hH.vectorExtensionSection n q hn hV hlinear ≫ q = 𝟙 H :=
  Classical.choose_spec (hH.exists_vectorExtensionSection n q hn hV hlinear)

end Langlands.GroupScheme
