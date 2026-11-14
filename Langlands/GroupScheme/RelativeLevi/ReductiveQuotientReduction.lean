import Langlands.GroupScheme.RelativeLevi.ReductiveQuotientStatement
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Reduction of the relative reductive quotient to existence and annihilation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

variable {S : Scheme.{u}} {P U M H : GroupScheme S}
    {r : U ⟶ P} {q : P ⟶ M}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q)

include hq

/-- A represented quotient kills its specified subgroup as a group-scheme map. -/
theorem subgroup_comp_eq_zero : r ≫ q = 0 := by
  apply Grp.hom_ext
  change r.hom.hom ≫ q.hom.hom = 1
  apply (mem_range_kernelι_iff q _).mp
  rw [hq.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 U.X, Category.id_comp _⟩

/-- Killing the specified subgroup kills the whole scheme-theoretic kernel. -/
theorem kernel_comp_eq_zero (f : P ⟶ H) (hf : r ≫ f = 0) :
    kernelι q ≫ f = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ f.hom.hom = 1
  have hx : (kernelι q).hom.hom ∈ (SubgroupFunctor.range r).carrier (kernel q).X := by
    rw [← hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 (kernel q).X, Category.id_comp _⟩
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hx, Category.assoc, ← Grp.comp_hom_hom, hf]
  change x ≫ (toUnit U.X ≫ η[H.X]) = toUnit (kernel q).X ≫ η[H.X]
  rw [← Category.assoc, comp_toUnit]

/-- An actual fpqc quotient has the expected unique factorization property for every
homomorphism killing its specified subgroup. -/
theorem existsUnique_factor [QuasiCompact q.hom.hom.left]
    (f : P ⟶ H) (hf : r ≫ f = 0) :
    ∃! g : M ⟶ H, q ≫ g = f := by
  have := hq.1
  have := hq.2.1
  exact ⟨FpqcHomDescent.hom q f (hq.kernel_comp_eq_zero f hf),
    FpqcHomDescent.fac q f (hq.kernel_comp_eq_zero f hf),
    fun g hg => FpqcHomDescent.unique q f (hq.kernel_comp_eq_zero f hf) g hg⟩

/-- For an actual fpqc quotient, factorization is equivalent to annihilating the subgroup. -/
theorem existsUnique_factor_iff [QuasiCompact q.hom.hom.left] (f : P ⟶ H) :
    (∃! g : M ⟶ H, q ≫ g = f) ↔ r ≫ f = 0 := by
  constructor
  · rintro ⟨g, hg, -⟩
    rw [← hg, ← Category.assoc, hq.subgroup_comp_eq_zero, Limits.zero_comp]
  · exact hq.existsUnique_factor f

end RelativeRoot.IsFppfQuotient

/-- The existence part of the relative reductive quotient, without its universal property. -/
def RelativeParabolicReductiveQuotientExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
      ∃ (M : GroupScheme S) (q : P ⟶ M),
        IsReductive M ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q

/-- Every surjection from a relative parabolic onto a reductive group kills its radical.
The conclusion is an equality of maps over the whole base. -/
def RelativeParabolicRadicalAnnihilationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
      ∀ (H : GroupScheme S) (f : P ⟶ H),
        IsReductive H → Surjective f.hom.hom.left → r ≫ f = 0

/-- The two geometric inputs in the relative reductive-quotient proof. -/
def RelativeParabolicReductiveQuotientInputsStatement : Prop :=
  RelativeParabolicReductiveQuotientExistenceStatement.{u} ∧
    RelativeParabolicRadicalAnnihilationStatement.{u}

/-- Existence and annihilation suffice: affineness makes the quotient quasi-compact,
and fpqc homomorphism descent supplies existence and uniqueness of the factorization. -/
theorem relativeParabolicReductiveQuotientReduction
    (hex : RelativeParabolicReductiveQuotientExistenceStatement.{u})
    (hkill : RelativeParabolicRadicalAnnihilationStatement.{u}) :
    RelativeParabolicReductiveQuotientStatement.{u} := by
  intro S G P U i r hG hP hU
  obtain ⟨M, q, hM, hq⟩ := hex S G P U i r hG hP hU
  have := hP.isAffineHom
  have := hM.isAffineHom
  have : QuasiCompact (q.hom.hom.left ≫ M.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ M.X.hom
  exact ⟨M, q, hM, hq,
    fun H f hH hf => hq.existsUnique_factor f (hkill S G P U i r hG hP hU H f hH hf)⟩

/-- The reduction loses no information: the full target implies both geometric inputs. -/
theorem relativeParabolicReductiveQuotient_iff_inputs :
    RelativeParabolicReductiveQuotientStatement.{u} ↔
      RelativeParabolicReductiveQuotientInputsStatement.{u} := by
  constructor
  · intro h
    constructor
    · intro S G P U i r hG hP hU
      obtain ⟨M, q, hM, hq, -⟩ := h S G P U i r hG hP hU
      exact ⟨M, q, hM, hq⟩
    · intro S G P U i r hG hP hU H f hH hf
      obtain ⟨M, q, hM, hq, hfac⟩ := h S G P U i r hG hP hU
      obtain ⟨g, hg, -⟩ := hfac H f hH hf
      rw [← hg, ← Category.assoc, hq.subgroup_comp_eq_zero, Limits.zero_comp]
  · rintro ⟨hex, hkill⟩
    exact relativeParabolicReductiveQuotientReduction hex hkill

end Langlands.GroupScheme
