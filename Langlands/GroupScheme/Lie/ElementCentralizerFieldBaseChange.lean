import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCConjugator
import Langlands.GroupScheme.Dynamic.AffineInclusionCriterion
import Langlands.GroupScheme.Lie.FieldExtension

/-! # Field base change of an actual Lie-element centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "G_E" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k E)) G

local instance elementCentralizerFieldBaseChangeAffine : IsAffineHom (G_E).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k E)))

local instance elementCentralizerFieldBaseChangeFiniteType : LocallyOfFiniteType (G_E).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap k E)))

/-- The centralizer of the extended Lie element is the base change of the
original all-test centralizer functor. -/
theorem elementCentralizer_fieldBaseChange (X : lieKernel G k) :
    elementCentralizer (G_E) (kernelFieldExtension (K := E) G X) =
      (elementCentralizer G X).baseChange (algebraBaseMap k E) := by
  let H := (G_E)
  let Y := kernelFieldExtension (K := E) G X
  let P := elementCentralizer H Y
  let Q := (elementCentralizer G X).baseChange (algebraBaseMap k E)
  have ha (A : Type u) [CommRing A] [Algebra k A] [Algebra E A] [IsScalarTower k E A]
      (g : AffinePoints H A) :
      g ∈ P.carrier ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E A))) ↔
        g ∈ Q.carrier ((algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E A))) := by
    change g ∈ (elementCentralizer H Y).carrier _ ↔
      g ∈ ((elementCentralizer G X).baseChange (algebraBaseMap k E)).carrier _
    rw [mem_elementCentralizer_baseChange_affine_iff, SubgroupFunctor.mem_baseChange_affine_iff,
      mem_elementCentralizer_adjoint_iff]
    have hY : kernelBaseChangeEquiv k E G E Y = lieKernelMap G (Algebra.ofId k E) X :=
      MulEquiv.apply_symm_apply _ _
    rw [hY]
    change adjoint G A (affineBaseChangeEquiv k E G A g)
        (lieKernelMapLinear G (IsScalarTower.toAlgHom k E A)
          (lieKernelMapLinear G (Algebra.ofId k E) (Additive.ofMul X))) =
      lieKernelMapLinear G (IsScalarTower.toAlgHom k E A)
        (lieKernelMapLinear G (Algebra.ofId k E) (Additive.ofMul X)) ↔ _
    rw [lieKernelMapLinear_base]
  have htest (A : CommRingCat.{u}) (f : Spec A ⟶ Spec (CommRingCat.of E))
      (g : Over.mk f ⟶ H.X) :
      g ∈ P.carrier (Over.mk f) ↔ g ∈ Q.carrier (Over.mk f) := by
    let : Algebra E A := (Spec.preimage f).hom.toAlgebra
    let : Algebra k A := Algebra.compHom A (algebraMap k E)
    let : IsScalarTower k E A := IsScalarTower.of_algebraMap_eq' rfl
    let U := (algSpec (CommRingCat.of E)).obj (op (CommAlgCat.of E A))
    have hU : U.hom = f := Spec.map_preimage f
    let e : U ≅ Over.mk f := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ f = U.hom
      simpa only [Category.id_comp] using hU.symm)
    have h : e.hom ≫ g ∈ P.carrier U ↔ e.hom ≫ g ∈ Q.carrier U := ha A (e.hom ≫ g)
    constructor
    · intro hg
      have hq := Q.comp_mem e.inv (h.mp (P.comp_mem e.hom hg))
      simpa only [Iso.inv_hom_id_assoc] using hq
    · intro hg
      have hp := P.comp_mem e.inv (h.mpr (Q.comp_mem e.hom hg))
      simpa only [Iso.inv_hom_id_assoc] using hp
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨C, i, hrep, hi⟩ := elementCentralizer_isClosedRepresentable G X
  obtain ⟨C', i', hrep', hi'⟩ := elementCentralizer_isClosedRepresentable H Y
  apply le_antisymm
  · exact SubgroupFunctor.le_of_closed_isRepresentedBy_of_affine_tests i' hrep' hi'
      fun A f g => (htest A f g).mp
  · exact SubgroupFunctor.le_of_closed_isRepresentedBy_of_affine_tests
      _ (hrep.baseChange _) (hi.baseChange _) fun A f g => (htest A f g).mpr

/-- The all-test centralizer of a tangent vector commutes with a field extension. -/
def ElementCentralizerFieldBaseChangeStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (X : lieKernel G k),
    elementCentralizer ((baseChange (algebraBaseMap k E)).obj G)
        (kernelFieldExtension (K := E) G X) =
      (elementCentralizer G X).baseChange (algebraBaseMap k E)

theorem elementCentralizerFieldBaseChange : ElementCentralizerFieldBaseChangeStatement.{u} :=
  fun _ _ _ _ _ _ _ _ X => elementCentralizer_fieldBaseChange X

end Langlands.GroupScheme.Lie
