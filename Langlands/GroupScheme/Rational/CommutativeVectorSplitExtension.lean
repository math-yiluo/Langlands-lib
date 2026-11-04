import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.AbelianScheme.Kernel

/-! # Vector coordinates for split commutative extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace CommutativeVectorSplitExtension

section Split

variable {B : Scheme.{u}} {E K V : GroupScheme B} [IsCommMonObj E.X]
    (j : K ⟶ E) [Mono j.hom.hom] (q : E ⟶ V)
    (hn : SubgroupFunctor.range j = SubgroupFunctor.range (kernelι q))
    (s : V ⟶ E) (hs : s ≫ q = 𝟙 V)

omit [IsCommMonObj E.X] [Mono j.hom.hom] in
include hn in
/-- Every point of the specified full kernel is killed by the quotient. -/
theorem kernel_comp {T : Over B} (x : T ⟶ K.X) :
    (x ≫ j.hom.hom) ≫ q.hom.hom = 1 := by
  rw [← mem_range_kernelι_iff, ← hn]
  exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩

omit [IsCommMonObj E.X] in
include hs in
/-- The group section splits the quotient on every test. -/
theorem section_comp {T : Over B} (x : T ⟶ V.X) :
    (x ≫ s.hom.hom) ≫ q.hom.hom = x := by
  rw [Category.assoc, ← Grp.comp_hom_hom, hs, Grp.id_hom_hom, Category.comp_id]

/-- Multiplying a kernel point and a section point is a homomorphism. -/
def splitPointHom (T : Over B) :
    ((T ⟶ K.X) × (T ⟶ V.X)) →* (T ⟶ E.X) where
  toFun x := (x.1 ≫ j.hom.hom) * (x.2 ≫ s.hom.hom)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, MonObj.one_comp, one_mul]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

include hn hs in
/-- A group section and the full kernel give a product decomposition on every test. -/
theorem splitPointHom_bijective (T : Over B) :
    Function.Bijective (splitPointHom j s T) := by
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have hy : y = y' := by
      have hh := congrArg (fun z : T ⟶ E.X => z ≫ q.hom.hom) h
      simpa only [splitPointHom, MonoidHom.coe_mk, OneHom.coe_mk,
        MonObj.mul_comp, kernel_comp j q hn, section_comp q s hs, one_mul] using hh
    subst y'
    refine Prod.ext ?_ rfl
    apply (cancel_mono j.hom.hom).mp
    exact mul_right_cancel h
  · intro x
    have hx : x * ((x ≫ q.hom.hom) ≫ s.hom.hom)⁻¹ ∈
        (SubgroupFunctor.range j).carrier T := by
      rw [hn, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp,
        section_comp q s hs, mul_inv_cancel]
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
    refine ⟨(y, x ≫ q.hom.hom), ?_⟩
    change (y ≫ j.hom.hom) * _ = x
    rw [hy, inv_mul_cancel_right]

/-- The canonical split-product equivalence, oriented toward the ambient group. -/
def splitPointEquiv (T : Over B) :
    ((T ⟶ K.X) × (T ⟶ V.X)) ≃* (T ⟶ E.X) :=
  MulEquiv.ofBijective (splitPointHom j s T) (splitPointHom_bijective j q hn s hs T)

@[simp]
theorem splitPointEquiv_apply (T : Over B) (x : (T ⟶ K.X) × (T ⟶ V.X)) :
    splitPointEquiv j q hn s hs T x =
      (x.1 ≫ j.hom.hom) * (x.2 ≫ s.hom.hom) := rfl

/-- The split-product equivalence commutes with every test morphism. -/
theorem splitPointEquiv_natural {T W : Over B} (f : W ⟶ T)
    (x : (T ⟶ K.X) × (T ⟶ V.X)) :
    splitPointEquiv j q hn s hs W (f ≫ x.1, f ≫ x.2) =
      f ≫ splitPointEquiv j q hn s hs T x := by
  simp only [splitPointEquiv_apply, MonObj.comp_mul, Category.assoc]

/-- The inverse split-product equivalence is natural on every test. -/
theorem splitPointEquiv_symm_natural {T W : Over B} (f : W ⟶ T)
    (x : T ⟶ E.X) :
    (splitPointEquiv j q hn s hs W).symm (f ≫ x) =
      (f ≫ ((splitPointEquiv j q hn s hs T).symm x).1,
        f ≫ ((splitPointEquiv j q hn s hs T).symm x).2) := by
  apply (splitPointEquiv j q hn s hs W).injective
  rw [MulEquiv.apply_symm_apply, splitPointEquiv_natural,
    MulEquiv.apply_symm_apply]

end Split

section Coordinates

variable {A : Type*} [AddCommGroup A] (n : ℕ)

/-- Join one additive coordinate and `n` further coordinates. -/
def consCoordinateEquiv :
    Multiplicative (Fin n → A) × Multiplicative (Fin 1 → A) ≃*
      Multiplicative (Fin (n + 1) → A) where
  toFun x := Multiplicative.ofAdd (Fin.cons (x.2.toAdd 0) x.1.toAdd)
  invFun x := (Multiplicative.ofAdd (Fin.tail x.toAdd),
    Multiplicative.ofAdd (fun _ => x.toAdd 0))
  left_inv x := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext i
      rfl
    · apply Multiplicative.toAdd.injective
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    exact congrFun (Fin.cons_self_tail x.toAdd) i
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end Coordinates

section Vector

variable {B : Scheme.{u}} {E K V : GroupScheme B} [IsCommMonObj E.X]
    (j : K ⟶ E) [Mono j.hom.hom] (q : E ⟶ V)
    (hn : SubgroupFunctor.range j = SubgroupFunctor.range (kernelι q))
    (s : V ⟶ E) (hs : s ≫ q = 𝟙 V) {n : ℕ}
    (eK : ∀ T : Over B, (T ⟶ K.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (eV : ∀ T : Over B, (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))

/-- Coordinates of a split extension, with the quotient coordinate first. -/
def splitVectorCoordinates (T : Over B) :
    (T ⟶ E.X) ≃* Multiplicative (Fin (n + 1) → Γ(T.left, ⊤)) :=
  ((splitPointEquiv j q hn s hs T).symm.trans
    (MulEquiv.prodCongr (eK T) (eV T))).trans (consCoordinateEquiv n)

include j q hn s hs in
/-- Natural coordinates on the kernel and the quotient induce natural coordinates
on the split commutative extension, including zero-dimensional kernels. -/
theorem isVectorGroupOfDimension_of_section
    (hK : IsVectorGroupOfDimension K n) (hV : IsVectorGroupOfDimension V 1) :
    IsVectorGroupOfDimension E (n + 1) := by
  obtain ⟨eK, heK⟩ := hK
  obtain ⟨eV, heV⟩ := hV
  refine ⟨splitVectorCoordinates j q hn s hs eK eV, ?_⟩
  intro T W f x
  change Fin.cons (α := fun _ : Fin (n + 1) => Γ(W.left, ⊤))
    ((eV W ((splitPointEquiv j q hn s hs W).symm (f ≫ x)).2).toAdd 0)
    ((eK W ((splitPointEquiv j q hn s hs W).symm (f ≫ x)).1).toAdd) = _
  rw [splitPointEquiv_symm_natural, heK T W f, heV T W f]
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end Vector

end CommutativeVectorSplitExtension
end Langlands.GroupScheme.RelativeRoot
