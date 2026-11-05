import Langlands.GroupScheme.FlagCoreTorus
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Cartan.InfiniteFieldStructure
import Langlands.GroupScheme.ReducedSubgroupAction
import Langlands.GroupScheme.KernelCoreQuotientDimension
import Langlands.GroupScheme.Reductive.FiniteCenterOfNoCentralSubgroups

/-! # Faithful unipotent matrix actions and finite normal subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

section MatrixCalculation

variable {A : Type*} [CommRing A] [IsReduced A]
  {n : Type} [Fintype n] [DecidableEq n]

/-- A diagonalizable invertible matrix with nilpotent deviation from identity
is identity over a reduced commutative coefficient ring. -/
theorem eq_one_of_diagonal_conjugate_of_isNilpotent_sub_one
    (M B : GL n A) (d : n → A)
    (hdiag : ((B⁻¹ : GL n A) : Matrix n n A) *
      (M : Matrix n n A) * (B : Matrix n n A) = Matrix.diagonal d)
    (hM : IsNilpotent ((M : Matrix n n A) - 1)) : M = 1 := by
  obtain ⟨l, hl⟩ := hM
  let Z : Matrix n n A := (M : Matrix n n A) - 1
  have hp (i : ℕ) :
      (((B⁻¹ : GL n A) : Matrix n n A) * Z * (B : Matrix n n A)) ^ i =
        ((B⁻¹ : GL n A) : Matrix n n A) * Z ^ i * (B : Matrix n n A) := by
    induction i with
    | zero => simp only [pow_zero, Matrix.mul_one, Units.inv_mul]
    | succ i hi =>
      rw [pow_succ, hi, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (B : Matrix n n A)
        ((B⁻¹ : GL n A) : Matrix n n A), Units.mul_inv, Matrix.one_mul]
  have hz : ((B⁻¹ : GL n A) : Matrix n n A) * Z *
      (B : Matrix n n A) = Matrix.diagonal (fun i => d i - 1) := by
    dsimp only [Z]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hdiag, Units.inv_mul,
      ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have hnil : Matrix.diagonal (fun i => d i - 1) ^ l = 0 := by
    rw [← hz, hp, show Z ^ l = 0 from hl, Matrix.mul_zero, Matrix.zero_mul]
  have hd (i : n) : d i = 1 := by
    have hi := congrArg (fun V : Matrix n n A => V i i) hnil
    rw [Matrix.diagonal_pow] at hi
    simp only [Matrix.diagonal_apply_eq, Pi.pow_apply, Matrix.zero_apply] at hi
    exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨l, hi⟩)
  have hh : ((B⁻¹ * M * B : GL n A) : Matrix n n A) = 1 := by
    rw [Units.val_mul, Units.val_mul, hdiag]
    rw [show d = (fun _ => 1) from funext hd, Matrix.diagonal_one]
  have hu : B⁻¹ * M * B = 1 := Units.ext hh
  have he := congrArg (fun V : GL n A => B * V * B⁻¹) hu
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_one, mul_inv_cancel] using he

end MatrixCalculation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- All relative scheme-test matrices of the representation have nilpotent
deviation from identity. No common exponent is required in this predicate. -/
def HasUnipotentPointMatrices (ρ : MatrixRepresentation G n) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    IsNilpotent ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) - 1)

/-- Restriction of the group preserves unipotent point matrices. -/
theorem HasUnipotentPointMatrices.restrict {ρ : MatrixRepresentation G n}
    (hρ : ρ.HasUnipotentPointMatrices) (i : H ⟶ G) :
    (ρ.restrict i).HasUnipotentPointMatrices := by
  intro T x
  rw [pointMatrix_restrict]
  exact hρ T (x ≫ i.hom.hom)

/-- Nilpotence passes to the actual ground-field rational matrices. -/
theorem HasUnipotentPointMatrices.rationalMatrix {ρ : MatrixRepresentation G n}
    (hρ : ρ.HasUnipotentPointMatrices)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    IsNilpotent ((ρ.rationalMatrix x : Matrix n n k) - 1) := by
  obtain ⟨l, hl⟩ := hρ _ x
  refine ⟨l, ?_⟩
  have h := congrArg (fun V : Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤) =>
    V.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom) hl
  rw [Matrix.map_pow, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)] at h
  exact h

section SplitTorus

variable [IsAlgClosed k]
  {I : Type u} [Fintype I] [DecidableEq I]

/-- A representation of a standard split torus with unipotent point matrices
is trivial. Rational diagonalization and reducedness detect this equality. -/
theorem eq_trivial_of_splitTorus_of_unipotentPointMatrices
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of k)) I) n)
    (hρ : ρ.HasUnipotentPointMatrices) :
    ρ = trivial _ n := by
  classical
  have : Smooth (splitTorus (Spec (CommRingCat.of k)) I).X.hom :=
    (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).smooth
  have : IsReduced (splitTorus (Spec (CommRingCat.of k)) I).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
      (splitTorus (Spec (CommRingCat.of k)) I).X.hom
  obtain ⟨B, w, hw⟩ :=
    GeneralLinear.CocharacterDiagonal.exists_diagonalizingMatrix I ρ
  have hr : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (splitTorus (Spec (CommRingCat.of k)) I).X, ρ.rationalMatrix z = 1 := by
    intro z
    let x := FlagCore.baseAffineTestIso.inv ≫ z
    let t := splitTorus.algebraPointsEquiv I k x
    have hx : FlagCore.baseAffineTestIso.hom ≫ x = z := by simp [x]
    have he : ρ.rationalMatrix z = GeneralLinear.CocharacterDiagonal.matrixAt I ρ t := by
      rw [← hx, FlagCore.rationalMatrix_baseAffineTestIso]
      simp only [GeneralLinear.CocharacterDiagonal.matrixAt, t, MulEquiv.symm_apply_apply]
    apply eq_one_of_diagonal_conjugate_of_isNilpotent_sub_one
      (ρ.rationalMatrix z) (Matrix.GeneralLinearGroup.map (algebraMap k k) B)
      (fun j => (splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)) : k))
    · have h := congrArg Units.val (hw k t)
      rw [← he] at h
      exact h
    · exact hρ.rationalMatrix z
  apply Grp.hom_ext
  apply hom_ext_rationalPoints
  intro z
  apply (GeneralLinear.pointsEquiv n (CommRingCat.of k) _).injective
  change ρ.pointMatrix _ z = (trivial _ n).pointMatrix _ z
  rw [trivial_pointMatrix]
  apply Units.ext
  ext i j
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
  have h := congrArg (fun U : GL n k => U i j) (hr z)
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      ((ρ.pointMatrix _ z : Matrix n n Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) i j) =
    (1 : Matrix n n k) i j at h
  simpa only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply,
    apply_ite, map_one, map_zero] using h

end SplitTorus

section AlgebraicallyClosed

variable [IsAlgClosed k]

/-- Over an algebraically closed field, a torus representation with unipotent
point matrices is trivial. -/
theorem eq_trivial_of_isTorus_of_unipotentPointMatrices
    (hG : IsTorus G) (ρ : MatrixRepresentation G n)
    (hρ : ρ.HasUnipotentPointMatrices) : ρ = trivial G n := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ :=
    hG.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have : Fintype I := Fintype.ofFinite I
  have h := eq_trivial_of_splitTorus_of_unipotentPointMatrices
    (ρ.restrict e.inv) (hρ.restrict e.inv)
  apply (cancel_epi e.inv).mp
  change ρ.restrict e.inv = e.inv ≫ trivial G n
  rw [h]
  change (0 : _ ⟶ _) = e.inv ≫ 0
  rw [comp_zero]

/-- A faithful unipotent matrix action excludes every nontrivial closed torus
in its source, with triviality asserted on all scheme tests. -/
theorem HasUnipotentPointMatrices.hasNoNontrivialClosedTorus
    {ρ : MatrixRepresentation G n} [Mono ρ.hom.hom]
    (hρ : ρ.HasUnipotentPointMatrices) : HasNoNontrivialClosedTorus G := by
  intro T hT i hi
  apply (SubgroupFunctor.range_comp_eq_bot_iff i ρ).mp
  have h := eq_trivial_of_isTorus_of_unipotentPointMatrices hT
    (ρ.restrict i) (hρ.restrict i)
  change SubgroupFunctor.range (ρ.restrict i) = ⊥
  rw [h]
  exact SubgroupFunctor.range_zero

/-- A smooth connected affine group with a faithful unipotent matrix action
is unipotent. The infinite-field no-torus theorem supplies the structural step. -/
theorem HasUnipotentPointMatrices.isUnipotent
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {ρ : MatrixRepresentation G n} [Mono ρ.hom.hom]
    (hρ : ρ.HasUnipotentPointMatrices) : IsUnipotent G :=
  hρ.hasNoNontrivialClosedTorus.isUnipotent_of_infiniteField

end AlgebraicallyClosed

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- In a smooth affine group with trivial unipotent radical, a closed normal
subgroup acting unipotently in a closed faithful representation is finite.
The conclusion retains the full, possibly nonreduced, subgroup scheme. -/
theorem isFinite_of_normal_of_unipotentPointMatrices
    (hG : HasTrivialUnipotentRadical G)
    (ρ : MatrixRepresentation G n) (hc : IsClosedSubgroup ρ)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hU : (ρ.restrict i).HasUnipotentPointMatrices) : IsFinite H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let C := ReducedSubgroup.identityCore H
  let j : C ⟶ G := ReducedSubgroup.identityCoreι H ≫ i
  have hj : IsClosedSubgroup j := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι H).hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have hnormal : (SubgroupFunctor.range j).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp i hi hn
  have : IsClosedImmersion ρ.hom.hom.left := hc
  have : IsClosedImmersion (ρ.restrict j).hom.hom.left := by
    change IsClosedImmersion (j.hom.hom.left ≫ ρ.hom.hom.left)
    have : IsClosedImmersion j.hom.hom.left := hj
    infer_instance
  have : Mono (ρ.restrict j).hom.hom := Over.mono_of_mono_left _
  have hUj : (ρ.restrict j).HasUnipotentPointMatrices := by
    intro T x
    rw [MatrixRepresentation.pointMatrix_restrict]
    have hh := hU T (x ≫ (ReducedSubgroup.identityCoreι H).hom.hom)
    rw [MatrixRepresentation.pointMatrix_restrict] at hh
    simpa only [j, Grp.comp_hom_hom, Category.assoc] using hh
  have hC : IsUnipotent C := hUj.isUnipotent
  have hbot := hG C j hj inferInstance inferInstance hC hnormal
  have hcorebot : SubgroupFunctor.range (ReducedSubgroup.identityCoreι H) = ⊥ :=
    (SubgroupFunctor.range_comp_eq_bot_iff (ReducedSubgroup.identityCoreι H) i).mp hbot
  have hz : ReducedSubgroup.identityCoreι H = 0 :=
    SubgroupFunctor.eq_zero_of_range_eq_bot hcorebot
  have hopen := ReducedSubgroup.isOpen_range_identityCoreι H
  rw [hz, range_zero_hom] at hopen
  exact FiniteCenterOfNoCentralSubgroups.isFinite_of_open_singleton H _ hopen

end Langlands.GroupScheme
