import Langlands.AbelianScheme.ConnectedGeometricPointHomFaithfulnessStatement
import Langlands.AbelianScheme.Tate.ConnectedTorsionDetection
import Langlands.AbelianScheme.Tate.IntegralBaseChange
import Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityProof
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Homomorphisms of abelian schemes over a connected base are detected at one geometric point -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

universe u

namespace Langlands.AbelianScheme

open GroupScheme

variable {S : Scheme.{u}}

/-- The zero homomorphism acts trivially on every torsion level. -/
theorem levelMap_groupHom_zero {A B : AbelianScheme S} (T : Over S) (n : ℕ)
    (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (groupHom (0 : A ⟶ B)) n x = 0 := by
  apply GroupScheme.Tate.toSection_injective B.toGrp T n
  change (Additive.toMul x).val ≫ (1 : A.toGrp ⟶ B.toGrp).hom.hom = 1
  exact MonObj.comp_one _

/-- A homomorphism whose base change vanishes kills the torsion points of the
original abelian schemes at the pushed-forward test scheme. -/
theorem levelMap_eq_zero_of_baseChange_eq_zero {S' : Scheme.{u}} (b : S' ⟶ S)
    {A B : AbelianScheme S} (f : A ⟶ B) (hf : (baseChange b).map f = 0)
    (T : Over S') (n : ℕ)
    (x : GroupScheme.Tate.Level A.toGrp ((Over.map b).obj T) n) :
    GroupScheme.Tate.levelMap ((Over.map b).obj T) (groupHom f) n x = 0 := by
  obtain ⟨y, rfl⟩ := (GroupScheme.Tate.levelBaseChange b A.toGrp T n).surjective x
  rw [← GroupScheme.Tate.levelBaseChange_map]
  have hmap : (Over.pullback b).mapGrp.map (groupHom f) =
      groupHom ((baseChange b).map f) := rfl
  have hy : GroupScheme.Tate.levelMap T ((Over.pullback b).mapGrp.map (groupHom f)) n y = 0 := by
    rw [hmap, hf]
    exact levelMap_groupHom_zero (A := (baseChange b).obj A) (B := (baseChange b).obj B) T n y
  rw [hy, map_zero]

/-- A homomorphism killing the scheme kernel of multiplication by `n` kills all
level-`n` points over every test scheme. -/
theorem levelMap_eq_zero_of_kernel_comp_eq_one {A B : AbelianScheme S} (f : A ⟶ B)
    (T : Over S) (n : ℕ)
    (hker : kernelι (multiplication A.toGrp (n : ℤ)) ≫ groupHom f = 1)
    (x : GroupScheme.Tate.Level A.toGrp T n) :
    GroupScheme.Tate.levelMap T (groupHom f) n x = 0 := by
  obtain ⟨z, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).surjective x
  apply GroupScheme.Tate.toSection_injective B.toGrp T n
  have h : (kernelι (multiplication A.toGrp (n : ℤ))).hom.hom ≫ (groupHom f).hom.hom =
      (1 : (kernel (multiplication A.toGrp (n : ℤ))).X ⟶ B.X) :=
    congrArg (fun g => g.hom.hom) hker
  change (Additive.toMul z ≫ (kernelι (multiplication A.toGrp (n : ℤ))).hom.hom) ≫
      (groupHom f).hom.hom = 1
  rw [Category.assoc, h]
  exact MonObj.comp_one _

/-- Every field-valued point of a base on which all positive integers are units
has characteristic zero. -/
theorem charZero_of_isUnit_natCast
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) : CharZero K := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  let φ : Γ(S, ⊤) →+* K := (t.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
  have h := (hu ⟨n, Nat.pos_of_ne_zero h0, trivial⟩).map φ
  rw [map_natCast] at h
  rw [hn] at h
  exact not_isUnit_zero h

/-- Over an algebraically closed field of characteristic zero, a homomorphism
killing every torsion kernel on the original base has zero base change. -/
theorem baseChange_eq_zero_of_kernel_comp_eq_one {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] (t : Spec (.of K) ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B)
    (hker : ∀ n : ℕ, 0 < n → kernelι (multiplication A.toGrp (n : ℤ)) ≫ groupHom f = 1) :
    (baseChange t).map f = 0 := by
  apply Tate.hom_eq_zero_of_dense_twoPowerTorsion
    (Tate.fieldTwoPowerTorsionDensity K ((baseChange t).obj A))
  intro m
  refine AddMonoidHom.ext fun x => ?_
  rw [AddMonoidHom.zero_apply]
  apply (GroupScheme.Tate.levelBaseChange t B.toGrp
    (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (2 ^ m)).injective
  exact (GroupScheme.Tate.levelBaseChange_map t (Over.mk (𝟙 (Spec (CommRingCat.of K))))
    (groupHom f) (2 ^ m) x).trans
    ((levelMap_eq_zero_of_kernel_comp_eq_one f _ (2 ^ m)
      (hker (2 ^ m) (Nat.pos_of_ne_zero (pow_ne_zero m two_ne_zero))) _).trans
      (map_zero _).symm)

/-- If the base change of a homomorphism to a field-valued point vanishes, the
homomorphism sends every point of the fibre over that point to the unit. -/
theorem hom_apply_eq_of_baseChange_eq_zero {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ S) {A B : AbelianScheme S} (f : A ⟶ B)
    (hf : (baseChange t).map f = 0) (x : A.X.left) (y : Spec (.of K))
    (hxy : A.X.hom x = t y) :
    hom f x = η[B.X].left (A.X.hom x) := by
  let T : Over (Spec (.of K)) := Over.mk (Limits.pullback.snd A.X.hom t)
  let p : T ⟶ ((Over.pullback t).mapGrp.obj A.toGrp).X := 𝟙 T
  have h1 : p ≫ ((Over.pullback t).mapGrp.map (groupHom f)).hom.hom = 1 := by
    change p ≫ (groupHom ((baseChange t).map f)).hom.hom = 1
    rw [hf]
    exact MonObj.comp_one _
  have h2 := congrArg (GroupScheme.baseChangePointsEquiv t B.toGrp T) h1
  rw [GroupScheme.baseChangePointsEquiv_comp t (groupHom f) T p, map_one] at h2
  have h3 : Limits.pullback.fst A.X.hom t ≫ hom f =
      Limits.pullback.snd A.X.hom t ≫ t ≫ η[B.X].left := by
    have h := congrArg (fun g => g.left) h2
    simp at h
    change (𝟙 _ ≫ Limits.pullback.fst A.X.hom t) ≫ hom f =
      (Limits.pullback.snd A.X.hom t ≫ t) ≫ η[B.X].left at h
    simpa using h
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have h4 := congrArg (fun g : Limits.pullback A.X.hom t ⟶ B.X.left => g z) h3
  simp only [Scheme.Hom.comp_apply, hz1, hz2] at h4
  rw [h4, hxy]

/-- The unit section is sent to the unit section by every homomorphism. -/
theorem unit_comp_hom {A B : AbelianScheme S} (g : A ⟶ B) :
    η[A.X].left ≫ hom g = η[B.X].left :=
  congrArg (fun k => k.left) (IsMonHom.one_hom (f := (groupHom g).hom.hom))

/-- Over a connected locally noetherian base on which every positive integer is
a unit, a homomorphism of abelian schemes whose pullback to one algebraically
closed geometric point is zero is zero. -/
theorem connectedGeometricPointHomFaithfulness :
    ConnectedGeometricPointHomFaithfulnessStatement.{u} := by
  intro S _ _ hu Ω _ _ s A B f hf
  have hker : ∀ n : ℕ, 0 < n →
      kernelι (multiplication A.toGrp (n : ℤ)) ≫ groupHom f = 1 := fun n hn =>
    Tate.kernel_comp_eq_one_of_levelMap_eq_zero torsionFiniteEtale (𝟙 _ ≫ s) f n hn
      (hu ⟨n, hn, trivial⟩)
      (fun x => levelMap_eq_zero_of_baseChange_eq_zero s f hf (Over.mk (𝟙 _)) n x)
  have hpt : ∀ x : A.X.left, hom f x = η[B.X].left (A.X.hom x) := by
    intro x
    let κ := S.residueField (A.X.hom x)
    let K := AlgebraicClosure κ
    let t : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ S.fromSpecResidueField (A.X.hom x)
    have : CharZero K := charZero_of_isUnit_natCast hu t
    exact hom_apply_eq_of_baseChange_eq_zero t f
      (baseChange_eq_zero_of_kernel_comp_eq_one t f hker) x default
      (by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply])
  have hsec : η[A.X].left ≫ A.X.hom = 𝟙 S := Over.w η[A.X]
  have hfac := Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions
    A.X.left S B.X.left A.X.hom η[A.X].left (hom f) hsec
    (Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
      A.X.left S A.X.hom inferInstance inferInstance inferInstance)
    (fun x => by rw [unit_comp_hom f]; exact hpt x)
  rw [unit_comp_hom f] at hfac
  have h0 : hom (0 : A ⟶ B) = A.X.hom ≫ η[B.X].left := rfl
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact Over.OverMorphism.ext (hfac.trans h0.symm)

end Langlands.AbelianScheme
