import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoublingDivisionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocus.FiniteFlatAgreement
import Langlands.AbelianScheme.IsogenyFactorization
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AbelianScheme.MultiplicationSpecialization

/-! # The divisibility locus of an abelian-scheme homomorphism -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {S T : Scheme.{u}} {A B : AbelianScheme S}

private lemma multiplication_comp_nat (k : ℕ) (f : A ⟶ B) :
    multiplication A (k : ℤ) ≫ f = k • f := by
  rw [multiplication, Preadditive.zsmul_comp, Category.id_comp, natCast_zsmul]

private lemma multiplication_isogeny_nat (A : AbelianScheme S) {k : ℕ} (hk : 0 < k) :
    IsIsogeny (multiplication A (k : ℤ)) :=
  isIsogeny_multiplication_of_statement GroupScheme.multiplicationIsogeny A k (by exact_mod_cast hk.ne')

open GroupScheme in
private lemma kernel_eq_one_iff (g : A ⟶ B) {k : ℕ} (hk : 0 < k) :
    kernelι (groupHom (AbelianScheme.multiplication A (k : ℤ))) ≫ groupHom g = 1 ↔
      ∃ divisor : A ⟶ B, k • divisor = g := by
  let f := groupHom (AbelianScheme.multiplication A (k : ℤ))
  constructor
  · intro h
    let divisor : A ⟶ B := Additive.ofMul (IsogenyFactorization.lift (multiplication_isogeny_nat A hk)
      (groupHom g) h)
    refine ⟨divisor, ?_⟩
    rw [← multiplication_comp_nat]
    exact congrArg Additive.ofMul (IsogenyFactorization.fac (multiplication_isogeny_nat A hk)
      (groupHom g) h)
  · rintro ⟨divisor, rfl⟩
    rw [← multiplication_comp_nat]
    apply Grp.hom_ext
    change ((kernelι f).hom.hom ≫ f.hom.hom) ≫ (groupHom divisor).hom.hom = 1
    rw [(kernel_isPullback f).w]
    exact MonObj.one_comp _

private lemma over_pullback_map_eq_iff {X Y : Over S} (f g : X ⟶ Y) (t : T ⟶ S) :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      pullback.fst X.hom t ≫ f.left = pullback.fst X.hom t ≫ g.left := by
  constructor
  · intro h
    simpa only [Over.pullback_map_left, pullback.lift_fst] using
      congrArg (fun a ↦ a.left ≫ pullback.fst Y.hom t) h
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.pullback_map_left, pullback.lift_fst] using h
    · simp only [Over.pullback_map_left, pullback.lift_snd]

open GroupScheme in
private lemma baseChange_kernel_eq_one_iff (t : T ⟶ S) (g : A ⟶ B) (k : ℕ) :
    let f := groupHom (AbelianScheme.multiplication A (k : ℤ))
    let a := (kernelι f ≫ groupHom g).hom.hom
    pullback.fst (GroupScheme.kernel f).X.hom t ≫ a.left =
        pullback.fst (GroupScheme.kernel f).X.hom t ≫ (1 : (GroupScheme.kernel f).X ⟶ B.X).left ↔
      kernelι (groupHom (AbelianScheme.multiplication ((baseChange t).obj A) (k : ℤ))) ≫
        groupHom ((baseChange t).map g) = 1 := by
  dsimp only
  let f := groupHom (AbelianScheme.multiplication A (k : ℤ))
  rw [← over_pullback_map_eq_iff _ _ t, ← multiplication_baseChange]
  change (Over.pullback t).map (kernelι f ≫ groupHom g).hom.hom =
      (Over.pullback t).map (1 : (GroupScheme.kernel f).X ⟶ B.X) ↔
    kernelι ((Over.pullback t).mapGrp.map f) ≫ (Over.pullback t).mapGrp.map (groupHom g) = 1
  rw [Functor.map_one]
  let e := kernelBaseChangeIso t f
  rw [← cancel_epi e.hom]
  change _ ↔ e.hom ≫ kernelι ((Over.pullback t).mapGrp.map f) ≫
    (Over.pullback t).mapGrp.map (groupHom g) = e.hom ≫ 1
  rw [← Category.assoc e.hom, show e.hom ≫ kernelι ((Over.pullback t).mapGrp.map f) = _
    from kernelBaseChangeIso_hom_ι t f, ← Functor.map_comp]
  rw [MonObj.comp_one]
  change _ ↔ (Over.pullback t).mapGrp.map (kernelι f ≫ groupHom g) = 1
  constructor
  · intro h
    apply Grp.hom_ext
    exact h
  · intro h
    exact congrArg (fun a ↦ a.hom.hom) h

/-- Divisibility by a positive integer is represented by a closed subscheme of the base. -/
theorem exists_homMultiple_locus [IsLocallyNoetherian S] (g : A ⟶ B) (k : ℕ) (hk : 0 < k) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S), IsClosedImmersion j ∧
      ∀ (T : Scheme.{u}) (t : T ⟶ S),
        (∃ t' : T ⟶ Z, t' ≫ j = t) ↔
          ∃ divisor : (baseChange t).obj A ⟶ (baseChange t).obj B, k • divisor = (baseChange t).map g := by
  let f := groupHom (multiplication A (k : ℤ))
  let K := (GroupScheme.kernel f).X
  have hf : GroupScheme.IsIsogeny f := multiplication_isogeny_nat A hk
  have hpb := GroupScheme.kernel_isPullback_scheme f
  have : IsFinite K.hom := MorphismProperty.of_isPullback hpb hf.1
  have : Flat K.hom := MorphismProperty.of_isPullback hpb hf.2.1
  obtain ⟨Z, j, hj, hZ⟩ := Langlands.AlgebraicGeometry.exists_finiteFlat_agreement_locus
    K B.X (GroupScheme.kernelι f ≫ groupHom g).hom.hom 1
  refine ⟨Z, j, hj, fun T t ↦ (hZ t).trans ?_⟩
  exact (baseChange_kernel_eq_one_iff t g k).trans (kernel_eq_one_iff ((baseChange t).map g) hk)

end Langlands.AbelianScheme.PolarizedFiniteLevel
