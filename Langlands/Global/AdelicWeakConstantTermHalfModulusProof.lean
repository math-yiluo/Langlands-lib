import Langlands.Global.AdelicWeakConstantTermTransitivity
import Langlands.GroupScheme.Lie.Functoriality
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Equality of the half moduli on the outer positive split component -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

private theorem det_eq_of_intertwiner_sub_one_range
    {R V W i k : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [Fintype i] [Fintype k] [DecidableEq i] [DecidableEq k]
    (B : Module.Basis i R V) (C : Module.Basis k R W)
    (f : Module.End R V) (g : Module.End R W) (j : V →ₗ[R] W) (hj : Function.Injective j)
    (hcomm : j ∘ₗ f = g ∘ₗ j) (hrange : ∀ y, (g - 1) y ∈ j.range) :
    f.det = g.det := by
  let e := LinearEquiv.ofInjective j hj
  let q : W →ₗ[R] V := e.symm.toLinearMap.comp ((g - 1).codRestrict j.range hrange)
  have hq (y : W) : j (q y) = (g - 1) y := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨(g - 1) y, hrange y⟩)
  have hqj : q ∘ₗ j = f - 1 := by
    ext x
    refine hj ?_
    rw [LinearMap.comp_apply, hq, LinearMap.sub_apply, LinearMap.sub_apply,
      Module.End.one_apply, Module.End.one_apply, map_sub]
    exact congrArg (fun k : V →ₗ[R] W => k x - j x) hcomm.symm
  have hjq : j ∘ₗ q = g - 1 := LinearMap.ext hq
  rw [← LinearMap.det_toMatrix B f, ← LinearMap.det_toMatrix C g,
    show f = 1 + q ∘ₗ j by rw [hqj]; abel,
    show g = 1 + j ∘ₗ q by rw [hjq]; abel]
  simp only [map_add, LinearMap.toMatrix_one]
  rw [LinearMap.toMatrix_comp B C B, LinearMap.toMatrix_comp C B C]
  exact Matrix.det_one_add_mul_comm (LinearMap.toMatrix C B q) (LinearMap.toMatrix B C j)

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

variable {Q P : StandardIndex F G fam.i fam.ν}

local notation "Adele" => Adeles F
local notation "AdeleAlg" => CommAlgCat.of F (Adeles F)

private theorem norm_adjointDeterminant_eq_of_nested_positive (hQP : Q ≤ P)
    (a : fam.positiveSplitComponent P) (b : fam.positiveSplitComponent Q)
    (hab : map F (fam.P Q) G (fam.p Q) b = map F (fam.P P) G (fam.p P) a) :
    characterNorm F (fam.P Q) (Lie.adjointDeterminantCharacter (fam.P Q)).toMul b =
      characterNorm F (fam.P P) (Lie.adjointDeterminantCharacter (fam.P P)).toMul a := by
  let inclusion := fam.nestedParabolicHom hQP
  have hinc := fam.nestedParabolicHom_comp hQP
  let : IsAffineHom (fam.P P).X.hom := (fam.isCompatible P).parabolic.isClosedSubgroup.isAffineHom
  let : IsAffineHom (fam.P Q).X.hom := (fam.isCompatible Q).parabolic.isClosedSubgroup.isAffineHom
  let : IsClosedImmersion (fam.p P).hom.hom.left := (fam.isCompatible P).parabolic.isClosedSubgroup
  let : IsClosedImmersion (fam.p Q).hom.hom.left := (fam.isCompatible Q).parabolic.isClosedSubgroup
  let : Mono (fam.p P).hom.hom := Over.mono_of_mono_left _
  let : Mono (fam.p Q).hom.hom := Over.mono_of_mono_left _
  have hinchom : inclusion.hom.hom ≫ (fam.p P).hom.hom = (fam.p Q).hom.hom :=
    congrArg (fun f : fam.P Q ⟶ G => f.hom.hom) hinc
  let : Mono inclusion.hom.hom := by
    constructor
    intro X f g h
    apply (cancel_mono (fam.p Q).hom.hom).mp
    simpa only [Category.assoc, hinchom] using
      congrArg (fun s : X ⟶ (fam.P P).X => s ≫ (fam.p P).hom.hom) h
  have hb : b.val ≫ inclusion.hom.hom = a.val := by
    apply (cancel_mono (fam.p P).hom.hom).mp
    rw [Category.assoc, hinchom]
    exact hab
  let j := Lie.targetMapLinear inclusion Adele
  let f := adjoint (fam.P Q) Adele b.val
  let g := adjoint (fam.P P) Adele a.val
  have hcomm : j ∘ₗ f = g ∘ₗ j := by
    apply LinearMap.ext
    intro z
    change Lie.targetMapLinear inclusion Adele (adjoint (fam.P Q) Adele b.val z) =
      adjoint (fam.P P) Adele a.val (Lie.targetMapLinear inclusion Adele z)
    rw [lieKernelHomLinear_adjoint, hb]
  have hRange (z : Additive (lieKernel (fam.P P) Adele)) : (g - 1) z ∈ j.range := by
    let w := (g - 1) z
    let X := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (DualNumber Adele)))
    let x : X ⟶ G.X := z.toMul.val ≫ (fam.p P).hom.hom
    let y : X ⟶ G.X := Lie.constant (fam.P P) a.val ≫ (fam.p P).hom.hom
    have hx : x ∈ (SubgroupFunctor.range (fam.p P)).carrier X := ⟨z.toMul.val, rfl⟩
    obtain ⟨t, _, ht⟩ := a.property
    have ht' : t ≫ (fam.a P ≫ fam.l P).hom.hom = a.val := ht
    have hy : Lie.constant (fam.A P).toGrp t ≫ (fam.a P ≫ fam.l P ≫ fam.p P).hom.hom = y := by
      dsimp only [y, Lie.constant, Lie.affineMap_apply]
      rw [← ht']
      simp only [Grp.comp_hom_hom, Category.assoc]
    have hR := fam.commutator_mem_radical_of_splitComponent P X (Lie.constant (fam.A P).toGrp t) hx
    dsimp only at hR
    rw [hy] at hR
    have hvalue : w.toMul.val ≫ (fam.p P).hom.hom = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
      dsimp only [w, g, LinearMap.sub_apply, Module.End.one_apply]
      change ((adjoint (fam.P P) Adele a.val z).toMul.val * z.toMul.val⁻¹) ≫ (fam.p P).hom.hom = _
      simp only [adjoint_val, MonObj.mul_comp, GrpObj.inv_comp, x, y]
      group
    have hw : w.toMul.val ≫ (fam.p P).hom.hom ∈ (SubgroupFunctor.range (fam.p Q)).carrier X := by
      rw [hvalue]
      exact ((fam.radical_le_of_le hQP).trans (SubgroupFunctor.range_comp_le _ _)) X (inv_mem hR)
    obtain ⟨u, hu⟩ := SubgroupFunctor.mem_range.mp hw
    have hu' : u ≫ inclusion.hom.hom = w.toMul.val := by
      apply (cancel_mono (fam.p P).hom.hom).mp
      simpa only [Category.assoc, hinchom] using hu
    have hk : u ∈ (Lie.reduction (fam.P Q) (A := Adele)).ker :=
      mem_lieKernel_of_comp inclusion u (by rw [hu']; exact w.toMul.property)
    refine ⟨Additive.ofMul ⟨u, hk⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hu'
  let B := (Pi.basisFun Adele _).map ((Lie.finiteCoordinates (fam.P Q)).equiv AdeleAlg).symm
  let C := (Pi.basisFun Adele _).map ((Lie.finiteCoordinates (fam.P P)).equiv AdeleAlg).symm
  have he := det_eq_of_intertwiner_sub_one_range B C f g j
    (Lie.targetMapLinear_injective inclusion Adele) hcomm hRange
  apply congrArg (IdeleAbsoluteValue.full F)
  apply Units.ext
  change (GroupScheme.Gm.affinePointsEquiv ((algSpec (CommRingCat.of F)).obj (op AdeleAlg)).hom
      (b.val ≫ (Lie.adjointDeterminantCharacter (fam.P Q)).toMul.hom.hom)).val =
    (GroupScheme.Gm.affinePointsEquiv ((algSpec (CommRingCat.of F)).obj (op AdeleAlg)).hom
      (a.val ≫ (Lie.adjointDeterminantCharacter (fam.P P)).toMul.hom.hom)).val
  rw [Lie.adjointDeterminantCharacter_val, Lie.adjointDeterminantCharacter_val]
  exact he

end StandardParabolicFamily

/-- The half moduli of nested parabolics agree on the positive split component of the outer
parabolic. The adjoint actions have equal determinants since their difference from the identity
factors through the Lie algebra of the inner parabolic. -/
theorem standardNestedHalfModulusCompatibility : StandardNestedHalfModulusCompatibilityStatement := by
  intro F _ _ G _ _ _ fam Q P hQP a b hab
  rw [fam.halfModulus_eq_sqrt Q, fam.halfModulus_eq_sqrt P,
    fam.norm_adjointDeterminant_eq_of_nested_positive hQP a b hab]

end Langlands.Global
