/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.LocalProperties
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRootBasis
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalRankOneIso
import all WeilConjectures.AlgebraicGeometry.Sp.SpIntegralRationalRootBasis
import WeilConjectures.AlgebraicGeometry.Sp.SpSliceScalarExtensionBasis
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # Invertibility of the finite quotient root projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem additive_id_nsmul
    {C : Type c} {D : Type v} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (M : C) (N : ℕ) (h : N • 𝟙 M = 0) : N • 𝟙 (F.obj M) = 0 := by
  calc
    N • 𝟙 (F.obj M) = N • F.map (𝟙 M) :=
      congrArg (fun f ↦ N • f) (F.map_id M).symm
    _ = F.map (N • 𝟙 M) := F.map_nsmul.symm
    _ = F.map 0 := congrArg (fun f : M ⟶ M ↦ F.map f) h
    _ = 0 := F.map_zero M M

private theorem quotientCoefficient_nsmul
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (U : X.ProEtᵒᵖ)
    (b : (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X).obj.obj U) :
    (l ^ (n + 1)) • b = 0 := by
  let B := completedResidue l E π n
  have hB : ((l ^ (n + 1) : ℕ) : B) = 0 := by
    let d : ULift.{u + 1} B →+* B := ULift.ringEquiv.toRingHom
    exact (map_natCast d _).symm.trans ((congrArg d hA).trans (map_zero d))
  have h : (l ^ (n + 1)) • 𝟙 (Profinite.continuousMapRingObj.{u} B) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (l ^ (n + 1)) • (f.down x) = (0 : B)
    rw [nsmul_eq_mul, hB, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hX := additive_id_nsmul (upperStarFromPoint X)
    (Profinite.continuousMapRingObj.{u} B) (l ^ (n + 1)) h
  exact congrArg (fun t ↦ t.hom.app U b) hX

attribute [local irreducible] quotientLine quotientLineMap spIntegralTwist spIntegralTwistSystem
  spSignedTwist

private theorem freeProjection_epi
    {C : Type c} [Category.{v} C] [MonoidalCategory C] (B : C) [MonObj B]
    {L G : C} (p : L ⟶ G) [Epi p] {M : Mod C B} (m : L ⟶ M.X)
    (q : M ⟶ (Mod.free B).obj G)
    (hq : m ≫ q.hom = p ≫ (Mod.freeForgetAdjunction B).unit.app G) : Epi q := by
  let adj := Mod.freeForgetAdjunction B
  have : Epi ((Mod.free B).map p) := ⟨by
    intro Z g h heq
    apply (adj.homEquiv _ Z).injective
    apply (cancel_epi p).mp
    have h := congrArg (adj.homEquiv _ Z) heq
    rw [adj.homEquiv_naturality_left p g, adj.homEquiv_naturality_left p _] at h
    exact h⟩
  let g := (adj.homEquiv L M).symm m
  have hg : g ≫ q = (Mod.free B).map p := by
    apply (adj.homEquiv L _).injective
    rw [adj.homEquiv_naturality_right g q]
    change adj.homEquiv L M ((adj.homEquiv L M).symm m) ≫ q.hom = _
    rw [Equiv.apply_symm_apply, hq, Adjunction.homEquiv_unit]
    exact adj.unit.naturality p
  exact epi_of_epi_fac hg

private theorem quotientRootProjection_epi
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤)))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (roots : IntegralRoots l E X)
    (q : quotientLine l E π n X ⟶
      (Mod.free (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).obj
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))))
    (hq : roots.hom ≫ quotientLineMap l E π n X ≫ q.hom =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        (Mod.freeForgetAdjunction (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).unit.app
            (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) : Epi q := by
  let B := condensedRingObj
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X
  let p : Scheme.purTwistZlOne X l ⟶
      Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)) :=
    Scheme.rootTowerProjection X l n
  have hT (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x trivial).hom
  have : Sheaf.IsLocallySurjective p := (Scheme.rootTower_finite_tensor X l hT n).1
  have : Epi p := (Sheaf.isLocallySurjective_iff_epi' _ p).mp inferInstance
  exact freeProjection_epi B p (roots.hom ≫ quotientLineMap l E π n X) q
    (by simpa only [p, B, Category.assoc] using hq)

/-- A root-normalized projection from the scalar quotient of the completed positive
Tate line to the free module on the finite root sheaf is invertible.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), expected reductions;
sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md, positive inverse-limit
construction; sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, compatible root bases.
(blueprint: lem-diagonal-quotient-root-projection-iso).

Proof in words. The root-tower projection is locally surjective. Applying the free
module functor preserves its epimorphism. By the displayed normalization it factors
through q, so q is epic. Choose the common compatible-root cover. The integral line
is free of rank one there, and extending this basis to the quotient retains rank
one without flatness. The finite root basis gives a basis for its free B-module:
tensor the cyclic root basis with B, and use that N annihilates B to identify
B tensor_Z Z/N with B. The presheaf tensor comparison is locally bijective and
restriction preserves this property, so the basis survives sheafification.
Thus q is locally an epic endomorphism of the regular module over a commutative
ring sheaf. Such an endomorphism is multiplication by its value on 1. Local
surjectivity lifts 1 locally, making that value a unit; separatedness then proves
injectivity. It is therefore an isomorphism on the cover and hence globally.
The same reasoning includes the zero ring, empty scheme and n=0. It uses only
the annihilation equation, not a flatness or ramification divisibility hypothesis. -/
theorem diagonalQuotientRootProjection_isIso
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤)))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (roots : IntegralRoots l E X)
    (q : quotientLine l E π n X ⟶
      (Mod.free (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).obj
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))))
    (hq : roots.hom ≫ quotientLineMap l E π n X ≫ q.hom =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        (Mod.freeForgetAdjunction (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X)).unit.app
            (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) : IsIso q := by
  let B := condensedRingObj
    (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) X
  let J := Scheme.ProEt.topology X
  let O := sectionRingSheaf.{u + 1, u + 1, u} J B
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let S := sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let f := S.functor.map q
  have : Epi q := quotientRootProjection_epi l X hX E π n roots q hq
  have : Epi f := inferInstance
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      simpa only [map_natCast] using
        (hX.map (X.presheaf.germ ⊤ x trivial).hom).map (X.residue x).hom).invertible
  obtain ⟨I, U, v, ζ, e, hc, hζ, he, _⟩ := Scheme.tateTwist_finite_locallyFree X l
  have hU : J.CoversTop U := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U v]
    exact Precoverage.generate_mem_toGrothendieck hc
  have hlocal (i : I) : IsIso (f.over (U i)) := by
    have hI := (spIntegralRationalRootBasis X l (U i) (fun r ↦ ζ r i)
      (fun r ↦ e r i) (fun r ↦ hζ r i) (fun r V a ↦ he r i V a) E).1
    obtain ⟨bI⟩ := hI
    simp only [spSignedTwist, WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower_one,
      SheafOfModules.scalarTensorPower_zero] at bI
    have hQ : Nonempty ((S.functor.obj (quotientLine l E π n X)).over (U i) ≅
        (SheafOfModules.unit R).over (U i)) := by
      unfold quotientLine
      exact spSliceScalarExtensionBasis X
        (coefficientMap (quotientMap l E π n) X) (spIntegralTwist X l E) (U i) bI
    obtain ⟨bQ⟩ := hQ
    have hb : ∀ (V : X.ProEtᵒᵖ) (b : B.obj.obj V), (l ^ (n + 1)) • b = 0 :=
      quotientCoefficient_nsmul l X E π n hA
    have hbF := diagonalFiniteRootBasis X l (U i) n (ζ n i) (e n i) (he n i) B hb
    obtain ⟨bF⟩ := hbF
    let bR := (SheafOfModules.overFunctor R (U i)).mapIso
      (AlgebraicGeometry.ProEtale.sectionUnitIso X B)
    let bT := bF.symm ≪≫ bR
    exact diagonalLocalRankOne_isIso X O (U i) f bQ bT
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := hlocal i
    change IsIso ((SheafOfModules.toSheaf (R.over (U i))).map (f.over (U i)))
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact isIso_of_reflects_iso q S.functor

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
