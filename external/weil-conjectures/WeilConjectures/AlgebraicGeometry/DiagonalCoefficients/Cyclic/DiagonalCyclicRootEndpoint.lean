/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientRootEndpoint
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientRootProjectionIso
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteIntegralEndpoint
import all WeilConjectures.AlgebraicGeometry.Sp.SpIntegralRationalRootBasis
import WeilConjectures.AlgebraicGeometry.Sp.SpSliceScalarExtensionBasis
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRootBasis
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalRankOneIso
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # The cyclic quotient of the integral Tate line

Source: diagonal tower coefficient changes (1), and the root-line reduction in
the diagonal tower limit proof.
(blueprint: lem-diagonal-cyclic-root-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

attribute [local irreducible] cyclicLine cyclicLineMap

private theorem cyclicFactor (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ r : spEllPointRingObj.{u} l (bottomField l) n ⟶
        Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))),
      IsMonHom r ∧
      integralMap l (bottomField l) ≫ spEllPointReduction l (bottomField l) n ≫ r =
        cyclicMap l n := by
  obtain ⟨_, eInt, _, heInt, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} l
  let I := spTateEllIdeal l (bottomField l) n
  let q₀ := (PadicInt.toZModPow (p := l) (n + 1)).comp eInt.symm.toRingHom
  have hI : I ≤ RingHom.ker q₀ := by
    apply Ideal.span_le.mpr
    rintro _ rfl
    change q₀ ((l : PadicAlgCl.integers l (bottomField l)) ^ (n + 1)) = 0
    simp only [q₀, map_natCast, ← Nat.cast_pow]
    exact ZMod.natCast_self _
  let r₀ := Ideal.Quotient.lift I q₀ hI
  let : TopologicalSpace (spEllQuotient l (bottomField l) n) := ⊥
  let : DiscreteTopology (spEllQuotient l (bottomField l) n) := ⟨rfl⟩
  let : IsTopologicalRing (spEllQuotient l (bottomField l) n) :=
    DiscreteTopology.topologicalRing
  let r : spEllPointRingObj.{u} l (bottomField l) n ⟶
      Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))) :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap r₀ continuous_of_discreteTopology)
  have hr : IsMonHom r := by dsimp only [r]; infer_instance
  refine ⟨r, hr, ?_⟩
  ext U z
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change q₀ (padicIntToIntegers l (bottomField l) (z.down x)) =
    PadicInt.toZModPow (p := l) (n + 1) (z.down x)
  rw [← heInt]
  change PadicInt.toZModPow (p := l) (n + 1) (eInt.symm (eInt (z.down x))) = _
  rw [RingEquiv.symm_apply_apply]

private theorem cyclicRootProjection_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℕ)
    (roots : IntegralRoots l (bottomField l) X) :
    ∃ q : cyclicLine l n X ⟶
        (Mod.free (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X)).obj
            (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))),
      roots.hom ≫ cyclicLineMap l n X ≫ q.hom =
        limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
          (Mod.freeForgetAdjunction (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X)).unit.app
              (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))) := by
  obtain ⟨r, hr, heq⟩ := cyclicFactor.{u} l n
  let := hr
  let a₀ := coefficientMap (integralMap l (bottomField l)) X
  let p := a₀ ≫ spEllReduction X l (bottomField l) n
  let a := coefficientMap (cyclicMap l n) X
  let b := coefficientMap r X
  have hab : p ≫ b = a := by
    dsimp only [p, a₀, a, b, spEllReduction]
    rw [Category.assoc, ← coefficientMap_comp, ← coefficientMap_comp, heq]
  let G := Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))
  let B := condensedRingObj (spEllPointRingObj l (bottomField l) n) X
  let f : zlLine l X ⟶ (Mod.comap p).obj ((Mod.free B).obj G) :=
    (Mod.comap a₀).map
        (limit.π (spIntegralTwistSystem X l (bottomField l)) (op n)) ≫
      (Mod.comapComp a₀ (spEllReduction X l (bottomField l) n)).inv.app
        ((Mod.free B).obj G)
  unfold cyclicLine cyclicLineMap
  exact extendFreeProjection p a b hab (zlLine l X) G f roots.hom
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    (by
      change roots.hom ≫
        (limit.π (spIntegralTwistSystem X l (bottomField l)) (op n)).hom = _
      exact roots.projections n)

private theorem cyclicCoefficient_nsmul
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (n : ℕ)
    (U : X.ProEtᵒᵖ)
    (b : (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X).obj.obj U) :
    (l ^ (n + 1)) • b = 0 := by
  have h : (l ^ (n + 1)) •
      𝟙 (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change (l ^ (n + 1)) • (f.down x) = (0 : ZMod (l ^ (n + 1)))
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint X) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint X).Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact congrArg (fun t ↦ t.hom.app U b)
    (additive_id_nsmul (upperStarFromPoint X) _ (l ^ (n + 1)) h)

private theorem cyclicRootProjection_isIso
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤))) (n : ℕ)
    (roots : IntegralRoots l (bottomField l) X)
    (q : cyclicLine l n X ⟶
      (Mod.free (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X)).obj
          (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1))))
    (hq : roots.hom ≫ cyclicLineMap l n X ≫ q.hom =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        (Mod.freeForgetAdjunction (condensedRingObj
          (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X)).unit.app
            (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) : IsIso q := by
  let B := condensedRingObj
    (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) X
  let J := Scheme.ProEt.topology X
  let O := sectionRingSheaf.{u + 1, u + 1, u} J B
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
  let S := sectionModuleEquivalence.{u + 1, u + 1, u} J B
  let f := S.functor.map q
  have hT (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x trivial).hom
  let p : Scheme.purTwistZlOne X l ⟶
      Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)) :=
    Scheme.rootTowerProjection X l n
  have : Epi p := (Sheaf.isLocallySurjective_iff_epi' _ p).mp
    (Scheme.rootTower_finite_tensor X l hT n).1
  have : Epi q := freeProjection_epi B p
    (roots.hom ≫ cyclicLineMap l n X) q
    (by simpa only [p, B, Category.assoc] using hq)
  have : Epi f := inferInstance
  let : ∀ x : X, Invertible (l : X.residueField x) := residueInvertible l X hX
  obtain ⟨I, U, v, ζ, e, hc, hζ, he, _⟩ := Scheme.tateTwist_finite_locallyFree X l
  have hU : J.CoversTop U := by
    let hterminal : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
      MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hterminal]
    rw [← Sieve.ofArrows_eq_ofObjects hterminal U v]
    exact Precoverage.generate_mem_toGrothendieck hc
  have hlocal (i : I) : IsIso (f.over (U i)) := by
    obtain ⟨bI⟩ := (spIntegralRationalRootBasis X l (U i) (fun r ↦ ζ r i)
      (fun r ↦ e r i) (fun r ↦ hζ r i) (fun r V a ↦ he r i V a) (bottomField l)).1
    simp only [spSignedTwist, WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower_one,
      SheafOfModules.scalarTensorPower_zero] at bI
    let a₀ := coefficientMap (integralMap l (bottomField l)) X
    have : IsIso (integralMap.{u} l (bottomField l)) := bottomMap_isIso l
    have : IsIso a₀ := (upperStarFromPoint X).map_isIso _
    let a₁ := (asIso a₀).inv
    have : IsMonHom a₁ := by dsimp only [a₁]; infer_instance
    let k : (Mod.extendScalars a₁).obj (spIntegralTwist X l (bottomField l)) ≅
        zlLine l X :=
      (Mod.extendScalarsIsoComapInv a₁).app _ ≪≫
        (Mod.comapCongr (show (asIso a₁).inv = a₀ by simp [a₁])).app _
    obtain ⟨bZ₀⟩ := spSliceScalarExtensionBasis X a₁
      (spIntegralTwist X l (bottomField l)) (U i) bI
    let bZ := ((spRootBasisSliceSections X
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)
        (U i)).mapIso k).symm ≪≫ bZ₀
    obtain ⟨bQ⟩ := spSliceScalarExtensionBasis X
      (coefficientMap (cyclicMap l n) X) (zlLine l X) (U i) bZ
    obtain ⟨bF⟩ := diagonalFiniteRootBasis X l (U i) n (ζ n i) (e n i) (he n i)
      B (cyclicCoefficient_nsmul l X n)
    let bR := (SheafOfModules.overFunctor R (U i)).mapIso
      (AlgebraicGeometry.ProEtale.sectionUnitIso X B)
    have bQ' : (S.functor.obj (cyclicLine l n X)).over (U i) ≅
        (SheafOfModules.unit R).over (U i) := by
      unfold cyclicLine
      exact bQ
    exact diagonalLocalRankOne_isIso X O (U i) f bQ' (bF.symm ≪≫ bR)
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := hlocal i
    change IsIso ((SheafOfModules.toSheaf (R.over (U i))).map (f.over (U i)))
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact isIso_of_reflects_iso q S.functor

/-- The ordinary tensor quotient of the integral root line is the finite cyclic
Tate line, with its actual root projection.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), together with the paragraph
beginning "Here the Tate twist" in sk-prop-diagonal-tower.proof.md.
(blueprint: lem-diagonal-cyclic-root-endpoint).

Proof: identify the bottom integer ring with Z_l and factor the actual continuous
PadicInt.toZModPow through its ell-power quotient. Restrict the n-th integral
root projection to Z_l and extend it along this factorization. The scalar-unit
formula gives a map q from cyclicLine to the free cyclic module on finite roots,
normalized by the actual root projection. That projection is locally surjective,
so q is epic. On the compatible-root cover, the bottom integral line is free of
rank one. Restricting along the bottom coefficient isomorphism and extending to
the cyclic ring retains this basis, without flatness. The finite root basis and
the annihilation of the cyclic coefficient ring give a rank-one target as well.
The existing local rank-one theorem makes q an isomorphism on this cover, hence
globally. The generic finite-root endpoint constructor compares the realized
free root module with the Cartier line, preserving its root unit. Composing with
q gives precisely the required LineEndpoint. The argument includes the zero ring,
the empty scheme and n=0. It uses no extension field or uniformizer. -/
theorem diagonalCyclicRootEndpoint
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsUnit (l : Γ(X, ⊤))) (n : ℕ)
    (e : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1))))
      (diagonalResidue.{u} l n) X)
    (integralRoots : IntegralRoots l (bottomField l) X)
    (finiteRoots : FiniteRoots X (l ^ (n + 1))) :
    Nonempty (e.LineEndpoint (cyclicLine l n X)
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) X)
      (integralRoots.hom ≫ cyclicLineMap l n X)
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) ≫
        finiteRoots.toLine (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1)))) := by
  obtain ⟨q, hq⟩ := cyclicRootProjection_exists l X n integralRoots
  have : IsIso q := cyclicRootProjection_isIso l X hX n integralRoots q hq
  exact endpointFromFree e (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) finiteRoots q
    (integralRoots.hom ≫ cyclicLineMap l n X)
    (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
    (by simpa only [Category.assoc] using hq)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
